load "Crypto/BFV/BFV.m";
load "Linear maps/GeneralCyclotomic/Linear_maps.m";
load "Linear maps/PowerOfTwo/Linear_maps.m";
load "Digit extraction/Digit_extraction.m";
load "Bootstrapping/Common.m";

// Generate all variables necessary for the GBFV recryption procedure
function GenerateGBFVBetterRecryptVariables(sk, pk, B)
    assert B le (p div 2);

    // Generate keys
    rk := GenRelinKey(sk);
    bootKey := GenBootKeyRecrypt(sk, pk, 2);
    
    // Generate constants for the linear maps
    adapted_evalConstants := []; adapted_evalInvConstants := [];
    gen_eval := []; dim_size_eval := []; dim_good_eval := [];
    gen_evalInv := []; dim_size_evalInv := []; dim_good_evalInv := [];
    switchKeys_eval := []; switchKeys_evalInv := [];
    for stage := 1 to #gbfv_mat_dimensions do
        // Forward transformation
        constants, generators, dim_sizes, dim_good := GBFVSparseEvalConstants(stage, 1);
        Append(~gen_eval, generators); Append(~dim_size_eval, dim_sizes); Append(~dim_good_eval, dim_good);
        Append(~switchKeys_eval, MatMulGeneralGBFVBabyGiantSwitchKeys(sk, generators, dim_sizes, dim_good));

        // Adapt constants in two ways
        // - Multiply with correction constant that puts zero in garbage slots
        // - Convert back from BFV to GBFV (we implement LT in the BFV domain so that all automorphisms are well-defined)
        //   --> This does not harm the noise growth because reinterpretation to GBFV decreases the invariant noise
        if stage + #allModuli - 1 gt #gbfv_mat_dimensions then
            constant := EmbedInSlots([slot eq 0 select 1 else 0 :
                                      slot in GetPlaintextParts(allModuli[stage + #allModuli - #gbfv_mat_dimensions - 1]:
                                      henselExponent := 1)]: henselExponent := 1);
            loop_sizes := [dim_good[i] select dim_sizes[i] else 2 * dim_sizes[i] - 1 : i in [1..#generators]];
            minima := [dim_good[i] select 0 else -dim_sizes[i] + 1 : i in [1..#generators]];
            constants := [ScaleAndRound((ApplyAutomorphismPlaintext(constant,
                          RotToExp(generators, IndexToSequence(index, loop_sizes: minima := minima)) mod (2 * n_prime):
                          henselExponent := 1) * constants[index]) mod f, p, allModuli[stage + #allModuli - #gbfv_mat_dimensions])
                          mod p : index in [1..#constants]];
        end if;
        Append(~adapted_evalConstants, MatMulGeneralGBFVAdaptedConstants(constants, generators, dim_sizes, dim_good, 1));

        // Inverse transformation
        constants, generators, dim_sizes, dim_good := GBFVSparseEvalInvConstants(stage, 2);
        Append(~gen_evalInv, generators); Append(~dim_size_evalInv, dim_sizes); Append(~dim_good_evalInv, dim_good);
        Append(~switchKeys_evalInv, MatMulGeneralGBFVBabyGiantSwitchKeys(sk, generators, dim_sizes, dim_good));

        // Adapt constants (same cheating trick of working in the BFV domain is applied here)
        if stage + #allModuli - 1 gt #gbfv_mat_dimensions then
            constants := [ScaleAndRound(el, p ^ 2, allModuli[stage + #allModuli - #gbfv_mat_dimensions - 1] ^ 2) mod (p ^ 2) :
                          el in constants];
        end if;
        Append(~adapted_evalInvConstants, MatMulGeneralGBFVAdaptedConstants(constants, generators, dim_sizes, dim_good, 2));
    end for;

    // Fix for zero dimensions
    if #gbfv_mat_dimensions eq 0 then
        adapted_evalInvConstants := DivideOverField(p ^ 2, gbfvModulus ^ 2);
    end if;

    // Generate constants for the trace operation
    traceKeys := [GenSwitchKey(sk, GetHypercubeRepresentative((n div (2 ^ i)) + 1)) : i in [1..Valuation(n div n_double_prime, 2)]];

    // Multiply input of lowest digit removal polynomial by inverse of trace constant
    // Multiply output of lowest digit removal polynomial by inverse of beta
    beta := Zx!Eltseq(ToCyclotomicField(p) * InvertOverField(gbfvModulus));
    beta_slots := GetPlaintextParts(beta: henselExponent := 1);
    Zt_F1<y> := GetSlotAlgebra(1);      // Inverse computed over slot algebra for non-zero elements only
    beta_inverse_slots := [Zx | (el eq 0) select 0 else (Zt_F1!el) ^ (-1) : el in beta_slots];
    exponent := (#gbfv_mat_dimensions eq 0) select 2 else 1;    // Fix for zero dimensions
    beta_inverse := Flatten(EmbedInSlots(beta_inverse_slots: henselExponent := 1) ^ exponent, gbfvModulus);
    lowestDigitRemovalPolynomialOverRange := Evaluate(GetLowestDigitRemovalPolynomialOverRange(p, B),
                                                      Modinv(n div n_double_prime, p ^ 2) * PolynomialRing(Zx).1) * beta_inverse;

    return <rk, bootKey, adapted_evalConstants, adapted_evalInvConstants, gen_eval, dim_size_eval, dim_good_eval,
            gen_evalInv, dim_size_evalInv, dim_good_evalInv, switchKeys_eval, switchKeys_evalInv, traceKeys,
            lowestDigitRemovalPolynomialOverRange>;
end function;

// Decode all variables necessary for the GBFV recryption procedure
function DecodeGBFVBetterRecryptVariables(variables)
    return variables[1], variables[2], variables[3], variables[4], variables[5], variables[6], variables[7],
           variables[8], variables[9], variables[10], variables[11], variables[12], variables[13], variables[14];
end function;

// Recrypt GBFV ciphertext
function GBFVBetterRecrypt(c, recrypt_variables)
    assert GetPlaintextModulus(c) eq gbfvModulus;

    // Decode recryption variables
    rk, bootKey, adapted_evalConstants, adapted_evalInvConstants, gen_eval, dim_size_eval, dim_good_eval,
    gen_evalInv, dim_size_evalInv, dim_good_evalInv, switchKeys_eval, switchKeys_evalInv, traceKeys,
    lowestDigitRemovalPolynomialOverRange := DecodeGBFVBetterRecryptVariables(recrypt_variables);

    // Slots to coefficients
    newModuli := intModuli cat [p];
    for stage := 1 to #gbfv_mat_dimensions do
        // Increase plaintext modulus: cheat by going to BFV domain
        if stage + #newModuli gt #gbfv_mat_dimensions then
            c := ScaleAndRoundCiphertext(c, GetPlaintextModulus(c), p);
        end if;

        // Linear transformation
        c := MatMulGeneralGBFVBabyGiant(c, adapted_evalConstants[stage], gen_eval[stage], dim_size_eval[stage],
                                        dim_good_eval[stage], switchKeys_eval[stage]);
        
        // Decrease plaintext modulus: go back to GBFV domain which reduces the invariant noise
        if stage + #newModuli gt #gbfv_mat_dimensions then
            c := SetPlaintextModulus(c, newModuli[stage + #newModuli - #gbfv_mat_dimensions]);
        end if;
    end for;

    // Fix for zero dimensions
    if #gbfv_mat_dimensions eq 0 then
        c := SetPlaintextModulus(c, p);
    end if;

    // Trace
    c := EvaluateTraceGBFV(c, traceKeys: start_index := Valuation(n div n_prime, 2) + 1);

    // Homomorphic inner product
    u := HomomorphicInnerProduct(c, bootKey, 0);

    // Trace
    u := EvaluateTraceGBFV(u, traceKeys);

    // Coefficients to slots
    newModuli := [gbfvModulus] cat intModuli;
    for iteration := 1 to #gbfv_mat_dimensions do
        stage := #gbfv_mat_dimensions - iteration + 1;

        // Increase plaintext modulus: cheat by going to BFV domain
        if stage + #newModuli gt #gbfv_mat_dimensions then
            u := ScaleAndRoundCiphertext(u, GetPlaintextModulus(u), p ^ 2);
        end if;

        // Linear transformation
        u := MatMulGeneralGBFVBabyGiant(u, adapted_evalInvConstants[stage], gen_evalInv[stage], dim_size_evalInv[stage],
                                        dim_good_evalInv[stage], switchKeys_evalInv[stage]);

        // Decrease plaintext modulus: go back to GBFV domain which reduces the invariant noise
        if stage + #newModuli gt #gbfv_mat_dimensions then
            u := SetPlaintextModulus(u, newModuli[stage + #newModuli - #gbfv_mat_dimensions] ^ 2);
        end if;
    end for;

    // Fix for zero dimensions
    if #gbfv_mat_dimensions eq 0 then
        u := MulConstant(u, adapted_evalInvConstants);
        u := SetPlaintextModulus(u, gbfvModulus ^ 2);
    end if;

    // Digit extraction
    return BoundedRangeDigitExtraction(u, addFunc, func<x, y | mulFunc(x, y, rk)>, func<x | ExactDivisionBy(x, gbfvModulus)>,
                                       lowestDigitRemovalPolynomialOverRange);
end function;