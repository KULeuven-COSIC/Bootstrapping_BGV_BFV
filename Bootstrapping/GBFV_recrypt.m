load "Crypto/BFV/BFV.m";
load "Bootstrapping/Thin_recrypt.m";

// Recrypt GBFV ciphertext based on black-box approach
// The required recryption variables are the same ones as for thin bootstrapping
function GBFVRecryptBlackBox(c, recrypt_variables)
    mod_copy := GetPlaintextModulus(c);     // Copy original value of plaintext modulus
    c := ScaleAndRoundCiphertext(c, mod_copy, p);
    c := ThinRecrypt(c, recrypt_variables);
    return ScaleAndRoundCiphertext(c, p, mod_copy);
end function;

// Generate all variables necessary for the GBFV recryption procedure
function GenerateGBFVRecryptVariables(sk, pk, B)
    variables := GenerateThinRecryptVariables(sk, pk, 1, 2, B);

    // Multiply lowest digit removal polynomial by inverse of beta
    beta := Zx!Eltseq(ToCyclotomicField(p) * InvertOverField(gbfvModulus));
    beta_slots := GetPlaintextParts(beta: henselExponent := 1);
    Zt_F1<y> := GetSlotAlgebra(1);      // Inverse computed over slot algebra for non-zero elements only
    beta_inverse_slots := [Zx | (el eq 0) select 0 else (Zt_F1!el) ^ (-1) : el in beta_slots];
    beta_inverse := Flatten(EmbedInSlots(beta_inverse_slots: henselExponent := 1), gbfvModulus);
    lowestDigitRemovalPolynomialOverRange := Evaluate(variables[13], PolynomialRing(Zx).1) * beta_inverse;

    // Multiply LT constants by beta ^ 2
    dimensions := [GetNbDimensions(), 1];
    inverse_constants := [((poly * (beta ^ 2)) mod f) mod (p ^ 2) : poly in SparseEvalInvStage_1Constants(dimensions, 2)];
    adapted_constantsAhead, adapted_constantsBack := MatMul2DBadDimensionAdaptedConstants(inverse_constants, dimensions, 2);
    variables[5][1] := adapted_constantsAhead; variables[6][1] := adapted_constantsBack;

    return <variables[1], variables[2], variables[3], variables[4], variables[5], variables[6], variables[7],
            variables[8], variables[10], variables[11], variables[12], lowestDigitRemovalPolynomialOverRange>;
end function;

// Decode all variables necessary for the GBFV recryption procedure
function DecodeGBFVRecryptVariables(variables)
    return variables[1], variables[2], variables[3], variables[4], variables[5], variables[6], variables[7],
           variables[8], variables[9], variables[10], variables[11], variables[12];
end function;

// Recrypt GBFV ciphertext
function GBFVRecrypt(c, recrypt_variables)
    // Implementation is restricted to full splitting case
    assert (GetLTVersion() eq 3) and (p mod m eq 1);

    mod_copy := GetPlaintextModulus(c);     // Copy original value of plaintext modulus
    c := ScaleAndRoundCiphertext(c, mod_copy, p);

    /*** Evaluate slot-wise noisy expansion ***/

    // Decode recryption variables
    rk, bootKey, adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead,
    adapted_evalInvConstantsBack, rotationSwitchKeysAhead, switchKeysMinusD,
    additionConstant, liftingPolynomial, lowestDigitRetainPolynomials,
    lowestDigitRemovalPolynomialOverRange := DecodeGBFVRecryptVariables(recrypt_variables);

    // First stage
    dimensions := [GetNbDimensions(), 1];
    c := MatMul2DBadDimensionBabyGiant(c, adapted_evalConstantsAhead[1], adapted_evalConstantsBack[1], dimensions,
                                       rotationSwitchKeysAhead[1], switchKeysMinusD[1]);

    // Other stages
    for dim := 2 to GetNbDimensions() - 1 do
        if dim eq GetNbDimensions() - 1 then
            c := MatMul1DGoodDimensionBabyGiant(c, adapted_evalConstantsAhead[dim], dim, rotationSwitchKeysAhead[dim]);
        else
            c := MatMul1DBadDimensionBabyGiant(c, adapted_evalConstantsAhead[dim], adapted_evalConstantsBack[dim],
                                               dim, rotationSwitchKeysAhead[dim], switchKeysMinusD[dim]);
        end if;
    end for;

    PrintNoiseBudget(c: message := "after first LT");
    StopTiming(timer_first_lt: message := "first LT");
    timer_inner_product := StartTiming();

    // Homomorphic inner product
    u := HomomorphicInnerProduct(c, bootKey, additionConstant);

    PrintNoiseBudget(u: message := "after inner product");
    StopTiming(timer_inner_product: message := "inner product");
    timer_second_lt := StartTiming();

    // Other stages
    dim := GetNbDimensions() - 1;
    while dim ge 2 do
        if dim eq GetNbDimensions() - 1 then
            u := MatMul1DGoodDimensionBabyGiant(u, adapted_evalInvConstantsAhead[dim], dim, rotationSwitchKeysAhead[dim]);
        else
            u := MatMul1DBadDimensionBabyGiant(u, adapted_evalInvConstantsAhead[dim], adapted_evalInvConstantsBack[dim],
                                               dim, rotationSwitchKeysAhead[dim], switchKeysMinusD[dim]);
        end if;
        dim -:= 1;
    end while;

    // First stage
    u := MatMul2DBadDimensionBabyGiant(u, adapted_evalInvConstantsAhead[1], adapted_evalInvConstantsBack[1], dimensions,
                                       rotationSwitchKeysAhead[1], switchKeysMinusD[1]);

    PrintNoiseBudget(u: message := "after second LT");
    StopTiming(timer_second_lt: message := "second LT");
    timer_digit_extract := StartTiming();

    // Convert back to GBFV
    u := SetPlaintextModulus(u, mod_copy ^ 2);

    // Digit extraction
    res := BoundedRangeDigitExtraction(u, addFunc, func<x, y | mulFunc(x, y, rk)>, func<x | ExactDivisionBy(x, mod_copy)>,
                                       lowestDigitRemovalPolynomialOverRange);
    res := SetPlaintextModulus(res, p);     // Won't print noise budget otherwise
    PrintNoiseBudget(res: message := "after digit extract");
    StopTiming(timer_digit_extract: message := "digit extract");
    return res;
end function;

// Generate all variables necessary for the GBFV batch recryption procedure
function GenerateGBFVBatchRecryptVariables(sk, pk, B)
    variables := GenerateThinRecryptVariables(sk, pk, 1, 2, B);

    // Multiply lowest digit removal polynomial by square of inverse of beta
    beta := Zx!Eltseq(ToCyclotomicField(p) * InvertOverField(gbfvModulus));
    beta_slots := GetPlaintextParts(beta: henselExponent := 1);
    Zt_F1<y> := GetSlotAlgebra(1);      // Inverse computed over slot algebra for non-zero elements only
    beta_inverse_slots := [Zx | (el eq 0) select 0 else (Zt_F1!el) ^ (-1) : el in beta_slots];
    beta_inverse_square := Flatten(EmbedInSlots(beta_inverse_slots: henselExponent := 1) ^ 2, gbfvModulus);
    lowestDigitRemovalPolynomialOverRange := Evaluate(variables[13], PolynomialRing(Zx).1) * beta_inverse_square;

    // Construct packing and unpacking keys
    nb_packed := n div gbfvExponent;
    pack_keys := [GenSwitchKey(sk, ((-1) ^ (index mod 2) * 5 ^ (index div 2)) mod m) : index in [1..nb_packed - 1]];
    unpack_keys := [GenSwitchKey(sk, Modinv((-1) ^ (index mod 2) * 5 ^ (index div 2), m)) : index in [1..nb_packed - 1]];

    return <variables[1], variables[2], variables[3], variables[4], variables[5], variables[6], variables[7], variables[8],
            variables[10], variables[11], variables[12], lowestDigitRemovalPolynomialOverRange, pack_keys, unpack_keys>;
end function;

// Decode all variables necessary for the GBFV batch recryption procedure
function DecodeGBFVBatchRecryptVariables(variables)
    return variables[1], variables[2], variables[3], variables[4], variables[5], variables[6], variables[7], variables[8],
           variables[9], variables[10], variables[11], variables[12], variables[13], variables[14];
end function;

// Batch recrypt GBFV ciphertexts
function GBFVBatchRecrypt(c_list, recrypt_variables)
    // Implementation is restricted to full splitting case
    assert (GetLTVersion() eq 3) and (p mod m eq 1);

    // Decode recryption variables
    rk, bootKey, adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead,
    adapted_evalInvConstantsBack, rotationSwitchKeysAhead, switchKeysMinusD, additionConstant, liftingPolynomial,
    lowestDigitRetainPolynomials, lowestDigitRemovalPolynomialOverRange, pack_keys,
    unpack_keys := DecodeGBFVBatchRecryptVariables(recrypt_variables);

    PrintNoiseBudget(c_list[1]: message := "batch initial");
    timer_pack := StartTiming();

    // Convert to BFV
    mod_copy := GetPlaintextModulus(c_list[1]);     // Copy original value of plaintext modulus
    c_converted := [SetPlaintextModulus(c, p) : c in c_list];

    // Pack ciphertexts
    c := c_converted[1];
    for index := 1 to #c_list - 1 do
        c := Add(c, ApplyAutomorphismCiphertext(c_converted[index + 1], ((-1) ^ (index mod 2) * 5 ^ (index div 2)) mod m,
                                                pack_keys[index]));
    end for;

    PrintNoiseBudget(c: message := "after batch packing");
    StopTiming(timer_pack: message := "batch packing");
    timer_first_lt := StartTiming();

    /*** Evaluate slot-wise noisy expansion ***/

    // First stage
    dimensions := [GetNbDimensions(), 1];
    c := MatMul2DBadDimensionBabyGiant(c, adapted_evalConstantsAhead[1], adapted_evalConstantsBack[1], dimensions,
                                       rotationSwitchKeysAhead[1], switchKeysMinusD[1]);

    // Other stages
    for dim := 2 to GetNbDimensions() - 1 do
        if dim eq GetNbDimensions() - 1 then
            c := MatMul1DGoodDimensionBabyGiant(c, adapted_evalConstantsAhead[dim], dim, rotationSwitchKeysAhead[dim]);
        else
            c := MatMul1DBadDimensionBabyGiant(c, adapted_evalConstantsAhead[dim], adapted_evalConstantsBack[dim],
                                               dim, rotationSwitchKeysAhead[dim], switchKeysMinusD[dim]);
        end if;
    end for;

    PrintNoiseBudget(c: message := "after first LT");
    StopTiming(timer_first_lt: message := "first LT");
    timer_inner_product := StartTiming();

    // Homomorphic inner product
    u := HomomorphicInnerProduct(c, bootKey, additionConstant);

    PrintNoiseBudget(u: message := "after inner product");
    StopTiming(timer_inner_product: message := "inner product");
    timer_second_lt := StartTiming();

    // Other stages
    dim := GetNbDimensions() - 1;
    while dim ge 2 do
        if dim eq GetNbDimensions() - 1 then
            u := MatMul1DGoodDimensionBabyGiant(u, adapted_evalInvConstantsAhead[dim], dim, rotationSwitchKeysAhead[dim]);
        else
            u := MatMul1DBadDimensionBabyGiant(u, adapted_evalInvConstantsAhead[dim], adapted_evalInvConstantsBack[dim],
                                               dim, rotationSwitchKeysAhead[dim], switchKeysMinusD[dim]);
        end if;
        dim -:= 1;
    end while;

    // First stage
    u := MatMul2DBadDimensionBabyGiant(u, adapted_evalInvConstantsAhead[1], adapted_evalInvConstantsBack[1], dimensions,
                                       rotationSwitchKeysAhead[1], switchKeysMinusD[1]);

    PrintNoiseBudget(u: message := "after second LT");
    StopTiming(timer_second_lt: message := "second LT");
    timer_unpack := StartTiming();

    // Unpack ciphertexts
    mod_copy := x ^ gbfvExponent - gbfvCoefficient; beta := ScaleAndRound(1, p, mod_copy);
    u_list := [SetPlaintextModulus(MulConstant(u, beta ^ 2), mod_copy ^ 2)];
    for index := 1 to #c_list - 1 do
        Append(~u_list, SetPlaintextModulus(MulConstant(ApplyAutomorphismCiphertext(u,
                                                        Modinv((-1) ^ (index mod 2) * 5 ^ (index div 2), m),
                                                        unpack_keys[index]), beta ^ 2), mod_copy ^ 2));
    end for;

    // Won't print noise budget otherwise
    PrintNoiseBudget(SetPlaintextModulus(u_list[1], p ^ 2): message := "after batch unpacking");
    StopTiming(timer_unpack: message := "batch unpacking");
    timer_digit_extract := StartTiming();

    // Digit extraction
    // Won't print noise budget otherwise
    res := [SetPlaintextModulus(BoundedRangeDigitExtraction(u, addFunc, func<x, y | mulFunc(x, y, rk)>,
                                                            func<x | ExactDivisionBy(x, mod_copy)>,
                                                            lowestDigitRemovalPolynomialOverRange), p) : u in u_list];
    PrintNoiseBudget(res[1]: message := "after digit extract");
    StopTiming(timer_digit_extract: message := "digit extract");
    return res;
end function;