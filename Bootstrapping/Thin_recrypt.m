load "Linear maps/GeneralCyclotomic/Linear_maps.m";
load "Linear maps/PowerOfTwo/Linear_maps.m";
load "Digit extraction/Digit_extraction.m";
load "Bootstrapping/Common.m";

if usePowerOfTwo then

// Generate the switch keys that are necessary during the linear transformations
function GenerateSwitchKeysThinRecrypt(sk)
    // Rotation switch keys
    rotationSwitchKeys := [];
    g_seq, h_seq := GetGeneralBabyGiantParams([GetDimensionSize(dim) : dim in [1..GetNbDimensions()]]);
    
    // Baby step
    for j := 2 to &*g_seq do
        rotationSwitchKeys[HypercubeToIndex(IndexToSequence(j, g_seq)) - 1] := GenSwitchKey(sk, IndexToSequence(j, g_seq));
    end for;

    // Giant step
    for k := 2 to &*h_seq do
        k_seq := IndexToSequence(k, h_seq);
        rot_size := [g_seq[ind] * k_seq[ind] : ind in [1..#g_seq]];
        rotationSwitchKeys[HypercubeToIndex(rot_size) - 1] := GenSwitchKey(sk, rot_size);
    end for;

    // Switch keys for coefficient selection
    coefficientSwitchKeys := [];
    for i := 0 to Valuation(d, 2) - 1 do
        Append(~coefficientSwitchKeys, GenSwitchKey(sk, (n div (2 ^ i)) + 1));
    end for;
    return rotationSwitchKeys, coefficientSwitchKeys;
end function;

// Generate the constants for the linear transformations
function GenerateThinConstants(henselExponentPlaintext, henselExponentCiphertext)
    // Compute constants for sparse linear transformation
    adapted_sparseConstants := MatMulAdaptedConstants(SparseConstants(henselExponentPlaintext), henselExponentPlaintext);
    adapted_sparseInvConstants := MatMulAdaptedConstants(SparseInvConstants(henselExponentCiphertext), henselExponentCiphertext);

    return adapted_sparseConstants, adapted_sparseInvConstants;
end function;

// Generate all variables necessary for the thin recryption procedure
function GenerateThinRecryptVariables(sk, pk, henselExponentPlaintext, henselExponentCiphertext)
    // Generate various keys and constants for the linear maps
    rk := GenRelinKey(sk);
    bootKey := GenBootKeyRecrypt(sk, pk, henselExponentCiphertext);
    adapted_sparseConstants, adapted_sparseInvConstants := GenerateThinConstants(henselExponentPlaintext,
                                                                                 henselExponentCiphertext);
    rotationSwitchKeys, coefficientSwitchKeys := GenerateSwitchKeysThinRecrypt(sk);
    additionConstant := EmbedInPowerfulBasis(Floor((p ^ henselExponentCiphertext) / 2 / (p ^ henselExponentPlaintext)), factors_m);
    liftingPolynomial := GetLiftingPolynomial(p, henselExponentCiphertext - 1);
    lowestDigitRetainPolynomials := [GetLowestDigitRetainPolynomial(p, iteration) : iteration in [1..henselExponentCiphertext]];

    return <rk, bootKey, adapted_sparseConstants, adapted_sparseInvConstants, rotationSwitchKeys, coefficientSwitchKeys,
            additionConstant, liftingPolynomial, lowestDigitRetainPolynomials>;
end function;

// Decode all variables necessary for the thin recryption procedure
function DecodeThinRecryptVariables(variables)
    return variables[1], variables[2], variables[3], variables[4], variables[5], variables[6], variables[7],
           variables[8], variables[9];
end function;

// Given a thin ciphertext c, return a recryption of all of its slots
function ThinRecrypt(c, recrypt_variables)
    // Decode recryption variables
    rk, bootKey, adapted_sparseConstants, adapted_sparseInvConstants, rotationSwitchKeys, coefficientSwitchKeys,
    additionConstant, liftingPolynomial, lowestDigitRetainPolynomials := DecodeThinRecryptVariables(recrypt_variables);

    // Apply linear map
    c := MatMulBabyGiant(c, adapted_sparseConstants, rotationSwitchKeys);

    // Homomorphic inner product
    u := HomomorphicInnerProduct(c, bootKey, additionConstant);

    // Perform coefficient selection and inverse linear map
    u := CoefficientSelection(u, coefficientSwitchKeys);
    u := MatMulBabyGiant(u, adapted_sparseInvConstants, rotationSwitchKeys);

    // Digit extraction
    henselExponentCiphertext := GetHenselExponent(bootKey);
    return OurDigitExtraction(u, p, henselExponentCiphertext,
                                    henselExponentCiphertext - GetHenselExponent(c),
                              addFunc, subFunc, func<x, y | mulFunc(x, y, rk)>,
                              div_pFunc, lowestDigitRetainPolynomials);
end function;

else

// Generate the switch keys that are necessary during the linear transformations
function GenerateSwitchKeysThinRecrypt(sk)
    // Rotation switch keys
    rotationSwitchKeysAhead := [[] : i in [1..GetNbDimensions()]];
    for dim := 1 to GetNbDimensions() do
        g, h := GetBabyGiantParams(GetDimensionSize(dim));
        
        // Not all switch keys are necessary, because of baby-step/giant-step implementation
        for pos in [1..g - 1] cat [g * k : k in [1..h - 1]] do
            rotationSwitchKeysAhead[dim][pos] := GenSwitchKey(sk, Get1DHyperIndex(dim, pos));
        end for;
    end for;

    // Additional switch key in the first dimension
    // --> Only necessary if first dimension is bad
    if IsGoodDimension(1) then
        switchKeyMinusD := [];
    else
        switchKeyMinusD := GenSwitchKey(sk, Get1DHyperIndex(1, -GetDimensionSize(1)));
    end if;

    // Frobenius switch keys
    frobeniusSwitchKeys := [];
    exponent := 1;
    for bit in Remove(Reverse(IntegerToSequence(d, 2)), 1) do
        frobeniusSwitchKeys[exponent] := GenSwitchKey(sk, Modexp(p, exponent, m));
        exponent := 2 * exponent + bit;
    end for;
    return rotationSwitchKeysAhead, switchKeyMinusD, frobeniusSwitchKeys;
end function;

// Generate the constants for the linear transformations
function GenerateThinConstants(henselExponentPlaintext, henselExponentCiphertext)
    // Compute constants for Eval linear transformation in dimension 1
    evalStage_1Constants := EvalStage_dimConstants(1, henselExponentPlaintext);
    if IsGoodDimension(1) then
        // Eval
        adapted_evalConstantsAhead := [MatMul1DGoodDimensionAdaptedConstants(evalStage_1Constants, 1,
                                                                             henselExponentPlaintext)];
        adapted_evalConstantsBack := [];
    else
        // Eval
        adapted_constantsAhead, adapted_constantsBack := MatMul1DBadDimensionAdaptedConstants(evalStage_1Constants, 1,
                                                                                              henselExponentPlaintext);
        adapted_evalConstantsAhead := [adapted_constantsAhead];
        adapted_evalConstantsBack := [adapted_constantsBack];
    end if;

    // Compute constants for EvalInv linear transformation in dimension 1
    evalInvStage_1Constants := EvalInvStage_1Constants(1, henselExponentCiphertext);
    unpack_constants := UnpackConstants(henselExponentCiphertext);
    chainedConstants := ChainTransformations(evalInvStage_1Constants, unpack_constants[1], 1, henselExponentCiphertext);
    if IsGoodDimension(1) then
        // EvalInv
        adapted_evalInvConstantsAhead := [MatMul1DGoodDimensionAdaptedConstants(chainedConstants, 1,
                                                                                henselExponentCiphertext)];
        adapted_evalInvConstantsBack := [];
    else
        // EvalInv
        adapted_constantsAhead, adapted_constantsBack := MatMul1DBadDimensionAdaptedConstants(chainedConstants, 1,
                                                                                              henselExponentCiphertext);
        adapted_evalInvConstantsAhead := [adapted_constantsAhead];
        adapted_evalInvConstantsBack := [adapted_constantsBack];
    end if;

    // Compute constants for linear transformations during stages 2, ..., GetNbDimensions()
    // --> These dimensions are always good
    for dim := 2 to GetNbDimensions() do
        evalStage_dimConstants := EvalStage_dimConstants(dim, henselExponentPlaintext);
        evalInvStage_dimConstants := EvalInvStage_dimConstants(dim, henselExponentCiphertext);

        // Eval
        Append(~adapted_evalConstantsAhead, MatMul1DGoodDimensionAdaptedConstants(evalStage_dimConstants, dim,
                                                                                  henselExponentPlaintext));
        
        // EvalInv
        Append(~adapted_evalInvConstantsAhead, MatMul1DGoodDimensionAdaptedConstants(evalInvStage_dimConstants, dim,
                                                                                     henselExponentCiphertext));
    end for;

    return adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead, adapted_evalInvConstantsBack;
end function;

// Generate all variables necessary for the thin recryption procedure
function GenerateThinRecryptVariables(sk, pk, henselExponentPlaintext, henselExponentCiphertext)
    // Generate various keys and constants for the linear maps
    rk := GenRelinKey(sk);
    bootKey := GenBootKeyRecrypt(sk, pk, henselExponentCiphertext);
    adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead,
    adapted_evalInvConstantsBack := GenerateThinConstants(henselExponentPlaintext, henselExponentCiphertext);
    rotationSwitchKeysAhead, switchKeyMinusD, frobeniusSwitchKeys := GenerateSwitchKeysThinRecrypt(sk);
    additionConstant := EmbedInPowerfulBasis(Floor((p ^ henselExponentCiphertext) / 2 / (p ^ henselExponentPlaintext)), factors_m);
    liftingPolynomial := GetLiftingPolynomial(p, henselExponentCiphertext - 1);
    lowestDigitRetainPolynomials := [GetLowestDigitRetainPolynomial(p, iteration) : iteration in [1..henselExponentCiphertext]];

    return <rk, bootKey, adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead,
            adapted_evalInvConstantsBack, rotationSwitchKeysAhead, switchKeyMinusD, frobeniusSwitchKeys, additionConstant,
            liftingPolynomial, lowestDigitRetainPolynomials>;
end function;

// Decode all variables necessary for the thin recryption procedure
function DecodeThinRecryptVariables(variables)
    return variables[1], variables[2], variables[3], variables[4], variables[5], variables[6], variables[7],
           variables[8], variables[9], variables[10], variables[11], variables[12];
end function;

// Given a thin ciphertext c, return a recryption of all of its slots
function ThinRecrypt(c, recrypt_variables)
    // Decode recryption variables
    rk, bootKey, adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead,
    adapted_evalInvConstantsBack, rotationSwitchKeysAhead, switchKeyMinusD, frobeniusSwitchKeys, additionConstant,
    liftingPolynomial, lowestDigitRetainPolynomials := DecodeThinRecryptVariables(recrypt_variables);

    // Apply series of linear maps
    // --> Only the first dimension can be a bad one
    if IsGoodDimension(1) then
        c := MatMul1DGoodDimensionBabyGiant(c, adapted_evalConstantsAhead[1], 1, rotationSwitchKeysAhead[1]);
    else
        c := MatMul1DBadDimensionBabyGiant(c, adapted_evalConstantsAhead[1], adapted_evalConstantsBack[1], 1,
                                           rotationSwitchKeysAhead[1], switchKeyMinusD);
    end if;
    for dim := 2 to GetNbDimensions() do
        c := MatMul1DGoodDimensionBabyGiant(c, adapted_evalConstantsAhead[dim], dim, rotationSwitchKeysAhead[dim]);
    end for;

    // Homomorphic inner product
    u := HomomorphicInnerProduct(c, bootKey, additionConstant);

    // Apply series of linear maps
    // --> Only the first dimension can be a bad one
    dim := GetNbDimensions();
    while dim ge 2 do
        u := MatMul1DGoodDimensionBabyGiant(u, adapted_evalInvConstantsAhead[dim], dim, rotationSwitchKeysAhead[dim]);
        dim -:= 1;
    end while;
    if IsGoodDimension(1) then
        u := MatMul1DGoodDimensionBabyGiant(u, adapted_evalInvConstantsAhead[1], 1, rotationSwitchKeysAhead[1]);
    else
        u := MatMul1DBadDimensionBabyGiant(u, adapted_evalInvConstantsAhead[1], adapted_evalInvConstantsBack[1], 1,
                                           rotationSwitchKeysAhead[1], switchKeyMinusD);
    end if;

    // Remove content of powers of x by applying slot-wise trace map
    u := SlotwiseTrace(u, frobeniusSwitchKeys);

    // Digit extraction
    henselExponentCiphertext := GetHenselExponent(bootKey);
    return OurDigitExtraction(u, p, henselExponentCiphertext,
                                    henselExponentCiphertext - GetHenselExponent(c),
                              addFunc, subFunc, func<x, y | mulFunc(x, y, rk)>,
                              div_pFunc, lowestDigitRetainPolynomials);
end function;

end if;