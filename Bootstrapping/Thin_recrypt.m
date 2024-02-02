load "Linear maps/GeneralCyclotomic/Linear_maps.m";
load "Linear maps/PowerOfTwo/Linear_maps.m";
load "Digit extraction/Digit_extraction.m";
load "Bootstrapping/Common.m";

// HElib version of thin bootstrapping
if GetLTVersion() eq 1 then

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
    assert henselExponentPlaintext lt henselExponentCiphertext;

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

// SEAL version of thin bootstrapping
elif GetLTVersion() eq 2 then

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
    assert henselExponentPlaintext lt henselExponentCiphertext;

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

// Our version of thin bootstrapping
elif GetLTVersion() eq 3 then

// Generate all variables necessary for the thin recryption procedure
forward GenerateSwitchKeysThinRecrypt; forward GenerateThinConstants;
function GenerateThinRecryptVariables(sk, pk, henselExponentPlaintext, henselExponentCiphertext)
    assert henselExponentPlaintext lt henselExponentCiphertext;

    // Generate various keys and constants for the linear maps
    rk := GenRelinKey(sk);
    bootKey := GenBootKeyRecrypt(sk, pk, henselExponentCiphertext);
    adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead,
    adapted_evalInvConstantsBack := GenerateThinConstants(henselExponentPlaintext, henselExponentCiphertext);
    rotationSwitchKeysAhead, switchKeysMinusD, traceKeys := GenerateSwitchKeysThinRecrypt(sk);
    additionConstant := EmbedInPowerfulBasis(Floor((p ^ henselExponentCiphertext) / 2 / (p ^ henselExponentPlaintext)), factors_m);
    liftingPolynomial := GetLiftingPolynomial(p, henselExponentCiphertext - 1);
    lowestDigitRetainPolynomials := [GetLowestDigitRetainPolynomial(p, iteration) : iteration in [1..henselExponentCiphertext]];

    return <rk, bootKey, adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead,
            adapted_evalInvConstantsBack, rotationSwitchKeysAhead, switchKeysMinusD, traceKeys, additionConstant,
            liftingPolynomial, lowestDigitRetainPolynomials>;
end function;

// Decode all variables necessary for the thin recryption procedure
function DecodeThinRecryptVariables(variables)
    return variables[1], variables[2], variables[3], variables[4], variables[5], variables[6], variables[7],
           variables[8], variables[9], variables[10], variables[11], variables[12];
end function;

if p mod 4 eq 1 then    // Non-cyclic case

// Generate the switch keys that are necessary during the linear transformations
function GenerateSwitchKeysThinRecrypt(sk)
    // Store backward and rotation switch keys
    rotationSwitchKeysAhead := [];
    switchKeysMinusD := [];

    // First stage
    dimensions := [GetNbDimensions(), 1];
    keys, back_key := MatMul2DBabyGiantSwitchKeys(sk, dimensions: is_good_dimension := false);
    Append(~rotationSwitchKeysAhead, keys); Append(~switchKeysMinusD, back_key);

    // Other stages
    for dim := 2 to GetNbDimensions() - 1 do
        generators, dim_sizes := ComputeGenSizes([dim]);
        if dim eq GetNbDimensions() - 1 then
            Append(~rotationSwitchKeysAhead, MatMulGeneralBabyGiantSwitchKeys(sk, generators, dim_sizes));
        else
            keys, back_key := MatMulGeneralBabyGiantSwitchKeys(sk, generators, dim_sizes: bad_dimension := dim);
            Append(~rotationSwitchKeysAhead, keys); Append(~switchKeysMinusD, back_key);
        end if;
    end for;

    // Generate trace switch keys
    traceKeys := [GenSwitchKey(sk, p ^ (d div (2 ^ i))) : i in [1..Valuation(d, 2)]];

    return rotationSwitchKeysAhead, switchKeysMinusD, traceKeys;
end function;

// Generate the constants for the linear transformations
function GenerateThinConstants(henselExponentPlaintext, henselExponentCiphertext)
    adapted_evalConstantsAhead := []; adapted_evalConstantsBack := [];
    adapted_evalInvConstantsAhead := []; adapted_evalInvConstantsBack := [];

    // First stage
    dimensions := [GetNbDimensions(), 1];
    constants := SparseEvalStage_1Constants(dimensions, henselExponentPlaintext);
    adapted_constantsAhead, adapted_constantsBack := MatMul2DBadDimensionAdaptedConstants(constants, dimensions,
                                                                                          henselExponentPlaintext);
    Append(~adapted_evalConstantsAhead, adapted_constantsAhead);
    Append(~adapted_evalConstantsBack, adapted_constantsBack);

    inverse_constants := SparseEvalInvStage_1Constants(dimensions, henselExponentCiphertext);
    for index := 1 to #inverse_constants do     // Compensate for extra factor of d
        inverse_constants[index] *:= Modinv(d, p ^ henselExponentCiphertext);
        inverse_constants[index] := inverse_constants[index] mod (p ^ henselExponentCiphertext);
    end for;
    adapted_constantsAhead, adapted_constantsBack := MatMul2DBadDimensionAdaptedConstants(inverse_constants, dimensions,
                                                                                          henselExponentCiphertext);
    Append(~adapted_evalInvConstantsAhead, adapted_constantsAhead);
    Append(~adapted_evalInvConstantsBack, adapted_constantsBack);

    // Other stages
    for dim := 2 to GetNbDimensions() - 1 do
        constants := SparseEvalStage_dimConstants(dim, henselExponentPlaintext);
        inverse_constants := SparseEvalInvStage_dimConstants(dim, henselExponentCiphertext);
        if dim eq GetNbDimensions() - 1 then
            adapted_constantsAhead := MatMul1DGoodDimensionAdaptedConstants(constants, dim, henselExponentPlaintext);
            Append(~adapted_evalConstantsAhead, adapted_constantsAhead);

            adapted_constantsAhead := MatMul1DGoodDimensionAdaptedConstants(inverse_constants, dim, henselExponentCiphertext);
            Append(~adapted_evalInvConstantsAhead, adapted_constantsAhead);
        else
            adapted_constantsAhead, adapted_constantsBack := MatMul1DBadDimensionAdaptedConstants(constants, dim,
                                                                                                  henselExponentPlaintext);
            Append(~adapted_evalConstantsAhead, adapted_constantsAhead);
            Append(~adapted_evalConstantsBack, adapted_constantsBack);

            adapted_constantsAhead, adapted_constantsBack := MatMul1DBadDimensionAdaptedConstants(inverse_constants, dim,
                                                                                                  henselExponentCiphertext);
            Append(~adapted_evalInvConstantsAhead, adapted_constantsAhead);
            Append(~adapted_evalInvConstantsBack, adapted_constantsBack);
        end if;
    end for;

    return adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead, adapted_evalInvConstantsBack;
end function;

// Given a thin ciphertext c, return a recryption of all of its slots
function ThinRecrypt(c, recrypt_variables)
    // Decode recryption variables
    rk, bootKey, adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead,
    adapted_evalInvConstantsBack, rotationSwitchKeysAhead, switchKeysMinusD, traceKeys, additionConstant,
    liftingPolynomial, lowestDigitRetainPolynomials := DecodeThinRecryptVariables(recrypt_variables);

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

    // Homomorphic inner product
    u := HomomorphicInnerProduct(c, bootKey, additionConstant);

    // Evaluate trace to subring that encodes sparse plaintexts
    u := EvaluateTrace(u, traceKeys);

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

    // Digit extraction
    henselExponentCiphertext := GetHenselExponent(bootKey);
    return OurDigitExtraction(u, p, henselExponentCiphertext,
                                    henselExponentCiphertext - GetHenselExponent(c),
                              addFunc, subFunc, func<x, y | mulFunc(x, y, rk)>,
                              div_pFunc, lowestDigitRetainPolynomials);
end function;

else    // Cyclic case

// Generate the switch keys that are necessary during the linear transformations
function GenerateSwitchKeysThinRecrypt(sk)
    // Store backward and rotation switch keys
    rotationSwitchKeysAhead := [];
    switchKeysMinusD := [];

    // Generate switch keys for all dimensions
    for dim := 1 to GetNbDimensions() do
        generators, dim_sizes := ComputeGenSizes([dim]);
        if dim eq GetNbDimensions() then
            Append(~rotationSwitchKeysAhead, MatMulGeneralBabyGiantSwitchKeys(sk, generators, dim_sizes));
        else
            keys, back_key := MatMulGeneralBabyGiantSwitchKeys(sk, generators, dim_sizes: bad_dimension := dim);
            Append(~rotationSwitchKeysAhead, keys); Append(~switchKeysMinusD, back_key);
        end if;
    end for;

    // Generate trace switch keys
    traceKeys := [GenSwitchKey(sk, p ^ (d div (2 ^ i))) : i in [1..Valuation(d, 2)]];

    return rotationSwitchKeysAhead, switchKeysMinusD, traceKeys;
end function;

// Generate the constants for the linear transformations
function GenerateThinConstants(henselExponentPlaintext, henselExponentCiphertext)
    adapted_evalConstantsAhead := []; adapted_evalConstantsBack := [];
    adapted_evalInvConstantsAhead := []; adapted_evalInvConstantsBack := [];

    for dim := 1 to GetNbDimensions() do
        constants := SparseEvalStage_dimConstants(dim, henselExponentPlaintext);
        inverse_constants := SparseEvalInvStage_dimConstants(dim, henselExponentCiphertext);
        if dim eq GetNbDimensions() then
            // Forward
            adapted_constantsAhead := MatMul1DGoodDimensionAdaptedConstants(constants, dim, henselExponentPlaintext);
            Append(~adapted_evalConstantsAhead, adapted_constantsAhead);

            // Inverse
            for index := 1 to #inverse_constants do     // Compensate for extra factor of d
                inverse_constants[index] *:= Modinv(d, p ^ henselExponentCiphertext);
                inverse_constants[index] := inverse_constants[index] mod (p ^ henselExponentCiphertext);
            end for;
            adapted_constantsAhead := MatMul1DGoodDimensionAdaptedConstants(inverse_constants, dim, henselExponentCiphertext);
            Append(~adapted_evalInvConstantsAhead, adapted_constantsAhead);
        else
            // Forward
            adapted_constantsAhead, adapted_constantsBack := MatMul1DBadDimensionAdaptedConstants(constants, dim,
                                                                                                  henselExponentPlaintext);
            Append(~adapted_evalConstantsAhead, adapted_constantsAhead);
            Append(~adapted_evalConstantsBack, adapted_constantsBack);

            // Inverse
            adapted_constantsAhead, adapted_constantsBack := MatMul1DBadDimensionAdaptedConstants(inverse_constants, dim,
                                                                                                  henselExponentCiphertext);
            Append(~adapted_evalInvConstantsAhead, adapted_constantsAhead);
            Append(~adapted_evalInvConstantsBack, adapted_constantsBack);
        end if;
    end for;

    return adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead, adapted_evalInvConstantsBack;
end function;

// Given a thin ciphertext c, return a recryption of all of its slots
function ThinRecrypt(c, recrypt_variables)
    // Decode recryption variables
    rk, bootKey, adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead,
    adapted_evalInvConstantsBack, rotationSwitchKeysAhead, switchKeysMinusD, traceKeys, additionConstant,
    liftingPolynomial, lowestDigitRetainPolynomials := DecodeThinRecryptVariables(recrypt_variables);

    for dim := 1 to GetNbDimensions() do
        if dim eq GetNbDimensions() then
            c := MatMul1DGoodDimensionBabyGiant(c, adapted_evalConstantsAhead[dim], dim, rotationSwitchKeysAhead[dim]);
        else
            c := MatMul1DBadDimensionBabyGiant(c, adapted_evalConstantsAhead[dim], adapted_evalConstantsBack[dim],
                                               dim, rotationSwitchKeysAhead[dim], switchKeysMinusD[dim]);
        end if;
    end for;

    // Homomorphic inner product
    u := HomomorphicInnerProduct(c, bootKey, additionConstant);

    // Evaluate trace to subring that encodes sparse plaintexts
    u := EvaluateTrace(u, traceKeys);

    dim := GetNbDimensions();
    while dim ge 1 do
        if dim eq GetNbDimensions() then
            u := MatMul1DGoodDimensionBabyGiant(u, adapted_evalInvConstantsAhead[dim], dim, rotationSwitchKeysAhead[dim]);
        else
            u := MatMul1DBadDimensionBabyGiant(u, adapted_evalInvConstantsAhead[dim], adapted_evalInvConstantsBack[dim],
                                               dim, rotationSwitchKeysAhead[dim], switchKeysMinusD[dim]);
        end if;
        dim -:= 1;
    end while;

    // Remove imaginary part from slots
    u := Add(u, ApplyAutomorphismCiphertext(u, p, traceKeys[#traceKeys]));

    // Digit extraction
    henselExponentCiphertext := GetHenselExponent(bootKey);
    return OurDigitExtraction(u, p, henselExponentCiphertext,
                                    henselExponentCiphertext - GetHenselExponent(c),
                              addFunc, subFunc, func<x, y | mulFunc(x, y, rk)>,
                              div_pFunc, lowestDigitRetainPolynomials);
end function;

end if;

else

error "Desired version of linear transformations is not supported!";

end if;