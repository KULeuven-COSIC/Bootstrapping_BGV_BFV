load "Linear maps/GeneralCyclotomic/Linear_maps.m";
load "Digit extraction/Digit_extraction.m";
load "Bootstrapping/Common.m";

// Generate the switch keys that are necessary during the linear transformations
function GenerateSwitchKeysRecrypt(sk)
    // Rotation switch keys
    rotationSwitchKeysAhead := [[] : i in [1..GetNbDimensions()]];
    for pos := 1 to GetDimensionSize(1) - 1 do
        Append(~rotationSwitchKeysAhead[1], GenSwitchKey(sk, Get1DHyperIndex(1, pos)));
    end for;
    for dim := 2 to GetNbDimensions() do
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
    for exp := 1 to d - 1 do
        Append(~frobeniusSwitchKeys, GenSwitchKey(sk, Modexp(p, exp, m)));
    end for;
    return rotationSwitchKeysAhead, switchKeyMinusD, frobeniusSwitchKeys;
end function;

// Generate the constants for the linear transformations
function GenerateConstants(henselExponentPlaintext, henselExponentCiphertext)
    // Compute constants for linear transformation in dimension 1
    evalStage_1Constants := EvalStage_1Constants(1, henselExponentPlaintext);
    evalInvStage_1Constants := EvalInvStage_1Constants(1, henselExponentCiphertext);

    // Compute adapted constants
    if IsGoodDimension(1) then
        // Eval
        adapted_evalConstantsAhead := [BlockMatMul1DGoodDimensionAdaptedConstants(evalStage_1Constants, 1,
                                                                                  henselExponentPlaintext)];
        adapted_evalConstantsBack := [];

        // EvalInv
        adapted_evalInvConstantsAhead := [BlockMatMul1DGoodDimensionAdaptedConstants(evalInvStage_1Constants, 1,
                                                                                     henselExponentCiphertext)];
        adapted_evalInvConstantsBack := [];
    else
        // Eval
        adapted_constantsAhead, adapted_constantsBack := BlockMatMul1DBadDimensionAdaptedConstants(evalStage_1Constants, 1,
                                                                                                   henselExponentPlaintext);
        adapted_evalConstantsAhead := [adapted_constantsAhead];
        adapted_evalConstantsBack := [adapted_constantsBack];

        // EvalInv
        adapted_constantsAhead, adapted_constantsBack := BlockMatMul1DBadDimensionAdaptedConstants(evalInvStage_1Constants, 1,
                                                                                                   henselExponentCiphertext);
        adapted_evalInvConstantsAhead := [adapted_constantsAhead];
        adapted_evalInvConstantsBack := [adapted_constantsBack];
    end if;

    // Compute constants for linear transformations during stages 2, ..., GetNbDimensions()
    // --> These dimensions are always good
    for dim := 2 to GetNbDimensions() do
        evalStage_dimConstants := EvalStage_dimConstants(dim, henselExponentPlaintext);
        evalInvStage_dimConstants := EvalInvStage_dimConstants(dim, henselExponentCiphertext);

        Append(~adapted_evalConstantsAhead, MatMul1DGoodDimensionAdaptedConstants(evalStage_dimConstants, dim,
                                                                                  henselExponentPlaintext));
        Append(~adapted_evalInvConstantsAhead, MatMul1DGoodDimensionAdaptedConstants(evalInvStage_dimConstants, dim,
                                                                                     henselExponentCiphertext));
    end for;
    unpackConstants := UnpackConstants(henselExponentCiphertext);
    repackConstants := RepackConstants(henselExponentPlaintext);
    return adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead,
           adapted_evalInvConstantsBack, unpackConstants, repackConstants;
end function;

// Generate all variables necessary for the recryption procedure
function GenerateRecryptVariables(sk, pk, henselExponentPlaintext, henselExponentCiphertext)
    // Generate various keys and constants for the linear maps
    rk := GenRelinKey(sk);
    bootKey := GenBootKeyRecrypt(sk, pk, henselExponentCiphertext);
    adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead, adapted_evalInvConstantsBack,
    unpackConstants, repackConstants := GenerateConstants(henselExponentPlaintext, henselExponentCiphertext);
    rotationSwitchKeysAhead, switchKeyMinusD, frobeniusSwitchKeys := GenerateSwitchKeysRecrypt(sk);
    additionConstant := EmbedInPowerfulBasis(Floor((p ^ henselExponentCiphertext) / 2 / (p ^ henselExponentPlaintext)), factors_m);
    liftingPolynomial := GetLiftingPolynomial(p, henselExponentCiphertext - 1);
    lowestDigitRetainPolynomials := [GetLowestDigitRetainPolynomial(p, iteration) : iteration in [1..henselExponentCiphertext]];

    return <rk, bootKey, adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead,
            adapted_evalInvConstantsBack, unpackConstants, repackConstants, rotationSwitchKeysAhead, switchKeyMinusD,
            frobeniusSwitchKeys, additionConstant, liftingPolynomial, lowestDigitRetainPolynomials>;
end function;

// Decode all variables necessary for the recryption procedure
function DecodeRecryptVariables(variables)
    return variables[1], variables[2], variables[3], variables[4], variables[5], variables[6], variables[7], variables[8],
           variables[9], variables[10], variables[11], variables[12], variables[13], variables[14];
end function;

// Given a fully-packed ciphertext c, return a recryption of all of its coefficients
function Recrypt(c, recrypt_variables)
    // Decode recryption variables
    rk, bootKey, adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead,
    adapted_evalInvConstantsBack, unpackConstants, repackConstants, rotationSwitchKeysAhead, switchKeyMinusD, frobeniusSwitchKeys,
    additionConstant, liftingPolynomial, lowestDigitRetainPolynomials := DecodeRecryptVariables(recrypt_variables);

    // Start with homomorphic inner product
    u := HomomorphicInnerProduct(c, bootKey, additionConstant);

    // Apply series of linear maps
    // --> Only the first dimension can be a bad one
    dim := GetNbDimensions();
    while dim ge 2 do
        u := MatMul1DGoodDimensionBabyGiant(u, adapted_evalInvConstantsAhead[dim], dim, rotationSwitchKeysAhead[dim]);
        dim -:= 1;
    end while;
    if IsGoodDimension(1) then
        u := BlockMatMul1DGoodDimensionBabyGiant(u, adapted_evalInvConstantsAhead[1], 1, rotationSwitchKeysAhead[1],
                                                 frobeniusSwitchKeys);
    else
        u := BlockMatMul1DBadDimensionBabyGiant(u, adapted_evalInvConstantsAhead[1], adapted_evalInvConstantsBack[1], 1,
                                                rotationSwitchKeysAhead[1], switchKeyMinusD, frobeniusSwitchKeys);
    end if;

    // Unpack the slots
    unpacked_u := UnpackSlots(u, unpackConstants, frobeniusSwitchKeys);

    // Digit extraction
    henselExponentCiphertext := GetHenselExponent(bootKey);
    for ind := 1 to #unpacked_u do
        unpacked_u[ind] := ChenHanDigitExtraction(unpacked_u[ind], p, henselExponentCiphertext,
                                                                      henselExponentCiphertext - GetHenselExponent(c),
                                                  addFunc, subFunc, func<x, y | mulFunc(x, y, rk)>,
                                                  div_pFunc, liftingPolynomial, lowestDigitRetainPolynomials);
    end for;

    // Repack the slots
    u := RepackSlots(unpacked_u, repackConstants);
    
    // Apply series of linear maps
    // --> Only the first dimension can be a bad one
    if IsGoodDimension(1) then
        u := BlockMatMul1DGoodDimensionBabyGiant(u, adapted_evalConstantsAhead[1], 1, rotationSwitchKeysAhead[1],
                                                 frobeniusSwitchKeys);
    else
        u := BlockMatMul1DBadDimensionBabyGiant(u, adapted_evalConstantsAhead[1], adapted_evalConstantsBack[1], 1,
                                                rotationSwitchKeysAhead[1], switchKeyMinusD, frobeniusSwitchKeys);
    end if;
    for dim := 2 to GetNbDimensions() do
        u := MatMul1DGoodDimensionBabyGiant(u, adapted_evalConstantsAhead[dim], dim, rotationSwitchKeysAhead[dim]);
    end for;
    return u;
end function;