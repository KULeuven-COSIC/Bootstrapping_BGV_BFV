load "Linear maps/GeneralCyclotomic/Linear_maps.m";
load "Linear maps/PowerOfTwo/Linear_maps.m";
load "Digit extraction/Digit_extraction.m";
load "Bootstrapping/Common.m";

// HElib version of bootstrapping
if GetLTVersion() eq 1 then

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
function GenerateRecryptVariables(sk, pk, henselExponentPlaintext, henselExponentCiphertext, B)
    assert henselExponentPlaintext lt henselExponentCiphertext;
    assert B le p ^ (henselExponentCiphertext - henselExponentPlaintext) div 2;
    assert (B eq p ^ (henselExponentCiphertext - henselExponentPlaintext) div 2) or
           ((henselExponentCiphertext eq 2) and (p ne 2));

    // Generate various keys and constants for the linear maps
    rk := GenRelinKey(sk);
    bootKey := GenBootKeyRecrypt(sk, pk, henselExponentCiphertext);
    adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead, adapted_evalInvConstantsBack,
    unpackConstants, repackConstants := GenerateConstants(henselExponentPlaintext, henselExponentCiphertext);
    rotationSwitchKeysAhead, switchKeyMinusD, frobeniusSwitchKeys := GenerateSwitchKeysRecrypt(sk);
    additionConstant := (p ^ (henselExponentCiphertext - henselExponentPlaintext) div 2) * SumPowerfulBasis(factors_m);

    // Generate required polynomials
    if (henselExponentCiphertext eq 2) and (p ne 2) then
        liftingPolynomial := []; lowestDigitRetainPolynomials := [];
        lowestDigitRemovalPolynomialOverRange := GetLowestDigitRemovalPolynomialOverRange(p, B);
    else
        liftingPolynomial := GetLiftingPolynomial(p, henselExponentCiphertext - 1);
        lowestDigitRetainPolynomials := [GetLowestDigitRetainPolynomial(p, iteration) :
                                         iteration in [1..henselExponentCiphertext]];
        lowestDigitRemovalPolynomialOverRange := [];
    end if;

    return <rk, bootKey, adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead,
            adapted_evalInvConstantsBack, unpackConstants, repackConstants, rotationSwitchKeysAhead, switchKeyMinusD,
            frobeniusSwitchKeys, additionConstant, liftingPolynomial, lowestDigitRetainPolynomials,
            lowestDigitRemovalPolynomialOverRange>;
end function;

// Decode all variables necessary for the recryption procedure
function DecodeRecryptVariables(variables)
    return variables[1], variables[2], variables[3], variables[4], variables[5], variables[6], variables[7], variables[8],
           variables[9], variables[10], variables[11], variables[12], variables[13], variables[14], variables[15];
end function;

// Given a fully packed ciphertext c, return a recryption of all of its coefficients
function Recrypt(c, recrypt_variables)
    // Decode recryption variables
    rk, bootKey, adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead,
    adapted_evalInvConstantsBack, unpackConstants, repackConstants, rotationSwitchKeysAhead, switchKeyMinusD,
    frobeniusSwitchKeys, additionConstant, liftingPolynomial, lowestDigitRetainPolynomials,
    lowestDigitRemovalPolynomialOverRange := DecodeRecryptVariables(recrypt_variables);

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
        if (henselExponentCiphertext eq 2) and (p ne 2) then
            unpacked_u[ind] := BoundedRangeDigitExtraction(unpacked_u[ind], addFunc, func<x, y | mulFunc(x, y, rk)>,
                                                           div_pFunc, lowestDigitRemovalPolynomialOverRange);
        else
            unpacked_u[ind] := OurDigitExtraction(unpacked_u[ind], henselExponentCiphertext,
                                                  henselExponentCiphertext - GetHenselExponent(c),
                                                  addFunc, subFunc, func<x, y | mulFunc(x, y, rk)>,
                                                  div_pFunc, lowestDigitRetainPolynomials);
        end if;
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

// Our version of bootstrapping
elif GetLTVersion() eq 3 then

// We need at least two dimensions, because matrix factors are merged with M and M^(-1)
// One can get rid of this merging by setting the first and last matrix dimension to 1
// However, to facilitate the implementation, this is not allowed for the first matrix
// dimension if p = 1 (mod 4): its size must be greater than 1
if #mat_dimensions lt 2 then
    error "There must be at least two matrix dimensions.";
end if;

// Generate all variables necessary for the recryption procedure
forward GenerateSwitchKeysRecrypt; forward GenerateConstants;
function GenerateRecryptVariables(sk, pk, henselExponentPlaintext, henselExponentCiphertext, B)
    assert henselExponentPlaintext lt henselExponentCiphertext;
    assert B le p ^ (henselExponentCiphertext - henselExponentPlaintext) div 2;
    assert (B eq p ^ (henselExponentCiphertext - henselExponentPlaintext) div 2) or
           ((henselExponentCiphertext eq 2) and (p ne 2));

    // Generate various keys and constants for the linear maps
    rk := GenRelinKey(sk);
    bootKey := GenBootKeyRecrypt(sk, pk, henselExponentCiphertext);
    adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead,
    adapted_evalInvConstantsBack := GenerateConstants(henselExponentPlaintext, henselExponentCiphertext);
    rotationSwitchKeysAhead, switchKeysMinusD, unpackingKeys := GenerateSwitchKeysRecrypt(sk);
    additionConstant := (p ^ (henselExponentCiphertext - henselExponentPlaintext) div 2) * SumPowerfulBasis(factors_m);

    // Generate required polynomials
    if (henselExponentCiphertext eq 2) and (p ne 2) then
        liftingPolynomial := []; lowestDigitRetainPolynomials := [];
        lowestDigitRemovalPolynomialOverRange := GetLowestDigitRemovalPolynomialOverRange(p, B);
    else
        liftingPolynomial := GetLiftingPolynomial(p, henselExponentCiphertext - 1);
        lowestDigitRetainPolynomials := [GetLowestDigitRetainPolynomial(p, iteration) :
                                         iteration in [1..henselExponentCiphertext]];
        lowestDigitRemovalPolynomialOverRange := [];
    end if;

    return <rk, bootKey, adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead,
            adapted_evalInvConstantsBack, rotationSwitchKeysAhead, switchKeysMinusD, unpackingKeys, additionConstant,
            liftingPolynomial, lowestDigitRetainPolynomials, lowestDigitRemovalPolynomialOverRange>;
end function;

// Decode all variables necessary for the recryption procedure
function DecodeRecryptVariables(variables)
    return variables[1], variables[2], variables[3], variables[4], variables[5], variables[6], variables[7], variables[8],
           variables[9], variables[10], variables[11], variables[12], variables[13];
end function;

if p mod 4 eq 1 then    // Non-cyclic case

// Generate the switch keys that are necessary during the linear transformations
function GenerateSwitchKeysRecrypt(sk)
    // Store backward and rotation switch keys
    rotationSwitchKeysAhead := [];
    switchKeysMinusD := [];

    // First stage merged with M and M^(-1)
    dimensions := [GetNbDimensions(), 1]; generators, dim_sizes := ComputeGenSizes(dimensions);
    keys, back_key := MatMulGeneralBabyGiantSwitchKeys(sk, [p] cat generators, [d] cat dim_sizes: bad_dimension := 1);
    Append(~rotationSwitchKeysAhead, keys); Append(~switchKeysMinusD, back_key);

    // Other stages
    for dim := 2 to GetNbDimensions() - 2 do
        generators, dim_sizes := ComputeGenSizes([dim]);
        keys, back_key := MatMulGeneralBabyGiantSwitchKeys(sk, generators, dim_sizes: bad_dimension := dim);
        Append(~rotationSwitchKeysAhead, keys); Append(~switchKeysMinusD, back_key);
    end for;

    // Last stage merged with M and M^(-1)
    dim := GetNbDimensions() - 1; dim_size := d * GetDimensionSize(dim);
    Append(~rotationSwitchKeysAhead, MatMulGeneralBabyGiantSwitchKeys(sk, [(5 ^ (m div (4 * dim_size))) mod m], [dim_size]));

    // Generate unpacking keys
    unpackingKeys := [GenSwitchKey(sk, Modexp(p, d div (2 ^ i), m)) : i in [1..Valuation(d, 2)]];
    return rotationSwitchKeysAhead, switchKeysMinusD, unpackingKeys;
end function;

// Generate the constants for the linear transformations
function GenerateConstants(henselExponentPlaintext, henselExponentCiphertext)
    adapted_evalConstantsAhead := []; adapted_evalConstantsBack := [];
    adapted_evalInvConstantsAhead := []; adapted_evalInvConstantsBack := [];

    // Constants for M and M^(-1)
    M_constants := ComputeMConstants(henselExponentCiphertext);
    MInv_constants := ComputeMInvConstants(henselExponentCiphertext);

    // First stage merged with M
    dimensions := [GetNbDimensions(), 1]; first_generators, first_dim_sizes := ComputeGenSizes(dimensions);
    first_constants := SparseEvalStage_1Constants(dimensions, henselExponentPlaintext);
    constants, generators, dim_sizes := MergeMaps(M_constants, [p], [d], first_constants, first_generators,
                                                  first_dim_sizes, true, henselExponentPlaintext: outer_bad_dimension := 1);
    adapted_constantsAhead, adapted_constantsBack := MatMulGeneralBadDimensionAdaptedConstants(constants, generators, dim_sizes,
                                                                                               1, henselExponentPlaintext);
    Append(~adapted_evalConstantsAhead, adapted_constantsAhead); Append(~adapted_evalConstantsBack, adapted_constantsBack);

    // First stage merged with M^(-1)
    first_inverse_constants := SparseEvalInvStage_1Constants(dimensions, henselExponentCiphertext);
    for index := 1 to #first_inverse_constants do     // Compensate for extra factor of d
        first_inverse_constants[index] *:= Modinv(d, p ^ henselExponentCiphertext);
        first_inverse_constants[index] := first_inverse_constants[index] mod (p ^ henselExponentCiphertext);
    end for;
    constants := MergeMaps(first_inverse_constants, first_generators, first_dim_sizes, MInv_constants,
                           [p], [d], false, henselExponentCiphertext);
    adapted_constantsAhead, adapted_constantsBack := MatMulGeneralBadDimensionAdaptedConstants(constants, generators, dim_sizes,
                                                                                               1, henselExponentCiphertext);
    Append(~adapted_evalInvConstantsAhead, adapted_constantsAhead); Append(~adapted_evalInvConstantsBack, adapted_constantsBack);

    // Other stages
    for dim := 2 to GetNbDimensions() - 2 do
        constants := SparseEvalStage_dimConstants(dim, henselExponentPlaintext);
        adapted_constantsAhead, adapted_constantsBack := MatMul1DBadDimensionAdaptedConstants(constants, dim,
                                                                                              henselExponentPlaintext);
        Append(~adapted_evalConstantsAhead, adapted_constantsAhead);
        Append(~adapted_evalConstantsBack, adapted_constantsBack);

        inverse_constants := SparseEvalInvStage_dimConstants(dim, henselExponentCiphertext);
        adapted_constantsAhead, adapted_constantsBack := MatMul1DBadDimensionAdaptedConstants(inverse_constants, dim,
                                                                                              henselExponentCiphertext);
        Append(~adapted_evalInvConstantsAhead, adapted_constantsAhead);
        Append(~adapted_evalInvConstantsBack, adapted_constantsBack);
    end for;

    // New generator for last dimension
    dim := GetNbDimensions() - 1; new_dim_sizes := [d * GetDimensionSize(dim)];
    new_generators := [(5 ^ (m div (4 * new_dim_sizes[1]))) mod m];

    // Last stage merged with M^(-1)
    last_generators, last_dim_sizes := ComputeGenSizes([dim]);
    last_constants := SparseEvalStage_dimConstants(dim, henselExponentPlaintext);
    constants, generators, dim_sizes := MergeMaps(last_constants, last_generators, last_dim_sizes, MInv_constants,
                                                  [p], [d], false, henselExponentPlaintext);
    constants := MergeGenerators(constants, generators, dim_sizes, new_generators, new_dim_sizes, henselExponentPlaintext:
                                 old_bad_dimension := dim);
    adapted_constantsAhead := MatMulGeneralGoodDimensionAdaptedConstants(constants, new_generators, new_dim_sizes,
                                                                         henselExponentPlaintext);
    Append(~adapted_evalConstantsAhead, adapted_constantsAhead);

    // Last stage merged with M
    last_inverse_constants := SparseEvalInvStage_dimConstants(dim, henselExponentCiphertext);
    constants := MergeMaps(M_constants, [p], [d], last_inverse_constants, last_generators, last_dim_sizes,
                           true, henselExponentCiphertext: outer_bad_dimension := dim);
    constants := MergeGenerators(constants, generators, dim_sizes, new_generators, new_dim_sizes, henselExponentCiphertext:
                                 old_bad_dimension := dim);
    adapted_constantsAhead := MatMulGeneralGoodDimensionAdaptedConstants(constants, new_generators, new_dim_sizes,
                                                                         henselExponentCiphertext);
    Append(~adapted_evalInvConstantsAhead, adapted_constantsAhead);

    return adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead, adapted_evalInvConstantsBack;
end function;

// Given a fully packed ciphertext c, return a recryption of all of its coefficients
function Recrypt(c, recrypt_variables)
    // Decode recryption variables
    rk, bootKey, adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead,
    adapted_evalInvConstantsBack, rotationSwitchKeysAhead, switchKeysMinusD, unpackingKeys,
    additionConstant, liftingPolynomial, lowestDigitRetainPolynomials,
    lowestDigitRemovalPolynomialOverRange := DecodeRecryptVariables(recrypt_variables);

    // Compute generators
    dimensions := [GetNbDimensions(), 1]; first_generators, first_dim_sizes := ComputeGenSizes(dimensions);
    first_generators := [p] cat first_generators; first_dim_sizes := [d] cat first_dim_sizes;
    dim := GetNbDimensions() - 1; new_dim_sizes := [d * GetDimensionSize(dim)];
    new_generators := [(5 ^ (m div (4 * new_dim_sizes[1]))) mod m];

    timer_inner_product := StartTiming();

    // Start with homomorphic inner product
    u := HomomorphicInnerProduct(c, bootKey, additionConstant);

    PrintNoiseBudget(u: message := "after inner product");
    StopTiming(timer_inner_product: message := "inner product");
    timer_first_lt := StartTiming();

    // Last stage merged with M
    u := MatMulGeneralGoodDimensionBabyGiant(u, adapted_evalInvConstantsAhead[dim], new_generators, new_dim_sizes,
                                             rotationSwitchKeysAhead[dim]);

    // Other stages
    dim := GetNbDimensions() - 2;
    while dim ge 2 do
        u := MatMul1DBadDimensionBabyGiant(u, adapted_evalInvConstantsAhead[dim], adapted_evalInvConstantsBack[dim],
                                           dim, rotationSwitchKeysAhead[dim], switchKeysMinusD[dim]);
        dim -:= 1;
    end while;

    // First stage merged with M^(-1)
    u := MatMulGeneralBadDimensionBabyGiant(u, adapted_evalInvConstantsAhead[1], adapted_evalInvConstantsBack[1], first_generators,
                                            first_dim_sizes, 1, rotationSwitchKeysAhead[1], switchKeysMinusD[1]);
    
    PrintNoiseBudget(u: message := "after first LT");
    StopTiming(timer_first_lt: message := "first LT");
    timer_unpack := StartTiming();

    // Unpack the slots
    unpacked_u := UnpackSlotsPowerOfTwo(u, unpackingKeys);

    PrintNoiseBudget(unpacked_u[1]: message := "after unpacking");
    StopTiming(timer_unpack: message := "unpacking");
    timer_digit_extract := StartTiming();

    // Digit extraction
    henselExponentCiphertext := GetHenselExponent(bootKey);
    for ind := 1 to #unpacked_u do
        if (henselExponentCiphertext eq 2) and (p ne 2) then
            unpacked_u[ind] := BoundedRangeDigitExtraction(unpacked_u[ind], addFunc, func<x, y | mulFunc(x, y, rk)>,
                                                           div_pFunc, lowestDigitRemovalPolynomialOverRange);
        else
            unpacked_u[ind] := OurDigitExtraction(unpacked_u[ind], henselExponentCiphertext,
                                                  henselExponentCiphertext - GetHenselExponent(c),
                                                  addFunc, subFunc, func<x, y | mulFunc(x, y, rk)>,
                                                  div_pFunc, lowestDigitRetainPolynomials);
        end if;
    end for;

    PrintNoiseBudget(unpacked_u[1]: message := "after digit extract");
    StopTiming(timer_digit_extract: message := "digit extract");
    timer_repack := StartTiming();

    // Repack the slots
    u := RepackSlotsPowerOfTwo(unpacked_u);

    PrintNoiseBudget(u: message := "after repacking");
    StopTiming(timer_repack: message := "repacking");
    timer_second_lt := StartTiming();

    // First stage merged with M
    u := MatMulGeneralBadDimensionBabyGiant(u, adapted_evalConstantsAhead[1], adapted_evalConstantsBack[1], first_generators,
                                            first_dim_sizes, 1, rotationSwitchKeysAhead[1], switchKeysMinusD[1]);

    // Other stages
    for dim := 2 to GetNbDimensions() - 2 do
        u := MatMul1DBadDimensionBabyGiant(u, adapted_evalConstantsAhead[dim], adapted_evalConstantsBack[dim],
                                           dim, rotationSwitchKeysAhead[dim], switchKeysMinusD[dim]);
    end for;

    // Last stage merged with M^(-1)
    dim := GetNbDimensions() - 1;
    res := MatMulGeneralGoodDimensionBabyGiant(u, adapted_evalConstantsAhead[dim], new_generators, new_dim_sizes,
                                               rotationSwitchKeysAhead[dim]);
    PrintNoiseBudget(res: message := "after second LT");
    StopTiming(timer_second_lt: message := "second LT");
    return res;
end function;

else    // Cyclic case

// Generate the switch keys that are necessary during the linear transformations
function GenerateSwitchKeysRecrypt(sk)
    // Store backward and rotation switch keys
    rotationSwitchKeysAhead := [];
    switchKeysMinusD := [];

    // First stage merged with M and M^(-1)
    generators, dim_sizes := ComputeGenSizes([1]);
    keys, back_key := MatMulGeneralBabyGiantSwitchKeys(sk, [(p ^ 2) mod m] cat generators,
                                                           [d div 2] cat dim_sizes: bad_dimension := 1);
    Append(~rotationSwitchKeysAhead, keys); Append(~switchKeysMinusD, back_key);

    // Generate switch keys for all dimensions
    for dim := 2 to GetNbDimensions() - 1 do
        generators, dim_sizes := ComputeGenSizes([dim]);
        keys, back_key := MatMulGeneralBabyGiantSwitchKeys(sk, generators, dim_sizes: bad_dimension := dim);
        Append(~rotationSwitchKeysAhead, keys); Append(~switchKeysMinusD, back_key);
    end for;

    // Last stage merged with M and M^(-1)
    dim := GetNbDimensions(); dim_size := (d div 2) * GetDimensionSize(dim);
    Append(~rotationSwitchKeysAhead, MatMulGeneralBabyGiantSwitchKeys(sk, [(5 ^ (m div (4 * dim_size))) mod m], [dim_size]));

    // Generate unpacking keys
    unpackingKeys := [GenSwitchKey(sk, Modexp(p, d div (2 ^ i), m)) : i in [1..Valuation(d, 2)]];
    return rotationSwitchKeysAhead, switchKeysMinusD, unpackingKeys;
end function;

// Generate the constants for the linear transformations
function GenerateConstants(henselExponentPlaintext, henselExponentCiphertext)
    adapted_evalConstantsAhead := []; adapted_evalConstantsBack := [];
    adapted_evalInvConstantsAhead := []; adapted_evalInvConstantsBack := [];

    // Constants for M and M^(-1)
    M_constants := ComputeMConstants(henselExponentCiphertext);
    M_constants := [M_constants[2 * i - 1] : i in [1..#M_constants div 2]];
    MInv_constants := ComputeMInvConstants(henselExponentCiphertext);
    MInv_constants := [MInv_constants[2 * i - 1] : i in [1..#MInv_constants div 2]];

    // First stage merged with M
    first_generators, first_dim_sizes := ComputeGenSizes([1]);
    first_constants := SparseEvalStage_dimConstants(1, henselExponentPlaintext);
    constants, generators, dim_sizes := MergeMaps(M_constants, [(p ^ 2) mod m], [d div 2], first_constants, first_generators,
                                                  first_dim_sizes, true, henselExponentPlaintext: outer_bad_dimension := 1);
    adapted_constantsAhead, adapted_constantsBack := MatMulGeneralBadDimensionAdaptedConstants(constants, generators, dim_sizes,
                                                                                               1, henselExponentPlaintext);
    Append(~adapted_evalConstantsAhead, adapted_constantsAhead); Append(~adapted_evalConstantsBack, adapted_constantsBack);

    // First stage merged with M^(-1)
    first_inverse_constants := SparseEvalInvStage_dimConstants(1, henselExponentCiphertext);
    constants := MergeMaps(first_inverse_constants, first_generators, first_dim_sizes, MInv_constants,
                           [(p ^ 2) mod m], [d div 2], false, henselExponentCiphertext);
    adapted_constantsAhead, adapted_constantsBack := MatMulGeneralBadDimensionAdaptedConstants(constants, generators, dim_sizes,
                                                                                               1, henselExponentCiphertext);
    Append(~adapted_evalInvConstantsAhead, adapted_constantsAhead); Append(~adapted_evalInvConstantsBack, adapted_constantsBack);

    for dim := 2 to GetNbDimensions() - 1 do
        // Forward
        constants := SparseEvalStage_dimConstants(dim, henselExponentPlaintext);
        adapted_constantsAhead, adapted_constantsBack := MatMul1DBadDimensionAdaptedConstants(constants, dim,
                                                                                              henselExponentPlaintext);
        Append(~adapted_evalConstantsAhead, adapted_constantsAhead);
        Append(~adapted_evalConstantsBack, adapted_constantsBack);

        // Inverse
        inverse_constants := SparseEvalInvStage_dimConstants(dim, henselExponentCiphertext);
        adapted_constantsAhead, adapted_constantsBack := MatMul1DBadDimensionAdaptedConstants(inverse_constants, dim,
                                                                                              henselExponentCiphertext);
        Append(~adapted_evalInvConstantsAhead, adapted_constantsAhead);
        Append(~adapted_evalInvConstantsBack, adapted_constantsBack);
    end for;

    // New generator for last dimension
    dim := GetNbDimensions(); new_dim_sizes := [(d div 2) * GetDimensionSize(dim)];
    new_generators := [(5 ^ (m div (4 * new_dim_sizes[1]))) mod m];

    // Last stage merged with M^(-1)
    last_generators, last_dim_sizes := ComputeGenSizes([dim]);
    last_constants := SparseEvalStage_dimConstants(dim, henselExponentPlaintext);
    constants, generators, dim_sizes := MergeMaps(last_constants, last_generators, last_dim_sizes, MInv_constants,
                                                  [(p ^ 2) mod m], [d div 2], false, henselExponentPlaintext);
    constants := MergeGenerators(constants, generators, dim_sizes, new_generators, new_dim_sizes, henselExponentPlaintext:
                                 old_bad_dimension := dim);
    adapted_constantsAhead := MatMulGeneralGoodDimensionAdaptedConstants(constants, new_generators, new_dim_sizes,
                                                                         henselExponentPlaintext);
    Append(~adapted_evalConstantsAhead, adapted_constantsAhead);

    // Last stage merged with M
    last_inverse_constants := SparseEvalInvStage_dimConstants(dim, henselExponentCiphertext);
    for index := 1 to #last_inverse_constants do     // Compensate for extra factor of d
        last_inverse_constants[index] *:= Modinv(d, p ^ henselExponentCiphertext);
        last_inverse_constants[index] := last_inverse_constants[index] mod (p ^ henselExponentCiphertext);
    end for;
    constants := MergeMaps(M_constants, [(p ^ 2) mod m], [d div 2], last_inverse_constants, last_generators, last_dim_sizes,
                           true, henselExponentCiphertext: outer_bad_dimension := dim);
    constants := MergeGenerators(constants, generators, dim_sizes, new_generators, new_dim_sizes, henselExponentCiphertext:
                                 old_bad_dimension := dim);
    adapted_constantsAhead := MatMulGeneralGoodDimensionAdaptedConstants(constants, new_generators, new_dim_sizes,
                                                                         henselExponentCiphertext);
    Append(~adapted_evalInvConstantsAhead, adapted_constantsAhead);

    return adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead, adapted_evalInvConstantsBack;
end function;

// Given a fully packed ciphertext c, return a recryption of all of its coefficients
function Recrypt(c, recrypt_variables)
    // Decode recryption variables
    rk, bootKey, adapted_evalConstantsAhead, adapted_evalConstantsBack, adapted_evalInvConstantsAhead,
    adapted_evalInvConstantsBack, rotationSwitchKeysAhead, switchKeysMinusD, unpackingKeys,
    additionConstant, liftingPolynomial, lowestDigitRetainPolynomials,
    lowestDigitRemovalPolynomialOverRange := DecodeRecryptVariables(recrypt_variables);

    // Compute generators
    first_generators, first_dim_sizes := ComputeGenSizes([1]);
    first_generators := [(p ^ 2) mod m] cat first_generators; first_dim_sizes := [d div 2] cat first_dim_sizes;
    dim := GetNbDimensions(); new_dim_sizes := [(d div 2) * GetDimensionSize(dim)];
    new_generators := [(5 ^ (m div (4 * new_dim_sizes[1]))) mod m];

    timer_inner_product := StartTiming();

    // Start with homomorphic inner product
    u := HomomorphicInnerProduct(c, bootKey, additionConstant);

    PrintNoiseBudget(u: message := "after inner product");
    StopTiming(timer_inner_product: message := "inner product");
    timer_first_lt := StartTiming();

    // Last stage merged with M
    u := MatMulGeneralGoodDimensionBabyGiant(u, adapted_evalInvConstantsAhead[dim], new_generators, new_dim_sizes,
                                             rotationSwitchKeysAhead[dim]);

    dim := GetNbDimensions() - 1;
    while dim ge 2 do
        u := MatMul1DBadDimensionBabyGiant(u, adapted_evalInvConstantsAhead[dim], adapted_evalInvConstantsBack[dim],
                                           dim, rotationSwitchKeysAhead[dim], switchKeysMinusD[dim]);
        dim -:= 1;
    end while;

    // First stage merged with M^(-1)
    u := MatMulGeneralBadDimensionBabyGiant(u, adapted_evalInvConstantsAhead[1], adapted_evalInvConstantsBack[1], first_generators,
                                            first_dim_sizes, 1, rotationSwitchKeysAhead[1], switchKeysMinusD[1]);

    PrintNoiseBudget(u: message := "after first LT");
    StopTiming(timer_first_lt: message := "first LT");
    timer_unpack := StartTiming();

    // Unpack the slots
    unpacked_u := UnpackSlotsPowerOfTwo(u, unpackingKeys);

    PrintNoiseBudget(unpacked_u[1]: message := "after unpacking");
    StopTiming(timer_unpack: message := "unpacking");
    timer_digit_extract := StartTiming();

    // Digit extraction
    henselExponentCiphertext := GetHenselExponent(bootKey);
    for ind := 1 to #unpacked_u do
        if (henselExponentCiphertext eq 2) and (p ne 2) then
            unpacked_u[ind] := BoundedRangeDigitExtraction(unpacked_u[ind], addFunc, func<x, y | mulFunc(x, y, rk)>,
                                                           div_pFunc, lowestDigitRemovalPolynomialOverRange);
        else
            unpacked_u[ind] := OurDigitExtraction(unpacked_u[ind], henselExponentCiphertext,
                                                  henselExponentCiphertext - GetHenselExponent(c),
                                                  addFunc, subFunc, func<x, y | mulFunc(x, y, rk)>,
                                                  div_pFunc, lowestDigitRetainPolynomials);
        end if;
    end for;

    PrintNoiseBudget(unpacked_u[1]: message := "after digit extract");
    StopTiming(timer_digit_extract: message := "digit extract");
    timer_repack := StartTiming();

    // Repack the slots
    u := RepackSlotsPowerOfTwo(unpacked_u);

    PrintNoiseBudget(u: message := "after repacking");
    StopTiming(timer_repack: message := "repacking");
    timer_second_lt := StartTiming();

    // First stage merged with M
    u := MatMulGeneralBadDimensionBabyGiant(u, adapted_evalConstantsAhead[1], adapted_evalConstantsBack[1], first_generators,
                                            first_dim_sizes, 1, rotationSwitchKeysAhead[1], switchKeysMinusD[1]);

    for dim := 2 to GetNbDimensions() - 1 do
        u := MatMul1DBadDimensionBabyGiant(u, adapted_evalConstantsAhead[dim], adapted_evalConstantsBack[dim],
                                           dim, rotationSwitchKeysAhead[dim], switchKeysMinusD[dim]);
    end for;

    // Last stage merged with M^(-1)
    dim := GetNbDimensions();
    res := MatMulGeneralGoodDimensionBabyGiant(u, adapted_evalConstantsAhead[dim], new_generators, new_dim_sizes,
                                               rotationSwitchKeysAhead[dim]);
    PrintNoiseBudget(res: message := "after second LT");
    StopTiming(timer_second_lt: message := "second LT");
    return res;
end function;

end if;

else

error "Desired version of linear transformations is not supported!";

end if;