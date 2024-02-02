load "Crypto/BFV/BFV.m";
load "Linear maps/GeneralCyclotomic/Linear_maps.m";

// Test if conversion works
result := true;
for dim := 1 to GetNbDimensions() do
    for index := 1 to d * GetDimensionSize(dim) do
        i, j := IndexToIJ(index, dim);
        if IJToIndex(i, j, dim) ne index then
            result := false;
        end if;
    end for;
end for;
"Test conversion between regular index and two-dimensional index", result;

// Simulate functionality on plaintext
function SimulateBlockMatMul1D(m, dim, constants)
    res := [0 : i in [1..l]];

    for index := 1 to d * GetDimensionSize(dim) do
        i, j := IndexToIJ(index, dim);
        constant_parts := GetPlaintextParts(constants[index]);
        
        m_parts := GetPlaintextParts(ApplyFrobeniusPowerPlaintext(RotateSlotsPlaintext(m, dim, i), j));
        res := [((res[k] + constant_parts[k] * m_parts[k]) mod GetFirstSlotFactor()) mod t : k in [1..l]];
    end for;

    return res;
end function;



// Test functionality on ciphertext
sk, pk := GenKeyPair();

// Generate switch keys
frobeniusSwitchKeys := [];
for exp := 1 to d - 1 do
    Append(~frobeniusSwitchKeys, GenSwitchKey(sk, Modexp(p, exp, m)));
end for;

m := RandPol(t);
c := Encrypt(m, t, pk);

// Test linear transformation in each dimension
for dim := 1 to GetNbDimensions() do
    dim_size := GetDimensionSize(dim);
    constants := [RandPol(t) : i in [1..d * dim_size]];
    adapted_constants := BlockMatMul1DGoodDimensionAdaptedConstants(constants, dim, e);
    adapted_constantsAhead, adapted_constantsBack := BlockMatMul1DBadDimensionAdaptedConstants(constants, dim, e);

    // Generate switch keys
    rotationSwitchKeysAhead := [];
    for pos := 1 to GetDimensionSize(dim) - 1 do
        Append(~rotationSwitchKeysAhead, GenSwitchKey(sk, Get1DHyperIndex(dim, pos)));
    end for;
    rotationSwitchKeysBack := [];
    for pos := 1 to GetDimensionSize(dim) - 1 do
        Append(~rotationSwitchKeysBack, GenSwitchKey(sk, Get1DHyperIndex(dim, pos - GetDimensionSize(dim))));
    end for;
    switchKeyMinusD := GenSwitchKey(sk, Get1DHyperIndex(dim, -GetDimensionSize(dim)));

    if IsGoodDimension(dim) then
        res := GetPlaintextParts(Decrypt(BlockMatMul1DGoodDimensionBabyGiant(c, adapted_constants, dim, rotationSwitchKeysAhead,
                                                                               frobeniusSwitchKeys), sk));
        // res := GetPlaintextParts(Decrypt(BlockMatMul1DGoodDimension(c, constants, dim, rotationSwitchKeysAhead,
        //                                                                                  frobeniusSwitchKeys), sk));
        // --> Naive algorithm: don't use
    else
        res := GetPlaintextParts(Decrypt(BlockMatMul1DBadDimensionBabyGiant(c, adapted_constantsAhead, adapted_constantsBack, dim,
                                                                              rotationSwitchKeysAhead, switchKeyMinusD,
                                                                              frobeniusSwitchKeys), sk));
        // res := GetPlaintextParts(Decrypt(BlockMatMul1DBadDimension(c, constants, dim, rotationSwitchKeysAhead,
        //                                                              rotationSwitchKeysBack, frobeniusSwitchKeys), sk));
        // --> Naive algorithm: don't use
    end if;
    
    "Test linear transformation in dimension", dim, res eq SimulateBlockMatMul1D(m, dim, constants);
end for;