load "Crypto/BFV/BFV.m";
load "Linear maps/GeneralCyclotomic/Linear_maps.m";

// Simulate functionality on plaintext
function SimulateMatMul1D(m, dim, constants)
    res := [0 : i in [1..l]];

    for constant in constants do
        m_parts := GetPlaintextParts(m);
        constant_parts := GetPlaintextParts(constant);
        res := [((res[i] + constant_parts[i] * m_parts[i]) mod GetFirstSlotFactor()) mod t : i in [1..l]];

        m := RotateSlotsPlaintext(m, dim, 1);
    end for;
    return res;
end function;



// Test functionality on ciphertext
sk, pk := GenKeyPair();

m := RandPol(t);
c := Encrypt(m, t, pk);

// Test linear transformation in each dimension
for dim := 1 to GetNbDimensions() do
    dim_size := GetDimensionSize(dim);
    constants := [RandPol(t) : i in [1..dim_size]];
    adapted_constants := MatMul1DGoodDimensionAdaptedConstants(constants, dim, e);
    adapted_constantsAhead, adapted_constantsBack := MatMul1DBadDimensionAdaptedConstants(constants, dim, e);

    // Generate switch keys
    switchKeysAhead := [];
    for pos := 1 to GetDimensionSize(dim) - 1 do
        Append(~switchKeysAhead, GenSwitchKey(sk, Get1DHyperIndex(dim, pos)));
    end for;
    switchKeysBack := [];
    for pos := 1 to GetDimensionSize(dim) - 1 do
        Append(~switchKeysBack, GenSwitchKey(sk, Get1DHyperIndex(dim, pos - GetDimensionSize(dim))));
    end for;
    switchKeyMinusD := GenSwitchKey(sk, Get1DHyperIndex(dim, -GetDimensionSize(dim)));

    // Good vs bad dimension
    if IsGoodDimension(dim) then
        res := GetPlaintextParts(Decrypt(MatMul1DGoodDimensionBabyGiant(c, adapted_constants, dim, switchKeysAhead), sk));
        // res := GetPlaintextParts(Decrypt(MatMul1DGoodDimension(c, constants, dim, switchKeysAhead), sk));
        // --> Naive algorithm: don't use
    else
        res := GetPlaintextParts(Decrypt(MatMul1DBadDimensionBabyGiant(c, adapted_constantsAhead, adapted_constantsBack, dim,
                                                                         switchKeysAhead, switchKeyMinusD), sk));
        // res := GetPlaintextParts(Decrypt(MatMul1DBadDimension(c, constants, dim, switchKeysAhead, switchKeysBack), sk));
        // --> Naive algorithm: don't use
    end if;
    
    "Test linear transformation in dimension", dim, res eq SimulateMatMul1D(m, dim, constants);
end for;