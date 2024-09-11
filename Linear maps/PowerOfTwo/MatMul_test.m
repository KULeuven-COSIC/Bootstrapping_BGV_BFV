load "Crypto/BFV/BFV.m";
load "Linear maps/PowerOfTwo/Linear_maps.m";

assert GetLTVersion() eq 2 or GetLTVersion() eq 3;

// Simulate functionality on plaintext
function SimulateMatMul(m, constants)
    res := [0 : i in [1..l]];

    index := 1;
    dim_sizes := [GetDimensionSize(dim) : dim in [1..GetNbDimensions()]];
    for constant in constants do
        m_parts := GetPlaintextParts(ApplyAutomorphismPlaintext(m, IndexToSequence(index, dim_sizes)));
        constant_parts := GetPlaintextParts(constant);
        res := [((res[i] + constant_parts[i] * m_parts[i]) mod GetFirstSlotFactor()) mod t : i in [1..l]];

        index +:= 1;
    end for;
    return res;
end function;

// Simulate functionality on plaintext
function SimulateMatMul2DBadDimension(m, dimensions, constants)
    res := [0 : i in [1..l]];
    m_orig := m;

    i := 1;
    for constant in constants do
        i +:= 1;
        m_parts := GetPlaintextParts(m);
        constant_parts := GetPlaintextParts(constant);
        res := [((res[i] + constant_parts[i] * m_parts[i]) mod GetFirstSlotFactor()) mod t : i in [1..l]];

        positions := IndexToSequence(i, [GetDimensionSize(dim) : dim in dimensions]);
        m := RotateSlotsPlaintext(RotateSlotsPlaintext(m_orig, dimensions[1], positions[1]), dimensions[2], positions[2]);
    end for;
    return res;
end function;



// Test functionality on ciphertext
sk, pk := GenKeyPair();

mmm := EmbedInSlots([Random(t - 1) : i in [1..l]]);
c := Encrypt(mmm, t, pk);

// Test linear transformation
dim_sizes := [GetDimensionSize(dim) : dim in [1..GetNbDimensions()]];

if GetLTVersion() eq 2 then
constants := [EmbedInSlots([Random(t - 1) : i in [1..l]]) : j in [1..l]];
adapted_constants := MatMulAdaptedConstants(constants, e);

// Generate switch keys
switchKeys := [];
for index := 2 to l do
    Append(~switchKeys, GenSwitchKey(sk, IndexToSequence(index, dim_sizes)));
end for;

res := GetPlaintextParts(Decrypt(MatMulBabyGiant(c, adapted_constants, switchKeys), sk));
// res := GetPlaintextParts(Decrypt(MatMul(c, constants, switchKeys), sk));
// --> Naive algorithm: don't use

"Test linear transformation", res eq SimulateMatMul(mmm, constants);
end if;



// Only perform this test if there is complete splitting
if (GetLTVersion() eq 3) and (p mod m eq 1) then
// Test 2-dimensional linear transformations
mmm := RandPol(t);
c := Encrypt(mmm, t, pk);

// Compute constants
dimensions := [GetNbDimensions() - 1, GetNbDimensions() eq 2 select 2 else 1];
dim_sizes := [GetDimensionSize(dim) : dim in dimensions];
constants := [RandPol(t) : j in [1..&*dim_sizes]];
adapted_constants := MatMul2DGoodDimensionAdaptedConstants(constants, dimensions, e);
adapted_constantsAhead, adapted_constantsBack := MatMul2DBadDimensionAdaptedConstants(constants, dimensions, e);

// Generate switch keys
switchKeysAhead := [];
switchKeysBack := [];
switchKeyMinusD := GenSwitchKey(sk, Get1DHyperIndex(dimensions[2], -dim_sizes[2]));
for index := 2 to &*dim_sizes do
    positions := IndexToSequence(index, dim_sizes);
    hyperIndexAhead := [var in dimensions select positions[Position(dimensions, var)] else 0 : var in [1..GetNbDimensions()]];
    hyperIndexBack := [var in dimensions select positions[Position(dimensions, var)] - (Position(dimensions, var) - 1) *
                            dim_sizes[2] else 0 : var in [1..GetNbDimensions()]];
    Append(~switchKeysAhead, GenSwitchKey(sk, hyperIndexAhead));
    Append(~switchKeysBack, GenSwitchKey(sk, hyperIndexBack));
end for;

if GetNbDimensions() eq 2 then
    // Good dimensions
    res := GetPlaintextParts(Decrypt(MatMul2DGoodDimensionBabyGiant(c, adapted_constants, dimensions, switchKeysAhead), sk));
    // res := GetPlaintextParts(Decrypt(MatMul2DGoodDimension(c, constants, dimensions, switchKeysAhead), sk));
    // --> Naive algorithm: don't use
else
    // Bad dimensions
    res := GetPlaintextParts(Decrypt(MatMul2DBadDimensionBabyGiant(c, adapted_constantsAhead, adapted_constantsBack,
                                                                   dimensions, switchKeysAhead, switchKeyMinusD), sk));
    // res := GetPlaintextParts(Decrypt(MatMul2DBadDimension(c, constants, dimensions, switchKeysAhead, switchKeysBack), sk));
    // --> Naive algorithm: don't use
end if;
"Test 2D linear transformation", res eq SimulateMatMul2DBadDimension(mmm, dimensions, constants);
end if;



// Test unpacking and repacking
mmm := RandPol(t);
c := Encrypt(mmm, t, pk);

switchKeys := [GenSwitchKey(sk, Modexp(p, d div (2 ^ i), m)) : i in [1..Valuation(d, 2)]];
c_seq := UnpackSlotsPowerOfTwo(c, switchKeys);
c_new := RepackSlotsPowerOfTwo(c_seq);
"Test unpacking and repacking cancel each other", Decrypt(c_new, sk) eq (mmm * d mod t);