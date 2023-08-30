load "Crypto/BFV/BFV.m";
load "Linear maps/PowerOfTwo/Linear_maps.m";

assert usePowerOfTwo;

// Simulate functionality on plaintext
function SimulateMatMul(m, constants)
    res := [0 : i in [1..l]];

    index := 1;
    dim_sizes := [GetDimensionSize(dim) : dim in [1..GetNbDimensions()]];
    for constant in constants do
        m_parts := GetPlaintextParts(ApplyAutomorphism(m, t, IndexToSequence(index, dim_sizes)));
        constant_parts := GetPlaintextParts(constant);
        res := [((res[i] + constant_parts[i] * m_parts[i]) mod GetFirstSlotFactor()) mod t : i in [1..l]];

        index +:= 1;
    end for;
    return res;
end function;



// Test functionality on ciphertext
sk, pk := GenKeyPair();

m := EmbedInSlots([Random(t - 1) : i in [1..l]]);
c := Encrypt(m, t, pk);

// Test linear transformation
dim_sizes := [GetDimensionSize(dim) : dim in [1..GetNbDimensions()]];
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

"Test linear transformation", res eq SimulateMatMul(m, constants);