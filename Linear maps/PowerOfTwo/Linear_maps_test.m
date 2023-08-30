load "Crypto/BFV/BFV.m";
load "Linear maps/PowerOfTwo/Linear_maps.m";

assert usePowerOfTwo;

// Compute ring structure present on the slots
Zt_F1<y> := GetSlotAlgebra(e);

sk, pk := GenKeyPair();

// Test sparse linear transformations
m := EmbedInSlots([Random(t - 1) : ind in [1..l]]);
c := Encrypt(m, t, pk);

adapted_constants := MatMulAdaptedConstants(SparseConstants(e), e);
switchKeys := [];
for pos := 2 to l do
    Append(~switchKeys, GenSwitchKey(sk, IndexToHypercube(pos)));
end for;
cNew := MatMulBabyGiant(c, adapted_constants, switchKeys);
plaintext := CatZeros(Eltseq(Decrypt(cNew, sk)), n);
result := true;
for index := 1 to n do
    if not IsDivisibleBy(index - 1, d) and plaintext[index] ne 0 then
        result := false;
    end if;
end for;
adapted_constants := MatMulAdaptedConstants(SparseInvConstants(e), e);
cNew := MatMulBabyGiant(cNew, adapted_constants, switchKeys);
"Test sparse linear transformation", result and ((d * Decrypt(cNew, sk)) mod t) eq Decrypt(c, sk);