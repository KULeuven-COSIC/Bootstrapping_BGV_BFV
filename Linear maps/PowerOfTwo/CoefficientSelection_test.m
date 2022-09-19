load "Crypto/BFV/BFV.m";
load "Linear maps/PowerOfTwo/Linear_maps.m";

assert usePowerOfTwo;

sk, pk := GenKeyPair();

m := RandPol(t);
c := Encrypt(m, t, pk);

switchKeys := [];
for i := 0 to Valuation(d, 2) - 1 do
    Append(~switchKeys, GenSwitchKey(sk, (n div (2 ^ i)) + 1));
end for;
cNew := CoefficientSelection(c, switchKeys);

m_orig := CatZeros(Eltseq(m), n);
m_new := CatZeros(Eltseq(Decrypt(cNew, sk)), n);
res := true;
for index := 1 to n do
    if (IsDivisibleBy(index - 1, d) and (m_new[index] ne ((d * m_orig[index]) mod t))) or
       (not IsDivisibleBy(index - 1, d) and (m_new[index] ne 0)) then
        res := false;
    end if;
end for;
"Test coefficient selection", res;