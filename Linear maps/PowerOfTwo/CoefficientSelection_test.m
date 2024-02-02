load "Crypto/BFV/BFV.m";
load "Linear maps/PowerOfTwo/Linear_maps.m";

assert GetLTVersion() eq 2 or GetLTVersion() eq 3;

sk, pk := GenKeyPair();

m := RandPol(t);
c := Encrypt(m, t, pk);

switchKeys := [GenSwitchKey(sk, (n div (2 ^ i)) + 1) : i in [0..Valuation(d, 2) - 1]];
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

// Coefficient selection is only identical to trace if p = 1 (mod 4)
if p mod 4 eq 1 then
    switchKeys := [GenSwitchKey(sk, p ^ (d div (2 ^ i))) : i in [1..Valuation(d, 2)]];
    cNew_prime := EvaluateTrace(c, switchKeys);

    "Test trace evaluation", Decrypt(cNew, sk) eq Decrypt(cNew_prime, sk);
end if;