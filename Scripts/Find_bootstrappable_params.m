load "Crypto/BFV/BFV.m";

// Find all bootstrappable parameters in the given range of m
m_range := [2^9..2^10];
d_max := 25;
m_max := 1000;

for m in m_range do
    d := Order(Integers(m)!p);
    if AreBootstrappableAnyOrder(p, m, PrimeSquareFactorization(m)) and (d_max eq 0 or d le d_max) and
       (m_max eq 0 or Maximum(PrimeSquareFactorization(m)) le m_max) then
        "The parameters p =", p, "and m =", m, "are bootstrappable with d =", d;
    end if;
end for;