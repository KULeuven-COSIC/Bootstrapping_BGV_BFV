// Find parameters that are easily bootstrappable in the HElib implementation
// This means that
// 1) The parameter m should factor into smaller prime powers
// 2) The parameter p should be small
// 3) The parameter d should be small
// This file does not check q and sigma, so the security level should be obtained
// with the lattice estimator
load "Crypto/General.m";
load "Crypto/Hypercube_structure.m";

// Find all bootstrappable parameters in a given range
n_min := 2^15;          // Determines security level (together with ciphertext modulus)
n_max := 2^16;
m_max := 2^20;
d_max := 5;             // Determines number of slots (equal to n / d)
p_max := 100;           // Determines polynomial degree of digit removal
m_factor_max := 250;    // Determines complexity of linear transformations

// Brute force search to check whether constraints are satisfied
primes := [p : p in [2..p_max] | IsPrime(p)];
for m := n_min to m_max do
    n := EulerPhi(m);
    if (n lt n_min) or (n gt n_max) then
        continue;
    end if;

    for p in primes do
        if GCD(m, p) ne 1 then
            continue;
        end if;

        // Check restrictions
        d := Order(Integers(m)!p);
        if ((d le d_max) and (Maximum(PrimePowerFactorization(m)) le m_factor_max)) then
            //if AreBootstrappableAnyOrder(p, m, PrimePowerFactorization(m)) then  // Checks HElib bootstrappable requirements
                "p =", p, "\t  n =", n, "\td =", d, "\t  m =", m, "\t", Factorization(m);
            //end if;
        end if;
    end for;
end for;