// BFV - Magma implementation
// Code based upon an earlier version written by Frederik Vercauteren
//--------------------------
load "Crypto/Common.m";
scheme := "BFV";

// The default modulus will be a product of two factors:
// - A number q' that is a power of baseModulus
// - A number q'' such that q' * q'' is approximately equal to q
// Mod switching is done by dividing by baseModulus
baseModulus := 2 ^ 10;
nbModuli := Floor(Log(baseModulus, q / Maximum(modPrecision, t)));
q_prime := baseModulus ^ nbModuli;
q_double_prime := Floor(q / q_prime);
defaultModulus := q_prime * q_double_prime;

// Return the default ciphertext modulus of a freshly encrypted plaintext
function GetDefaultModulus()
    return defaultModulus;
end function;



// Key pair generation
// sk: ternary pol with hamming weight h
// pk: (a*s + e, -a) with a random and e an errorpol
function GenKeyPair()
    q := GetDefaultModulus();
    a := RandPol(q);
    e := ErrorPol();
    s := TernaryPol(h);

    return s, [((a*s + e) mod f) mod q, -a mod q];
end function;

// Encryption, message is a polynomial mod ti, pk is public key
// The encrypted message is of the form <[c0, c1, ...], ti, qi, noise> where [c0, c1, ...] is
// the ciphertext, ti is the plaintext modulus, qi is the current ciphertext modulus and noise
// is the current noise estimate
function Encrypt(m, ti, pk)
    q := GetDefaultModulus();
    u := TernaryPol(h);
    return <[ ((u*pk[1] + ErrorPol() + (q div ti)*m) mod f) mod q, ((u*pk[2] + ErrorPol()) mod f) mod q ], ti, q,
              R!(errorB * n / 2) * (1 + h + can_max)>;
end function;

// Generate encryption of the given key
// Can be used for relinearisation/key switching init
function GenEncryptedKey(sk, key)
    q := GetDefaultModulus();
    enc := [];
    for i := 0 to L-1 do
        a := RandPol(q);
        e := ErrorPol();
        Append(~enc, [((a*sk + e + w^i*key) mod f) mod q, -a mod q]);
    end for;
    
    return enc;
end function;

// Decryption, can do general ciphertexts, not only linear ones
function Decrypt(c, sk)
    return ScaleAndRound(EvalC(c, sk), c[2], c[3]) mod c[2];
end function;

// Decryption using powerful basis coefficients
// Can do general ciphertexts, not only linear ones
function DecryptPowerful(c, sk)
    coefficients, monomials := CoefficientsAndMonomials(PolynomialToPowerfulBasis(EvalC(c, sk), factors_m));
    scaling := ScaleAndRoundSequence(coefficients, c[2], c[3]);
    return PowerfulBasisToPolynomial(&+[scaling[index] * monomials[index] : index in [1..#scaling]], factors_m) mod c[2];
end function;



// Mod switch ciphertext to qp
// If you want to reuse rlk, you should always switch to a divisor of the current modulus
// Noise estimate is only valid for linear ciphertexts
function ModSwitch(cp, qp)
    res := [ScaleAndRound(cpi, qp, cp[3]) : cpi in cp[1]];
    return <res, cp[2], qp, ((qp / cp[3]) ^ 2) * cp[4] + (n / 12) * (can_max + 1)>;
end function;

// Perform modulus switching for efficiency reasons
// --> Just make sure that the noise is always above the relin level
procedure DynamicModSwitch(~cp)
    AutomaticModSwitchRelin(~cp);
end procedure;

// Automatic mod switch before multiplication
// No need to implement this for BFV since there is no major impact on the noise
procedure AutomaticModSwitchMul(~cp)
end procedure;

// Automatic mod switch before relinearization
procedure AutomaticModSwitchRelin(~cp)
    if Sqrt(cp[4]) gt 0 then
        // Estimate roughly the size of the new modulus
        mod_size := cp[3] * noiseLevelRelin / Sqrt(cp[4]);
        newMod := baseModulus ^ Maximum(Ceiling(Log(baseModulus, mod_size / q_double_prime)), 0) * q_double_prime;

        // Perform actual mod switch
        if newMod ne cp[3] then
            cp := ModSwitch(cp, Minimum(Maximum(newMod, q_double_prime), GetDefaultModulus()));
        end if;
    end if;
end procedure;

// Addition with constant
function AddConstant(c, constant)
    return Add(c, <[Zx | ((c[3] div c[2]) * CenteredReduction(constant, c[2])) mod c[3]], c[2], c[3], R!0>);
end function;

// Compute ciphertext minus constant
function SubCiphertextConstant(c, constant)
    return Sub(c, <[Zx | ((c[3] div c[2]) * CenteredReduction(constant, c[2])) mod c[3]], c[2], c[3], R!0>);
end function;

// Compute constant minus ciphertext
function SubConstantCiphertext(c, constant)
    return Sub(<[Zx | ((c[3] div c[2]) * CenteredReduction(constant, c[2])) mod c[3]], c[2], c[3], R!0>, c);
end function;

// Multiplication without relinearization
// c1 and c2 must be degree 1 ciphertexts
function MulNR(c1, c2)
    assert c1[2] eq c2[2];  // Plaintext moduli should be equal

    // Ciphertexts should have same modulus
    ModSwitchLowestModulus(~c1, ~c2);

    // Important for multiplication to do centered reduction
    for i := 1 to #c1[1] do
        c1[1][i] := CenteredReduction(c1[1][i], c1[3]);
    end for;
    for i := 1 to #c2[1] do
        c2[1][i] := CenteredReduction(c2[1][i], c2[3]);
    end for;

    // New noise
    sigma_2 := ((c1[4] + c2[4]) * ((c1[3] ^ 2) * n / 12) * (1 + can_max)) / ((c1[3] / c1[2]) ^ 2);

    c31 := ((c1[1][1]*c2[1][1]) mod f);
    if #c1[1] eq 1 and #c2[1] eq 1 then
        return <[ScaleAndRound(c31, c1[2], c1[3]) mod c1[3]], c1[2], c1[3], sigma_2>;
    elif #c1[1] eq 1 or #c2[1] eq 1 then
        c32 := ((c1[1][#c1[1]]*c2[1][#c2[1]]) mod f);
        return <[ScaleAndRound(c31, c1[2], c1[3]) mod c1[3], ScaleAndRound(c32, c1[2], c1[3]) mod c1[3]], c1[2], c1[3], sigma_2>;
    else
        c33 := ((c1[1][2]*c2[1][2]) mod f);
        c32 := (((c1[1][1] + c1[1][2])*(c2[1][1] + c2[1][2]) mod f) - c31 - c33); // Computing mul via karatsuba to save one mul
        return <[ScaleAndRound(c31, c1[2], c1[3]) mod c1[3], ScaleAndRound(c32, c1[2], c1[3]) mod c1[3],
                 ScaleAndRound(c33, c1[2], c1[3]) mod c1[3]], c1[2], c1[3], sigma_2>;
    end if;
end function;

// Relinearization, degree 2 back to degree 1
function Relin(c, rk)
    rel, noise := ApplyEncryptedKey(c[1][3], c[3], rk);
    return <[c[1][1] + rel[1], c[1][2] + rel[2]], c[2], c[3], c[4] + noise>;
end function;

// Key switching for automorphisms
function KeySwitch(c, switchKey)
    rel, noise := ApplyEncryptedKey(c[1][2], c[3], switchKey);
    return <[c[1][1] + rel[1], rel[2]], c[2], c[3], c[4] + noise>;
end function;



// Return the error polynomial of the given ciphertext
function CiphertextErrorPol(c, sk)
    return Zx![el div c[2] : el in Eltseq(CenteredReduction(c[2] * EvalC(c, sk), c[3]))];
end function;



// Given an encryption of a plaintext that is divisible by number, divide
// it by number and decrease the plaintext modulus with the same amount
function ExactDivisionBy(c, number)
    c[2] div:= number;
    return c;
end function;

// Compute the homomorphic inner product of the given ciphertext with the given bootstrapping key
function HomomorphicInnerProduct(c, bootKey, additionConstant)
    henselExponentCiphertext := GetHenselExponent(bootKey);
    c := ModSwitch(c, p ^ henselExponentCiphertext);            // Mod switch to lowest possible modulus
    u := AddConstant(MulConstant(bootKey, c[1][2]), c[1][1]);   // Homomorphic inner product

    // Replace rounding by flooring for odd p
    return (p eq 2) select AddConstant(u, additionConstant) else u;
end function;