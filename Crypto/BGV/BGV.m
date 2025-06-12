// BGV - Magma implementation
//--------------------------
load "Crypto/Common.m";
scheme := "BGV";

/*****
 * Remark: the public key, relinearization key and switch keys are
 * generated with respect to the default plaintext modulus t. This
 * adds some extra noise when working with a divisor of t, but it
 * avoids the need to generate separate keys for bootstrapping.
 *****/

// The default modulus will be a product of two factors:
// - A number q' that is a power of baseModulus
// - A number q'' such that q' * q'' is approximately equal to q
// Mod switching is done by dividing by baseModulus
baseModulus := t + 1; modPrecision := 2^5;
nbModuli := Floor(Log(baseModulus, q / t / modPrecision));
q_prime := baseModulus ^ nbModuli;
q_double_prime := Floor((q / q_prime - 1) / t) * t + 1;
defaultModulus := q_prime * q_double_prime;
assert nbModuli ge 0;

// Return the default ciphertext modulus of a freshly encrypted plaintext
function GetDefaultModulus()
    return defaultModulus;
end function;



// Key pair generation
// sk: ternary pol with hamming weight h
// pk: (a*s + t*e, -a) with a random and e an errorpol
function GenKeyPair()
    q := GetDefaultModulus();
    a := RandPol(q);
    e := ErrorPol();
    s := TernaryPol(h);

    return s, [((a*s + t*e) mod f) mod q, -a mod q];
end function;

// Encryption, message is a polynomial mod ti, pk is public key
// The encrypted message is of the form <[c0, c1, ...], ti, qi, noise> where [c0, c1, ...] is
// the ciphertext, ti is the plaintext modulus, qi is the current ciphertext modulus and noise
// is the current noise estimate
function Encrypt(m, ti, pk)
    assert IsDivisibleBy(t, ti);        // Check that r in 'Crypto/Params.m' is high enough

    q := GetDefaultModulus();
    u := TernaryPol(h);
    return <[ ((u*pk[1] + ti*ErrorPol() + m) mod f) mod q, ((u*pk[2] + ti*ErrorPol()) mod f) mod q ], ti, q,
              R!((t / ti) ^ 2) * (errorB * n / 2) * (1 + h + can_max)>;
end function;

// Generate encryption of the given key
// Can be used for relinearisation/key switching init
function GenEncryptedKey(sk, key)
    q := GetDefaultModulus();
    enc := [];
    for i := 0 to L-1 do
        a := RandPol(q);
        e := ErrorPol();
        Append(~enc, [((a*sk + t*e + w^i*key) mod f) mod q, -a mod q]);
    end for;
    
    return enc;
end function;

// Decryption, can do general ciphertexts, not only linear ones
function Decrypt(c, sk)
    return CenteredReduction(EvalC(c, sk), c[3]) mod c[2];
end function;

// Decryption using powerful basis coefficients
// Can do general ciphertexts, not only linear ones
function DecryptPowerful(c, sk)
    coefficients, monomials := CoefficientsAndMonomials(PolynomialToPowerfulBasis(EvalC(c, sk), factors_m));
    reduction := CenteredReductionSequence(CenteredReductionSequence(coefficients, c[3]), c[2]);
    return PowerfulBasisToPolynomial(&+[reduction[index] * monomials[index] : index in [1..#reduction]], factors_m) mod c[2];
end function;



// Mod switch ciphertext to qp
// If you want to reuse rlk, you should always switch to a divisor of the current modulus
// Noise estimate is only valid for linear ciphertexts
function ModSwitch(cp, qp)
    assert qp mod cp[2] eq 1;           // We only support moduli of this shape

    // Perform mod switching in two steps: up + down
    max_mod := LCM(cp[3], qp);
    factor_up := max_mod div cp[3];
    factor_down := max_mod div qp;

    // Perform both steps of the mod switching
    res_up := [cp[1][index] * factor_up : index in [1..#cp[1]]];                                    // Step 1
    inv := Modinv(cp[2], factor_down);
    delta := [cp[2] * CenteredReduction(-element * inv, factor_down) : element in res_up];
    res_down := [((res_up[index] + delta[index]) div factor_down) mod qp : index in [1..#res_up]];  // Step 2

    return <res_down, cp[2], qp, ((qp / cp[3]) ^ 2) * cp[4] + (n / 12) * (can_max + 1)>;
end function;

// Perform modulus switching for efficiency reasons
// --> Just make sure that the noise is always above the relin level
procedure DynamicModSwitch(~cp)
    AutomaticModSwitchRelin(~cp);
end procedure;

// Automatic mod switch before multiplication
procedure AutomaticModSwitchMul(~cp)
    assert IsDivisibleBy(t, cp[2]);     // Check that r in 'Crypto/Params.m' is high enough

    if (Sqrt(cp[4]) gt 0) and (1 / Sqrt(cp[4]) ne 0) then
        // Estimate roughly the size of the new modulus
        mod_size := cp[3] * noiseLevelMul / Sqrt(cp[4]);
        fact1 := baseModulus ^ Maximum(Floor(Log(baseModulus, mod_size / cp[2] / modPrecision)), 0);
        fact2 := Round((mod_size / fact1 - 1) / cp[2]) * cp[2] + 1;
        newMod := fact1 * fact2;
        
        // Perform actual mod switch
        if newMod ne cp[3] then
            cp := ModSwitch(cp, Minimum(Maximum(newMod, q_double_prime), GetDefaultModulus()));
        end if;
    end if;
end procedure;

// Automatic mod switch before relinearization
procedure AutomaticModSwitchRelin(~cp)
    assert IsDivisibleBy(t, cp[2]);     // Check that r in 'Crypto/Params.m' is high enough

    if (Sqrt(cp[4]) gt 0) and (1 / Sqrt(cp[4]) ne 0) then
        // Estimate roughly the size of the new modulus
        mod_size := cp[3] * (t / cp[2]) * noiseLevelRelin / Sqrt(cp[4]);
        newMod := baseModulus ^ Maximum(Ceiling(Log(baseModulus, mod_size / q_double_prime)), 0) * q_double_prime;

        // Perform actual mod switch
        if newMod ne cp[3] then
            cp := ModSwitch(cp, Minimum(Maximum(newMod, q_double_prime), GetDefaultModulus()));
        end if;
    end if;
end procedure;

// Addition with constant
function AddConstant(c, constant)
    return Add(c, <[Zx | CenteredReduction(constant mod f, c[2]) mod c[3]], c[2], c[3], R!0>);
end function;

// Compute ciphertext minus constant
function SubCiphertextConstant(c, constant)
    return Sub(c, <[Zx | CenteredReduction(constant mod f, c[2]) mod c[3]], c[2], c[3], R!0>);
end function;

// Compute constant minus ciphertext
function SubConstantCiphertext(c, constant)
    return Sub(<[Zx | CenteredReduction(constant mod f, c[2]) mod c[3]], c[2], c[3], R!0>, c);
end function;

// Multiplication without relinearization
// c1 and c2 must be degree 1 ciphertexts
function MulNR(c1, c2)
    assert c1[2] eq c2[2];  // Plaintext moduli should be equal

    // Ciphertexts should have same modulus
    ModSwitchLowestModulus(~c1, ~c2);

    // New noise
    sigma_2 := (c1[2] ^ 2) * c1[4] * c2[4];

    c31 := ((c1[1][1]*c2[1][1]) mod f);
    if #c1[1] eq 1 and #c2[1] eq 1 then
        return <[c31 mod c1[3]], c1[2], c1[3], sigma_2>;
    elif #c1[1] eq 1 or #c2[1] eq 1 then
        c32 := ((c1[1][#c1[1]]*c2[1][#c2[1]]) mod f);
        return <[c31 mod c1[3], c32 mod c1[3]], c1[2], c1[3], sigma_2>;
    else
        c33 := ((c1[1][2]*c2[1][2]) mod f);
        c32 := (((c1[1][1] + c1[1][2])*(c2[1][1] + c2[1][2]) mod f) - c31 - c33); // Computing mul via Karatsuba to save one mul
        return <[c31 mod c1[3], c32 mod c1[3], c33 mod c1[3]], c1[2], c1[3], sigma_2>;
    end if;
end function;

// Relinearization, degree 2 back to degree 1
function Relin(c, rk)
    assert IsDivisibleBy(t, c[2]);      // Check that r in 'Crypto/Params.m' is high enough

    rel, noise := ApplyEncryptedKey(c[1][3], c[3], rk);
    return <[c[1][1] + rel[1], c[1][2] + rel[2]], c[2], c[3], c[4] + ((t / c[2]) ^ 2) * noise>;
end function;

// Key switching for automorphisms
function KeySwitch(c, switchKey)
    assert IsDivisibleBy(t, c[2]);      // Check that r in 'Crypto/Params.m' is high enough

    rel, noise := ApplyEncryptedKey(c[1][2], c[3], switchKey);
    return <[c[1][1] + rel[1], rel[2]], c[2], c[3], c[4] + ((t / c[2]) ^ 2) * noise>;
end function;



// Return the error polynomial of the given ciphertext
function CiphertextErrorPol(c, sk)
    return CenteredReduction(EvalC(c, sk), c[3]) div c[2];
end function;



// Given an encryption of a plaintext that is divisible by number, divide
// it by number and decrease the plaintext modulus with the same amount
function ExactDivisionBy(c, number)
    multiplier := Modinv(number, c[3]);
    return <[(multiplier * element) mod c[3] : element in c[1]], c[2] div number, c[3], c[4]>;
end function;

// Compute the homomorphic inner product of the given ciphertext with the given bootstrapping key
function HomomorphicInnerProduct(c, bootKey, additionConstant)
    henselExponentCiphertext := GetHenselExponent(bootKey); henselExponentPlaintext := GetHenselExponent(c);
    new_modulus := Ceiling(c[3] / (p ^ henselExponentCiphertext)) * (p ^ henselExponentCiphertext) + 1;
    p_to_the_v := p ^ (henselExponentCiphertext - henselExponentPlaintext);

    // The actual computation
    c := ModSwitch(c, new_modulus);   // Mod switch to an appropriate modulus of roughly the same size
    u := AddConstant(MulConstant(bootKey, CenteredReduction(p_to_the_v * c[1][2], new_modulus)),
                                          CenteredReduction(p_to_the_v * c[1][1], new_modulus));   // Homomorphic inner product

    // Replace rounding by flooring for odd p
    return (p eq 2) select AddConstant(u, additionConstant) else u;
end function;