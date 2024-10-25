// GBFV - Magma implementation
//--------------------------
load "Crypto/Common.m";
scheme := "BFV";

// The default modulus will be a product of two factors:
// - A number q' that is a power of baseModulus
// - A number q'' such that q' * q'' is approximately equal to q
// Mod switching is done by dividing by baseModulus
baseModulus := 2^10; modPrecision := 2^5;
nbModuli := Floor(Log(baseModulus, q / Maximum(modPrecision, t)));
q_prime := baseModulus ^ nbModuli;
q_double_prime := Floor(q / q_prime);
defaultModulus := q_prime * q_double_prime;
assert nbModuli ge 0;

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
function Encrypt(m, ti, pk: print_result := true)
    q := GetDefaultModulus();
    u := TernaryPol(h);
    return <[ ((u*pk[1] + ErrorPol() + ScaleAndRound(m, q, ti)) mod f) mod q, ((u*pk[2] + ErrorPol()) mod f) mod q ],
              (Category(ti) eq RngIntElt) select ti else ti mod f, q, R!(errorB * n / 2) * (1 + h + can_max)>;
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
    res := ScaleAndRound(EvalC(c, sk), c[2], c[3]);
    return Category(c[2]) eq RngIntElt select res mod c[2] else Flatten(res, c[2]);
end function;

// Print the remaining noise budget of the given ciphertext
procedure PrintNoiseBudget(c: message := "")
    _ := Decrypt(c, 0: print_plaintext := false, message := message);
end procedure;

// Decryption using powerful basis coefficients
// Can do general ciphertexts, not only linear ones
function DecryptPowerful(c, sk)
    coefficients, monomials := CoefficientsAndMonomials(PolynomialToPowerfulBasis((EvalC(c, sk) * c[2]) mod f, factors_m));
    scaling := ScaleAndRoundSequence(coefficients, c[3]);
    res := PowerfulBasisToPolynomial(&+[scaling[index] * monomials[index] : index in [1..#scaling]], factors_m);
    return Category(c[2]) eq RngIntElt select res mod c[2] else Flatten(res, c[2]);
end function;



function CopyCiphertext(ciphertext: print_result := true)
    hash1 := MyHash(ciphertext);
    res := ciphertext; res[1][1] +:= RandPol(2);
    if print_result then
        hash2 := MyHash(res); CreateCiphertext(hash2);
        PrintFile(TRACE, "*" cat hash2 cat " = *" cat hash1 cat ";");
        UseCiphertext(hash1);
    end if;
    return res;
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
    if enableModSwitch then
        AutomaticModSwitchRelin(~cp);
    end if;
end procedure;

// Automatic mod switch before multiplication
// No need to implement this for BFV since there is no major impact on the noise
procedure AutomaticModSwitchMul(~cp)
end procedure;

// Automatic mod switch before relinearization
procedure AutomaticModSwitchRelin(~cp)
    if enableModSwitch then
        if (Sqrt(cp[4]) gt 0) and (1 / Sqrt(cp[4]) ne 0) then
            // Estimate roughly the size of the new modulus
            mod_size := cp[3] * noiseLevelRelin / Sqrt(cp[4]);
            newMod := baseModulus ^ Maximum(Ceiling(Log(baseModulus, mod_size / q_double_prime)), 0) * q_double_prime;

            // Perform actual mod switch
            if newMod ne cp[3] then
                cp := ModSwitch(cp, Minimum(Maximum(newMod, q_double_prime), GetDefaultModulus()));
            end if;
        end if;
    end if;
end procedure;

// Addition with constant
function AddConstant(c, constant)
    return Add(c, <[Zx | ScaleAndRound(constant, c[3], c[2]) mod c[3]], c[2], c[3], R!0>);
end function;

// Compute ciphertext minus constant
function SubCiphertextConstant(c, constant)
    return Sub(c, <[Zx | ScaleAndRound(constant, c[3], c[2]) mod c[3]], c[2], c[3], R!0>);
end function;

// Compute constant minus ciphertext
function SubConstantCiphertext(c, constant)
    return Sub(<[Zx | ScaleAndRound(constant, c[3], c[2]) mod c[3]], c[2], c[3], R!0>, c);
end function;

// Multiplication without relinearization
// c1 and c2 must be degree 1 ciphertexts
function MulNR(c1, c2: print_result := true)
    assert c1[2] eq c2[2];  // Plaintext moduli should be equal
    if IsZero(c1) or IsZero(c2) then
        return GetZeroCiphertext(c1);
    elif IsOne(c1) then
        return c2;
    elif IsOne(c2) then
        return c1;
    end if;
    hash1 := MyHash(c1); hash2 := MyHash(c2);

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
    sigma_2 := (c1[4] + c2[4]) * (n / 12) * (1 + can_max) * SquareSum(c1[2]);

    c31 := ((c1[1][1]*c2[1][1]) mod f);
    if #c1[1] eq 1 and #c2[1] eq 1 then
        res := <[ScaleAndRound(c31, c1[2], c1[3]) mod c1[3]], c1[2], c1[3], sigma_2>;
    elif #c1[1] eq 1 or #c2[1] eq 1 then
        c32 := ((c1[1][#c1[1]]*c2[1][#c2[1]]) mod f);
        res := <[ScaleAndRound(c31, c1[2], c1[3]) mod c1[3], ScaleAndRound(c32, c1[2], c1[3]) mod c1[3]], c1[2], c1[3], sigma_2>;
    else
        c33 := ((c1[1][2]*c2[1][2]) mod f);
        c32 := (((c1[1][1] + c1[1][2])*(c2[1][1] + c2[1][2]) mod f) - c31 - c33); // Computing mul via Karatsuba to save one mul
        res := <[ScaleAndRound(c31, c1[2], c1[3]) mod c1[3], ScaleAndRound(c32, c1[2], c1[3]) mod c1[3],
                 ScaleAndRound(c33, c1[2], c1[3]) mod c1[3]], c1[2], c1[3], sigma_2>;
    end if;
    res := CopyCiphertext(res: print_result := false);

    if print_result then
        hash3 := MyHash(res); CreateCiphertext(hash3);
        if hash1 eq hash2 then
            PrintFile(TRACE, "bootstrapper.squareNR(*" cat hash1 cat ", *" cat
                             hash3 cat ", " cat GetHighLevelBit(res) cat ");");
        else
            PrintFile(TRACE, "bootstrapper.multiplyNR(*" cat hash1 cat ", *" cat hash2 cat ", *" cat
                             hash3 cat ", " cat GetHighLevelBit(res) cat ");");
        end if;
        UseCiphertext(hash1); UseCiphertext(hash2);
    end if;
    return res;
end function;

// Relinearization, degree 2 back to degree 1
function Relin(c, rk: print_result := true)
    if IsZero(c) then
        return GetZeroCiphertext(c);
    end if;
    hash1 := MyHash(c);

    rel, noise := ApplyEncryptedKey(c[1][3], c[3], rk);
    res := CopyCiphertext(<[c[1][1] + rel[1], c[1][2] + rel[2]], c[2], c[3], c[4] + noise>: print_result := false);
    if print_result then
        hash2 := MyHash(res); CreateCiphertext(hash2);
        PrintFile(TRACE, "bootstrapper.relinearize(*" cat hash1 cat ", bk, *" cat
                         hash2 cat ", " cat GetHighLevelBit(res) cat ");");
        UseCiphertext(hash1);
    end if;
    return res;
end function;

// Key switching for automorphisms
function KeySwitch(c, switchKey)
    rel, noise := ApplyEncryptedKey(c[1][2], c[3], switchKey);
    return <[c[1][1] + rel[1], rel[2]], c[2], c[3], c[4] + noise>;
end function;



// Return the error polynomial of the given ciphertext
function CiphertextErrorPol(c, sk)
    return ScaleAndRound(CenteredReduction((c[2] * EvalC(c, sk)) mod f, c[3]), 1, c[2]);
end function;



// Scale and round the given ciphertext over qp/q and scale the plaintext
// modulus over its inverse
function ScaleAndRoundCiphertext(c, qp, q)
    ptxt_mod := ScaleAndRound(c[2], q, qp);
    return <[ScaleAndRound(poly, qp, q) : poly in c[1]], Degree(ptxt_mod) eq 0 select Z!ptxt_mod else ptxt_mod, c[3],
            (SquareSum(qp) / SquareSum(q)) * c[4]>;
end function;

// Given an encryption of a plaintext that is divisible by number, divide
// it by number and decrease the plaintext modulus with the same amount
function ExactDivisionBy(c, number)
    if (Category(c[2]) eq RngIntElt) and (Category(number) eq RngIntElt) then
        c[2] div:= number;
    else
        c[2] := Zx!Eltseq(ToCyclotomicField(c[2]) / ToCyclotomicField(number));
    end if;
    return c;
end function;

// Set the plaintext modulus to the given value
function SetPlaintextModulus(c, modulus)
    return <c[1], modulus, c[3], c[4]>;
end function;

// Compute the homomorphic inner product of the given ciphertext with the given bootstrapping key
function HomomorphicInnerProduct(c, bootKey, additionConstant)
    if IsZero(c) then
        return GetZeroCiphertext(bootKey);
    end if;
    hash1 := MyHash(c);

    henselExponentCiphertext := GetHenselExponent(bootKey);
    c := ModSwitch(c, p ^ henselExponentCiphertext);            // Mod switch to lowest possible modulus
    u := AddConstant(MulConstant(bootKey, c[1][2]: print_result := false), c[1][1]:
                     print_result := false);                    // Homomorphic inner product

    // Replace rounding by flooring for odd p
    res := CopyCiphertext((p eq 2) select AddConstant(u, additionConstant: print_result := false) else u:
                          print_result := false);
    hash2 := MyHash(res); CreateCiphertext(hash2);
    PrintFile(TRACE, "bootstrapper.homomorphic_noisy_decrypt(*" cat hash1 cat ", bk, *" cat hash2 cat ");");
    UseCiphertext(hash1);
    return res;
end function;