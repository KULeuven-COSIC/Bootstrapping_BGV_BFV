// Common functionality for the BGV and BFV scheme
//--------------------------
load "Crypto/General.m";
load "Arithmetic/FFT.m";
load "Arithmetic/Powerful.m";
load "Crypto/Hypercube_structure.m";

/*****
 Forward declarations for scheme-specific functionality
 *****/
forward GetDefaultModulus;
forward GenKeyPair;
forward Encrypt;
forward GenEncryptedKey;
forward Decrypt;
forward DecryptPowerful;
forward ModSwitch;
forward DynamicModSwitch;
forward AutomaticModSwitchMul;
forward AutomaticModSwitchRelin;
forward AddConstant;
forward SubCiphertextConstant;
forward SubConstantCiphertext;
forward MulNR;
forward Relin;
forward KeySwitch;
forward CiphertextErrorPol;
forward ExactDivisionBy;
forward HomomorphicInnerProduct;
forward CopyCiphertext;



// Check whether the given variable is a ciphertext
function IsCiphertext(c)
    return Category(c) eq Tup;
end function;

// Return a new ciphertext that encrypts the constant 0
function GetZeroCiphertext(c)
    q := GetDefaultModulus();
    if (Category(c) eq RngIntElt) or (Category(c) eq RngUPolElt) then
        return <[Zx | 0], c, q, R!0>;
    else
        return <[Zx | 0], c[2], q, R!0>;
    end if;
end function;

// Return the plaintext Hensel exponent of the given ciphertext
function GetHenselExponent(c)
    if Category(c[2]) ne RngIntElt then
        error "This function does not accept GBFV ciphertexts.";
    end if;
    return Round(Log(p, c[2]));
end function;

// Return the number of ciphertext parts
function GetNbParts(c)
    return #c[1];
end function;

// Evaluate ciphertext in secret key
// Can do general ciphertexts, not only linear ones
function EvalC(c, sk)
    cp := c[1][1];
    ski := sk;
    for i := 2 to #c[1] do
        cp +:= (((c[1][i] * ski) mod f) mod c[3]);
        if (i lt #c[1]) then
            ski := ((ski * sk) mod f);    // Coefficients are small so no mod q reduction
        end if;
    end for;
    return cp;
end function;

// Apply the encryption of the given key to a ciphertext part
// Return a sequence of two new ciphertext parts and the added noise
// Can be used for relinearisation/key switching
function ApplyEncryptedKey(c, qi, key)
    // Split c into base w, and multiply correct parts with key
    res := [Zx | 0 : i in [1..2]];      // Result

    i := 1;                             // Iteration
    c := CenteredReduction(c, qi);      // Ensure that last iteration is also a small number
    while c ne 0 do
        if i eq #key then
            cpart := c;                 // Last iteration only: make sure we have added full ciphertext
        else
            cpart := CenteredReduction(c, w);
        end if;

        // Update result
        res[1] +:= cpart*key[i][1];
        res[2] +:= cpart*key[i][2];
        
        // Update variables for next iteration
        c := (c - cpart) div w;
        i +:= 1;
    end while;
    
    // Modular reduction
    res[1] := (res[1] mod f) mod qi;
    res[2] := (res[2] mod f) mod qi;
    
    return res, ((w ^ 2) * n / 12) * (i - 1) * (errorB * n / 2);
end function;

// Mod switch c1 and c2 to the same modulus (the lowest one of the two)
procedure ModSwitchLowestModulus(~c1, ~c2)
    if c1[3] lt c2[3] then
        c2 := ModSwitch(c2, c1[3]);
    elif c2[3] lt c1[3] then
        c1 := ModSwitch(c1, c2[3]);
    end if;
end procedure;

// Pad zeros to the shortest ciphertext
procedure PadZeros(~c1, ~c2)
    c1[1] := CatZeros(c1[1], #c2[1]);
    c2[1] := CatZeros(c2[1], #c1[1]);
end procedure;



function GetPlaintextModulus(ciphertext)
    return ciphertext[2];
end function;

function IsHighLevel(ciphertext)
    return (GetPlaintextModulus(ciphertext) eq p ^ e) or
           (ToCyclotomicField(GetPlaintextModulus(ciphertext)) eq common_moduli[e]);
end function;

function GetHighLevelBit(ciphertext)
    return IsHighLevel(ciphertext) select "1" else "0";
end function;

function IsGBFVCiphertext(ciphertext)
    return Category(GetPlaintextModulus(ciphertext)) ne RngIntElt;
end function;



SetAutoColumns(false);
SetColumns(0);

load "Traces/Hash.m";
load "Traces/Helpers.m";



// Addition
function Add(c1, c2: print_result := true)
    assert c1[2] eq c2[2];  // Plaintext moduli should be equal
    if IsZero(c1) then
        return c2;
    elif IsZero(c2) then
        return c1;
    end if;
    hash1 := MyHash(c1); hash2 := MyHash(c2);

    // Ciphertexts should have same modulus and degree
    ModSwitchLowestModulus(~c1, ~c2);
    PadZeros(~c1, ~c2);
    res := CopyCiphertext(<[(c1[1][i] + c2[1][i]) mod c1[3] : i in [1..#c1[1]]], c1[2], c1[3], c1[4] + c2[4]>:
                          print_result := false);
    if print_result then
        hash3 := MyHash(res); CreateCiphertext(hash3);
        PrintFile(TRACE, "bootstrapper.add(*" cat hash1 cat ", *" cat hash2 cat ", *" cat
                         hash3 cat ", " cat GetHighLevelBit(res) cat ");");
        UseCiphertext(hash1); UseCiphertext(hash2);
    end if;
    return res;
end function;

// Subtraction
function Sub(c1, c2: print_result := true)
    assert c1[2] eq c2[2];  // Plaintext moduli should be equal
    if IsZero(c2) then
        return c1;
    end if;
    hash1 := MyHash(c1); hash2 := MyHash(c2);

    // Ciphertexts should have same modulus and degree
    ModSwitchLowestModulus(~c1, ~c2);
    PadZeros(~c1, ~c2);
    res := CopyCiphertext(<[(c1[1][i] - c2[1][i]) mod c1[3] : i in [1..#c1[1]]], c1[2], c1[3], c1[4] + c2[4]>:
                          print_result := false);
    if print_result then
        hash3 := MyHash(res); CreateCiphertext(hash3);
        PrintFile(TRACE, "bootstrapper.sub(*" cat hash1 cat ", *" cat hash2 cat ", *" cat
                         hash3 cat ", " cat GetHighLevelBit(res) cat ");");
        UseCiphertext(hash1); UseCiphertext(hash2);
    end if;
    return res;
end function;

// Multiplication with relinearization
function Mul(c1, c2, rk)
    if IsZero(c1) or IsZero(c2) then
        return GetZeroCiphertext(c1);
    elif IsOne(c1) then
        return c2;
    elif IsOne(c2) then
        return c1;
    end if;
    hash1 := MyHash(c1); hash2 := MyHash(c2);

    // Ensure that noise doesn't grow exponentially in multiplicative depth
    AutomaticModSwitchMul(~c1);
    AutomaticModSwitchMul(~c2);

    // Perform the multiplication and relinearization
    mul := MulNR(c1, c2: print_result := false);
    if #mul[1] eq 3 then
        AutomaticModSwitchRelin(~mul);
        mul := Relin(mul, rk: print_result := false);
    end if;

    // Decrease current modulus for efficiency reasons
    DynamicModSwitch(~mul);
    res := CopyCiphertext(mul: print_result := false);
    hash3 := MyHash(res); CreateCiphertext(hash3);
    if hash1 eq hash2 then
        PrintFile(TRACE, "bootstrapper." cat (IsGBFVCiphertext(c1) select "gbfv_" else "") cat "square(*" cat hash1 cat
                         ", bk, *" cat hash3 cat ", " cat (IsGBFVCiphertext(c1) select (IntegerToString(gbfvExponent) cat ", " cat
                         IntegerToString(gbfvCoefficient) cat ", ") else "") cat GetHighLevelBit(res) cat ");");
    else
        PrintFile(TRACE, "bootstrapper." cat (IsGBFVCiphertext(c1) select "gbfv_" else "") cat "multiply(*" cat hash1 cat
                         ", *" cat hash2 cat ", bk, *" cat hash3 cat ", " cat (IsGBFVCiphertext(c1) select
                         (IntegerToString(gbfvExponent) cat ", " cat IntegerToString(gbfvCoefficient) cat ", ") else "") cat
                         GetHighLevelBit(res) cat ");");
    end if;
    UseCiphertext(hash1); UseCiphertext(hash2);
    return res;
end function;

// Multiplication with constant
function MulConstant(c, constant: print_result := true)
    constant := Flatten(constant, GetPlaintextModulus(c));
    if IsZero(c) or IsZero(constant) then
        return GetZeroCiphertext(c);
    elif IsOne(constant) then
        return c;
    end if;
    hash1 := MyHash(c);

    mul := <[((constant * cPart) mod f) mod c[3] : cPart in c[1]], c[2], c[3], SquareSum(constant) * c[4]>;

    // Decrease current modulus for efficiency reasons
    DynamicModSwitch(~mul);
    res := CopyCiphertext(mul: print_result := false);
    if print_result then
        hash2 := RandomHash(); hash3 := MyHash(res); CreateCiphertext(hash3);
        PrintFile(TRACE, "bootstrapper.multiply_plain(*" cat hash1 cat ", " cat hash2 cat ", *" cat
                         hash3 cat ", " cat GetHighLevelBit(res) cat ");");
        SEAL_modulus := IsHighLevel(res) select p ^ 2 else p; seq := Eltseq(constant mod SEAL_modulus);
        if ((&+[el eq 0 select 0 else 1 : el in seq]) eq 1) and ((&+seq) gt (SEAL_modulus div 2)) then
            PrintFile(TRACE, "bootstrapper.negate_inplace(*" cat hash3 cat ", " cat GetHighLevelBit(res) cat ");");
            UsePlaintextOptimalDomain(hash2, (-constant) mod SEAL_modulus, IsHighLevel(res));
        else
            UsePlaintextOptimalDomain(hash2, constant mod SEAL_modulus, IsHighLevel(res));
        end if;
        UseCiphertext(hash1);
    end if;
    return res;
end function;

// Relin key init
function GenRelinKey(sk)
    sk2 := sk^2 mod f;
    return GenEncryptedKey(sk, sk2);
end function;



// Max norm of the error in the coefficient embedding
// The error is normalized to the standard modulus q
function ErrorC(c, sk)
    return R!(Log(2, (q / c[3]) * MaximumOrOne([Abs(coeff) : coeff in Eltseq(CiphertextErrorPol(c, sk))])));
end function;

// Max norm of the error in the canonical embedding
// The error is normalized to the standard modulus q
function ErrorCanC(c, sk)
    return R!(Log(2, (q / c[3]) * MaximumOrOne(GetMaxModulus(CiphertextErrorPol(c, sk)))));
end function;

// Estimated error of the given ciphertext
// The error is normalized to the standard modulus q
function EstimatedErrorCanC(c)
    return R!(Log(2, MaximumOrOne(q * Sqrt(c[4]) / c[3])));
end function;



// The code from here on is only executed if there is a valid hypercube structure
if (GCD(m, p) eq 1) and IsPrime(p) then

// Return the number of dimensions
function GetNbDimensions()
    return #S;
end function;

// Return the size of the given dimension
function GetDimensionSize(dim)
    return orders[dim][2];
end function;

// Check whether the given dimension is a good dimension
function IsGoodDimension(dim)
    return orders[dim][1] eq orders[dim][2];
end function;

// Get a one-dimensional hypercube index in the given dimension and
// with pos positions
function Get1DHyperIndex(dim, pos)
    return [var eq dim select pos else 0 : var in [1..GetNbDimensions()]];
end function;

// Convert the given index to a hypercube index
function IndexToHypercube(index)
    return IndexToSequence(index, [GetDimensionSize(dim) : dim in [1..GetNbDimensions()]]);
end function;

// Convert the given hypercube index to a regular index
function HypercubeToIndex(hyperIndex)
    return SequenceToIndex(hyperIndex, [GetDimensionSize(dim) : dim in [1..GetNbDimensions()]]);
end function;

// Get the representative of (Z/mZ)*/<p> based on the set S and the given (hypercube) index
function GetHypercubeRepresentative(index)
    if Category(index) eq RngIntElt then
        index := IndexToHypercube(index);
    end if;

    // Exponentiate elements of S and multiply together
    result := Zm!1;
    for i := 1 to #index do
        result *:= ((Zm!(S[i])) ^ index[i]);
    end for;
    return Z!result;
end function;

// Get the inverse representative of (Z/mZ)*/<p> based on the set S and the given (hypercube) index
function GetInverseHypercubeRepresentative(index)
    return Modinv(GetHypercubeRepresentative(index), m);
end function;

// Get the sequence of factors of f mod t
// Factor F_i corresponds to GCD(F_1(x^k), f) with k the inverse of the i'th element of S
function GetSlotFactors()
    // Construct polynomial ring over Galois field
    Fp := GF(p);
    Fp_poly := PolynomialRing(Fp);

    // Get cyclotomic polynomial mod p
    fp := Fp_poly!f;
    Ffp<y> := quo<Fp_poly | fp>;

    // Random first factor
    F1 := Factorization(fp)[1][1];

    // Different way of deriving other factors than in HElib design document
    // --> Ensure that implementation is consistent with powerful basis representation
    factors := [F1];
    for index := 2 to l do
        exp := GetInverseHypercubeRepresentative(index);
        Append(~factors, GCD(Fp_poly!(Evaluate(F1, y ^ exp)), fp));
    end for;

    return [Zt_poly | factor : factor in HenselLift(f, factors, Zt_poly)];
end function;

// Return the first slot factor
factors := GetSlotFactors();
function GetFirstSlotFactor()
    return Zx!factors[1];
end function;

// Return normal element used for packing
normalElement := Zx!Eltseq(NormalElement(ext<GF(p) | GetFirstSlotFactor()>));
function GetNormalElement()
    return normalElement;
end function;

// Return the slot algebra (the ring structure that is present on the slots)
function GetSlotAlgebra(henselExponent)
    assert henselExponent le e;

    Zt := Integers(p ^ henselExponent);
    Zt_poly := PolynomialRing(Zt);
    return quo<Zt_poly | GetFirstSlotFactor()>;
end function;



// Precomputed data for applying the inverse CRT
function RecombPoly()
    recombPolyLarge := [Zx | ];
    recombPolySmall := [Zx | ];

    for slot := 1 to l do
        // Construct ring modulo the factor of the current slot
        Zt_slot := quo<Zt_poly | factors[slot]>;
        factExceptCurrent := Remove(factors, slot);         // Exclude current factor

        // Store product and inverse
        prod := &*factExceptCurrent;
        prod_slot := Zt_slot!prod;
        Append(~recombPolyLarge, prod);                     // Product of all factors except the current one
        Append(~recombPolySmall, prod_slot ^ (-1));         // Inverse of product mod the current factor
    end for;

    return recombPolyLarge, recombPolySmall;
end function;

// Get the plaintext part at the given (hypercube) index
function GetFromSlot(plaintext, index: henselExponent := e)
    assert henselExponent le e;

    if Category(index) ne RngIntElt then
        index := HypercubeToIndex(index);
    end if;

    // Construct ring modulo the factor of the first slot
    Zt_F1<y> := GetSlotAlgebra(henselExponent);
    slotRepresentation := Zx!(plaintext mod factors[index]);
    return Zx!Evaluate(slotRepresentation, y ^ GetHypercubeRepresentative(index));
end function;

// Convert each plaintext part to the power basis of x ^ h where h is its hypercube representative
y_powers := [Zt_poly | (quo<Zt_poly | factors[slot]>.1) ^ GetInverseHypercubeRepresentative(slot) : slot in [1..l]];
function GetSlotRepresentation(parts, henselExponent)
    slotRepresentation := [Zx | ];
    for slot := 1 to l do
        Zt_slot<y> := quo<Zt_poly | factors[slot]>;
        Append(~slotRepresentation, Evaluate(Zx!parts[slot], Zt_slot!y_powers[slot]));
    end for;
    return [Zx | el mod (p ^ henselExponent) : el in slotRepresentation];
end function;

assert (not useFFTBatchEncoder) or IsPowerOfTwo(m);
if useFFTBatchEncoder then

// Precomputation for FFT-based batch encoder
function PrecompBatchEncoder(m, generating_poly)
    rootFFTBatcher, generating_poly, root_in_base_ring := ComputeBluesteinRoot(m, p, e, generating_poly);
    fft_ring := quo<Zt_poly | generating_poly>;                             // Ring for FFT algorithm
    precomp_batcher := PrecompBluestein(m, fft_ring: W := Evaluate(rootFFTBatcher, fft_ring.1));
    batcher_info := [<GCD(i, m) eq 1, 0, fft_ring!0> : i in [0..m - 1]];    // Store batcher info
    for slot := 1 to l do
        hyper_rep := GetHypercubeRepresentative(slot);
        for exp := 0 to Order(Integers(m)!p) - 1 do
            pow := Z!((Integers(m)!p) ^ exp); ind := ((hyper_rep * pow) mod m) + 1;
            batcher_info[ind][2] := slot; batcher_info[ind][3] := (Evaluate(rootFFTBatcher, fft_ring.1) ^ 2) ^ (ind - 1);
        end for;
    end for;
    return precomp_batcher, batcher_info, root_in_base_ring;
end function;
decimation_factor := (p mod 4 eq 1) select d else d div 2; m_prime := m div decimation_factor;
precomp_batcher, batcher_info, root_in_base_ring := PrecompBatchEncoder(m_prime, DecimatePolynomial(GetFirstSlotFactor(),
                                                                                                    decimation_factor));

// Embed the given sequence of plaintext parts in the plaintext slots
// Advanced implementation based on FFT
function EmbedInSlots(parts: henselExponent := e)
    assert henselExponent le e;

    // Compute slot representation and split in subpolynomials
    slotRepresentation := GetSlotRepresentation(parts, henselExponent); fft_inv_res := [Zx | ];
    splittedRepresentation := [SplitPolynomial(polynomial, decimation_factor) : polynomial in slotRepresentation];
    for index := 1 to decimation_factor do
        input := [batcher_info[i][1] select Evaluate(splittedRepresentation[batcher_info[i][2]][index], batcher_info[i][3])
                                     else 0 : i in [1..m_prime]];

        // Compute inverse FFT and convert to polynomial
        Append(~fft_inv_res, BluesteinFFTInv(input, precomp_batcher));
    end for;

    // Combine polynomials to get final result
    return (CombinePolynomials(fft_inv_res) mod f) mod (p ^ henselExponent);
end function;

// Get all plaintext parts
// Advanced implementation based on FFT
function GetPlaintextParts(plaintext: henselExponent := e)
    assert henselExponent le e;

    // Compute evaluation in roots of unity and select necessary values
    sub_polynomials := SplitPolynomial(plaintext, decimation_factor); acc := [Zx | 0 : i in [1..l]];
    for index := 1 to decimation_factor do
        fft_res := BluesteinFFT(CatZeros(Eltseq(sub_polynomials[index]), m_prime), precomp_batcher);
        res := [ExpandPolynomial(Zx!fft_res[(GetHypercubeRepresentative(slot) mod m_prime) + 1], decimation_factor) :
                slot in [1..l]];
        for slot := 1 to l do   // Accumulate and replace x ^ 2 by x if necessary
            acc[slot] +:= (x ^ (((index - 1) * GetHypercubeRepresentative(slot)) mod m)) *
                          (root_in_base_ring select res[slot] else DecimatePolynomial(res[slot], 2));
        end for;
    end for;
    return [Zx | (el mod GetFirstSlotFactor()) mod (p ^ henselExponent) : el in acc];
end function;

else

// Precomputed data for inverse CRT
recombPolyLarge, recombPolySmall := RecombPoly();

// Apply the inverse CRT to the plaintext slots
function InverseCRT(slotRepresentation, henselExponent)
    return &+[Zx | ((slotRepresentation[index] * recombPolySmall[index]) mod factors[index]) * recombPolyLarge[index] :
                     index in [1..#slotRepresentation]] mod (p ^ henselExponent);
end function;

// Embed the given sequence of plaintext parts in the plaintext slots
// Naive implementation based on Chinese remainder theorem
function EmbedInSlots(parts: henselExponent := e)
    assert henselExponent le e;

    return InverseCRT(GetSlotRepresentation(parts, henselExponent), henselExponent);
end function;

// Get all plaintext parts
// Naive implementation based on Chinese remainder theorem
function GetPlaintextParts(plaintext: henselExponent := e)
    assert henselExponent le e;

    return [GetFromSlot(plaintext, index: henselExponent := henselExponent) : index in [1..l]];
end function;

end if;



// Return first 0/1 mask as a sequence
function GetMask(dim, pos)
    mask := [];
    for index := 1 to l do
        hyperIndex := IndexToHypercube(index);
        if hyperIndex[dim] + pos lt GetDimensionSize(dim) then
            Append(~mask, 1);
        else
            Append(~mask, 0);
        end if;
    end for;
    return mask;
end function;

// Compute first 0/1 mask
function GetMaskAhead(dim, pos, henselExponent)
    assert henselExponent le e;

    return EmbedInSlots(GetMask(dim, pos): henselExponent := henselExponent);
end function;

// Compute second 0/1 mask
function GetMaskBack(dim, pos, henselExponent)
    assert henselExponent le e;

    return EmbedInSlots([1 - entry : entry in GetMask(dim, pos)]: henselExponent := henselExponent);
end function;

// Return first adapted 0/1 mask as a sequence
function GetAdaptedMask(dim, pos)
    mask := [];
    for index := 1 to l do
        hyperIndex := IndexToHypercube(index);
        if pos le hyperIndex[dim] then
            Append(~mask, 1);
        else
            Append(~mask, 0);
        end if;
    end for;
    return mask;
end function;

// Compute first adapted 0/1 mask
function GetAdaptedMaskAhead(dim, pos, henselExponent)
    assert henselExponent le e;

    return EmbedInSlots(GetAdaptedMask(dim, pos): henselExponent := henselExponent);
end function;

// Compute second adapted 0/1 mask
function GetAdaptedMaskBack(dim, pos, henselExponent)
    assert henselExponent le e;

    return EmbedInSlots([1 - entry : entry in GetAdaptedMask(dim, pos)]: henselExponent := henselExponent);
end function;



// Apply an automorphism to the given element of Zx based on
// the modulus qi and the given exponent or hypercube index
// - If exponent is given: map x -> x ^ exp
// - If hypercube index is given: perform 'rotation', but not yet taking into
//   account that slots might leak to different hypercolumns in bad dimensions
function ApplyAutomorphism(element, qi, exp_hyperIndex)
    if Category(exp_hyperIndex) ne RngIntElt then
        exp_hyperIndex := GetInverseHypercubeRepresentative(exp_hyperIndex);
    end if;

    element := Eltseq(element); res := [0 : i in [1..m]];
    for index := 1 to #element do
        res[(((index - 1) * exp_hyperIndex) mod m) + 1] +:= element[index];
    end for;
    return ((Zx!res) mod f) mod qi;
end function;

// Apply an automorphism to the given ciphertext based on the given exponent or hypercube index
function ApplyAutomorphismCiphertext(c, exp_hyperIndex, switchKey)
    if Category(exp_hyperIndex) ne RngIntElt then
        exp_hyperIndex := GetInverseHypercubeRepresentative(exp_hyperIndex);
    end if;
    if HasDegreeZero(c) or (exp_hyperIndex eq 1) then
        return c;
    end if;
    hash1 := MyHash(c);

    cNew := <[ApplyAutomorphism(cPart, c[3], exp_hyperIndex) : cPart in c[1]], c[2], c[3], c[4]>;

    // Perform key switching if necessary
    if #cNew[1] eq 2 then
        AutomaticModSwitchRelin(~cNew);
        cNew := KeySwitch(cNew, switchKey);
    end if;

    // Decrease current modulus for efficiency reasons
    DynamicModSwitch(~cNew);
    res := CopyCiphertext(cNew: print_result := false);
    hash2 := MyHash(res); CreateCiphertext(hash2);
    PrintFile(TRACE, "bootstrapper.apply_galois(*" cat hash1 cat ", bk, *" cat hash2 cat
                     ", " cat IntegerToString(exp_hyperIndex) cat ", " cat GetHighLevelBit(res) cat ");");
    UseCiphertext(hash1);
    PrintFile(CONSTANTS, IntegerToString(exp_hyperIndex));
    return res;
end function;

// Apply an automorphism to the given plaintext based on the given exponent or hypercube index
function ApplyAutomorphismPlaintext(m, exp_hyperIndex: henselExponent := e)
    assert henselExponent le e;

    return ApplyAutomorphism(m, p ^ henselExponent, exp_hyperIndex);
end function;

// Key switching init
function GenSwitchKey(sk, exp_hyperIndex)
    skPrime := ApplyAutomorphism(sk, GetDefaultModulus(), exp_hyperIndex);
    return GenEncryptedKey(sk, skPrime);
end function;



// Apply the exp'th power of the Frobenius map, i.e. x -> x ^ (p ^ exp), to the given ciphertext
function ApplyFrobeniusPowerCiphertext(c, exp, switchKey)
    return ApplyAutomorphismCiphertext(c, Modexp(p, exp, m), switchKey);
end function;

// Apply the exp'th power of the Frobenius map, i.e. x -> x ^ (p ^ exp), to the given plaintext
function ApplyFrobeniusPowerPlaintext(element, exp: henselExponent := e)
    assert henselExponent le e;

    return ApplyAutomorphismPlaintext(element, Modexp(p, exp, m): henselExponent := henselExponent);
end function;



// Rotate the plaintext slots of the given ciphertext with pos positions in a good dimension
// The dimension dim can take the values 1, ..., GetNbDimensions().
// The variable pos can take the values 0, ..., GetDimensionSize(dim) - 1.
function RotateSlotsGoodDimension(c, dim, pos, switchKey)
    // Compute hypercube index and apply automorphism
    hyperIndex := Get1DHyperIndex(dim, pos);
    return ApplyAutomorphismCiphertext(c, hyperIndex, switchKey);
end function;

// Rotate the plaintext slots of the given ciphertext with pos positions in a bad dimension
// The dimension dim can take the values 1, ..., GetNbDimensions().
// The variable pos can take the values 0, ..., GetDimensionSize(dim) - 1.
function RotateSlotsBadDimension(c, dim, pos, switchKeyAhead, switchKeyBack)
    // Embed mask entries into slots
    maskAhead := GetMaskAhead(dim, pos, GetHenselExponent(c));
    maskBack := GetMaskBack(dim, pos, GetHenselExponent(c));

    // Apply masks to ciphertext in order to prevent leaking to other hypercolumns
    cAhead := MulConstant(c, maskAhead);
    cBack := MulConstant(c, maskBack);

    // Compute hypercube indices for automorphisms
    hyperIndexAhead := Get1DHyperIndex(dim, pos);
    hyperIndexBack := Get1DHyperIndex(dim, pos - GetDimensionSize(dim));

    // Apply automorphisms
    cAhead := ApplyAutomorphismCiphertext(cAhead, hyperIndexAhead, switchKeyAhead);
    cBack := ApplyAutomorphismCiphertext(cBack, hyperIndexBack, switchKeyBack);

    return Add(cAhead, cBack);
end function;

// Rotate the plaintext slots of the given ciphertext with the given exponent
// One bad dimension (and corresponding number of positions) may be specified
function RotateSlotsGeneral(c, exp, bad_dimension, bad_positions, switchKeyAhead, switchKeyBack)
    // Embed mask entries into slots
    maskAhead := GetMaskAhead(bad_dimension, bad_positions, GetHenselExponent(c));
    maskBack := GetMaskBack(bad_dimension, bad_positions, GetHenselExponent(c));

    // Apply masks to ciphertext in order to prevent leaking to other hypercolumns
    cAhead := MulConstant(c, maskAhead);
    cBack := MulConstant(c, maskBack);

    // Apply automorphisms
    backwards_factor := GetHypercubeRepresentative([index eq bad_dimension select GetDimensionSize(bad_dimension) else 0 :
                                                    index in [1..GetNbDimensions()]]);
    cAhead := ApplyAutomorphismCiphertext(cAhead, exp, switchKeyAhead);
    cBack := ApplyAutomorphismCiphertext(cBack, (exp * backwards_factor) mod m, switchKeyBack);

    return Add(cAhead, cBack);
end function;

// Rotate the plaintext slots of the given plaintext with pos positions
// The dimension dim can take the values 1, ..., GetNbDimensions().
// The variable pos can take the values 0, ..., GetDimensionSize(dim) - 1.
function RotateSlotsPlaintext(ptxt, dim, pos: henselExponent := e)
    assert henselExponent le e;

    if IsGoodDimension(dim) then
        // Compute hypercube index and apply automorphism
        hyperIndex := Get1DHyperIndex(dim, pos);
        return ApplyAutomorphismPlaintext(ptxt, hyperIndex: henselExponent := henselExponent);
    else
        // Embed mask entries into slots
        maskAhead := GetMaskAhead(dim, pos, henselExponent);
        maskBack := GetMaskBack(dim, pos, henselExponent);

        // Apply masks to plaintext in order to prevent leaking to other hypercolumns
        mAhead := ((ptxt * maskAhead) mod f) mod (p ^ henselExponent);
        mBack := ((ptxt * maskBack) mod f) mod (p ^ henselExponent);

        // Compute hypercube indices for automorphisms
        hyperIndexAhead := Get1DHyperIndex(dim, pos);
        hyperIndexBack := Get1DHyperIndex(dim, pos - GetDimensionSize(dim));

        // Apply automorphisms
        mAhead := ApplyAutomorphismPlaintext(mAhead, hyperIndexAhead: henselExponent := henselExponent);
        mBack := ApplyAutomorphismPlaintext(mBack, hyperIndexBack: henselExponent := henselExponent);

        return (mAhead + mBack) mod (p ^ henselExponent);
    end if;
end function;

// Rotate the plaintext slots of the given plaintext with the given exponent
// One bad dimension (and corresponding number of positions) may be specified
function RotateSlotsGeneralPlaintext(ptxt, exp, bad_dimension, bad_positions: henselExponent := e)
    // Embed mask entries into slots
    maskAhead := GetMaskAhead(bad_dimension, bad_positions, henselExponent);
    maskBack := GetMaskBack(bad_dimension, bad_positions, henselExponent);

    // Apply masks to plaintext in order to prevent leaking to other hypercolumns
    mAhead := ((ptxt * maskAhead) mod f) mod (p ^ henselExponent);
    mBack := ((ptxt * maskBack) mod f) mod (p ^ henselExponent);

    // Apply automorphisms
    backwards_factor := GetHypercubeRepresentative([index eq bad_dimension select GetDimensionSize(bad_dimension) else 0 :
                                                    index in [1..GetNbDimensions()]]);
    mAhead := ApplyAutomorphismPlaintext(mAhead, exp: henselExponent := henselExponent);
    mBack := ApplyAutomorphismPlaintext(mBack, (exp * backwards_factor) mod m: henselExponent := henselExponent);

    return (mAhead + mBack) mod (p ^ henselExponent);
end function;

end if;