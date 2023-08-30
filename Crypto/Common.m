// Common functionality for the BGV and BFV scheme
//--------------------------
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



// Check whether the given variable is a ciphertext
function IsCiphertext(c)
    if Category(c) eq Category(<[Zx | ], 0, 0, R!0>) then
        return true;
    else
        return false;
    end if;
end function;

// Return a new ciphertext that encrypts the constant 0
function GetZeroCiphertext(c)
    q := GetDefaultModulus();
    if Category(c) eq Category(0) then
        return <[Zx | 0], c, q, R!0>;
    else
        return <[Zx | 0], c[2], q, R!0>;
    end if;
end function;

// Return the plaintext Hensel exponent of the given ciphertext
function GetHenselExponent(c)
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



// Addition
function Add(c1, c2)
    assert c1[2] eq c2[2];  // Plaintext moduli should be equal

    // Ciphertexts should have same modulus and degree
    ModSwitchLowestModulus(~c1, ~c2);
    PadZeros(~c1, ~c2);
    return <[(c1[1][i] + c2[1][i]) mod c1[3] : i in [1..#c1[1]]], c1[2], c1[3], c1[4] + c2[4]>;
end function;

// Subtraction
function Sub(c1, c2)
    assert c1[2] eq c2[2];  // Plaintext moduli should be equal

    // Ciphertexts should have same modulus and degree
    ModSwitchLowestModulus(~c1, ~c2);
    PadZeros(~c1, ~c2);
    return <[(c1[1][i] - c2[1][i]) mod c1[3] : i in [1..#c1[1]]], c1[2], c1[3], c1[4] + c2[4]>;
end function;

// Multiplication with relinearization
function Mul(c1, c2, rk)
    // Ensure that noise doesn't grow exponentially in multiplicative depth
    AutomaticModSwitchMul(~c1);
    AutomaticModSwitchMul(~c2);

    // Perform the multiplication and relinearization
    mul := MulNR(c1, c2);
    if #mul[1] eq 3 then
        AutomaticModSwitchRelin(~mul);
        mul := Relin(mul, rk);
    end if;

    // Decrease current modulus for efficiency reasons
    DynamicModSwitch(~mul);
    return mul;
end function;

// Multiplication with constant
function MulConstant(c, constant)
    constant := CenteredReduction(constant, c[2]);
    res := <[((constant * cPart) mod f) mod c[3] : cPart in c[1]], c[2], c[3], SquareSum(constant) * c[4]>;

    // Decrease current modulus for efficiency reasons
    DynamicModSwitch(~res);
    return res;
end function;

// Relin key init
function GenRelinKey(sk)
    sk2 := sk^2 mod f;
    return GenEncryptedKey(sk, sk2);
end function;



// Max norm of the error in coefficient embedding
// The error is normalized to the standard modulus q
function ErrorC(c, sk)
    return R!(Log(2, (q / c[3]) * MaximumOrOne([Abs(coeff) : coeff in Eltseq(CiphertextErrorPol(c, sk))])));
end function;

// The maximum of the entries of the error polynomial in the canonical embedding
// The error is normalized to the standard modulus q
function ErrorCanC(c, sk)
    errPol := CiphertextErrorPol(c, sk);    // Compute only once
    return R!(Log(2, (q / c[3]) * MaximumOrOne([Modulus(Evaluate(errPol, xi ^ pow)) : pow in [0..m - 1] | GCD(pow, m) eq 1])));
end function;

// Estimated error of the given ciphertext
// The error is normalized to the standard modulus q
function EstimatedErrorCanC(c)
    return R!(Log(2, MaximumOrOne(q * Sqrt(c[4]) / c[3])));
end function;



// The code from here on is only executed if there is a valid hypercube structure
if GCD(m, p) eq 1 then

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
    if Category(index) eq Category(0) then
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

// Precomputed data for inverse CRT
recombPolyLarge, recombPolySmall := RecombPoly();

// Apply the inverse CRT to the plaintext slots
function InverseCRT(slotRepresentation, henselExponent)
    return &+[Zx | ((slotRepresentation[index] * recombPolySmall[index]) mod factors[index]) * recombPolyLarge[index] :
                     index in [1..#slotRepresentation]] mod (p ^ henselExponent);
end function;

// Embed the given sequence of plaintext parts in the plaintext slots
function EmbedInSlots(parts: henselExponent := e)
    assert henselExponent le e;

    slotRepresentation := [Zx | ];
    for slot := 1 to l do
        // Construct ring modulo the factor of the slot
        Zt_slot<y> := quo<Zt_poly | factors[slot]>;

        // Apply inverse automorphism to compute representation in slot
        exp := GetInverseHypercubeRepresentative(slot);
        Append(~slotRepresentation, Evaluate(Zx!parts[slot], y ^ exp));
    end for;

    return InverseCRT(slotRepresentation, henselExponent);
end function;

// Get the plaintext part at the given (hypercube) index
function GetFromSlot(plaintext, index: henselExponent := e)
    assert henselExponent le e;

    if Category(index) ne Category(0) then
        index := HypercubeToIndex(index);
    end if;

    // Construct ring modulo the factor of the first slot
    Zt_F1<y> := GetSlotAlgebra(henselExponent);
    slotRepresentation := Zx!(plaintext mod factors[index]);
    return Zx!Evaluate(slotRepresentation, y ^ GetHypercubeRepresentative(index));
end function;

// Get all plaintext parts
function GetPlaintextParts(plaintext: henselExponent := e)
    assert henselExponent le e;

    return [GetFromSlot(plaintext, index: henselExponent := henselExponent) : index in [1..l]];
end function;



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
    if Category(exp_hyperIndex) ne Category(0) then
        exp_hyperIndex := GetInverseHypercubeRepresentative(exp_hyperIndex);
    end if;

    // Convert to doubleCRT representation
    nbPrimes := Ceiling(Log(qi * expansion_automorphism) / Log(minModulus));
    doubleCRT := PolynomialToDoubleCRT(element: level := nbPrimes);

    // Automorphism is just swapping some elements
    autoDoubleCRT := [[] : i in [1..#doubleCRT]];
    for currentExponent := 0 to m - 1 do
        if GCD(currentExponent, m) eq 1 then
            for ind := 1 to #doubleCRT do
                autoDoubleCRT[ind][currentExponent + 1] := doubleCRT[ind][((exp_hyperIndex * currentExponent) mod m) + 1];
            end for;
        end if;
    end for;
    return CenteredReduction(DoubleCRTToPolynomial(autoDoubleCRT), partialModuli[nbPrimes]) mod qi;
end function;

// Apply an automorphism to the given ciphertext based on the given exponent or hypercube index
function ApplyAutomorphismCiphertext(c, exp_hyperIndex, switchKey)
    cNew := <[ApplyAutomorphism(cPart, c[3], exp_hyperIndex) : cPart in c[1]], c[2], c[3], c[4]>;

    // Perform key switching if necessary
    if #cNew[1] eq 2 then
        AutomaticModSwitchRelin(~cNew);
        cNew := KeySwitch(cNew, switchKey);
    end if;

    // Decrease current modulus for efficiency reasons
    DynamicModSwitch(~cNew);
    return cNew;
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

// Rotate the plaintext slots of the given plaintext with pos positions
// The dimension dim can take the values 1, ..., GetNbDimensions().
// The variable pos can take the values 0, ..., GetDimensionSize(dim) - 1.
function RotateSlotsPlaintext(m, dim, pos: henselExponent := e)
    assert henselExponent le e;

    if IsGoodDimension(dim) then
        // Compute hypercube index and apply automorphism
        hyperIndex := Get1DHyperIndex(dim, pos);
        return ApplyAutomorphismPlaintext(m, hyperIndex: henselExponent := henselExponent);
    else
        // Embed mask entries into slots
        maskAhead := GetMaskAhead(dim, pos, henselExponent);
        maskBack := GetMaskBack(dim, pos, henselExponent);

        // Apply masks to plaintext in order to prevent leaking to other hypercolumns
        mAhead := ((m * maskAhead) mod f) mod (p ^ henselExponent);
        mBack := ((m * maskBack) mod f) mod (p ^ henselExponent);

        // Compute hypercube indices for automorphisms
        hyperIndexAhead := Get1DHyperIndex(dim, pos);
        hyperIndexBack := Get1DHyperIndex(dim, pos - GetDimensionSize(dim));

        // Apply automorphisms
        mAhead := ApplyAutomorphismPlaintext(mAhead, hyperIndexAhead: henselExponent := henselExponent);
        mBack := ApplyAutomorphismPlaintext(mBack, hyperIndexBack: henselExponent := henselExponent);

        return (mAhead + mBack) mod (p ^ henselExponent);
    end if;
end function;

end if;