// This file stores some helper functions
//--------------------------
load "Crypto/Params.m";
assert (useHElibLT select 1 else 0) + (useSEALLT select 1 else 0) +
       (useOurLT select 1 else 0) + (useGBFVLT select 1 else 0) eq 1;

// Encryption parameters
n := EulerPhi(m);   // Degree of f(x)
t := p^e;           // Plaintext modulus during bootstrapping

// Quotient rings
Zm := Integers(m);
Zt := Integers(t);

// Polynomial rings
Zt_poly := PolynomialRing(Zt);
f := Zx!CyclotomicPolynomial(m);

// Cyclotomic field
Q := Rationals();
cyclo_field := ext<Q | f>;

// Real and complex numbers used for error estimation
R := RealField(10);
C := ComplexField(10);

// Compute exponent for GBFV
Fp_poly := PolynomialRing(GF(p)); fp := Fp_poly!f;
gbfvExponent := Degree(GCD(fp, Fp_poly!gbfvModulus));
intModuli := [modulus mod f : modulus in intModuli];
allModuli := [gbfvModulus] cat intModuli cat [p];
intExponents := [gbfvExponent] cat [Degree(GCD(fp, Fp_poly!modulus)) : modulus in intModuli];

// Only for SEAL traces
assert #intModuli eq 0;



// Convert the given index to a sequence of indices based on the given sizes (and minima)
function IndexToSequence(index, sizes: minima := [0 : i in sizes])
    index -:= 1; result := [Z | ];  // Start counting from zero in sequence
    for i := 1 to #sizes do
        Append(~result, (index mod sizes[i]) + minima[i]);
        index := index div sizes[i];
    end for;
    return result;
end function;

// Convert the given sequence of indices to a regular index based on the given sizes (and minima)
function SequenceToIndex(ind_seq, sizes: minima := [0 : i in sizes])
    result := (#ind_seq eq 0) select 0 else (ind_seq[#ind_seq] - minima[#minima]);
    for index := 1 to #ind_seq - 1 do
        result *:= sizes[#sizes - index];
        result +:= (ind_seq[#ind_seq - index] - minima[#minima - index]);
    end for;
    return result + 1;              // Start counting from one in index
end function;

// Return the number that is the lowest in absolute value
// If both absolute values are equal, the second one is returned
function MinAbs(a, b)
    if Abs(a) lt Abs(b) then
        return a;
    else
        return b;
    end if;
end function;

// Concatenate zeros to the given array until it reaches the indicated length
function CatZeros(seq, length)
    return seq cat [Z | 0 : i in [1..length - #seq]];
end function;

// Centered reduction of a sequence mod qi
function CenteredReductionSequence(seq, qi)
    return [Z | MinAbs(coeff mod qi, (coeff mod qi) - qi) : coeff in seq];
end function;

// Centered reduction of a polynomial mod qi
function CenteredReduction(poly, qi)
    return Zx!CenteredReductionSequence(Eltseq(poly), qi);
end function;

// Centered reduction of a rational sequence mod 1
function CenteredReductionRationalSequence(seq)
    seq := [Q | number - Round(number) : number in seq];
    return [Q | number eq 1/2 select -1/2 else number : number in seq];
end function;

// Convert the given integer polynomial to the cyclotomic field
function ToCyclotomicField(poly)
    return cyclo_field!CatZeros(Eltseq((Zx!poly) mod f), n);
end function;

// Precompute inverses of t^i and p^i
common_moduli := [ToCyclotomicField(gbfvModulus) ^ i : i in [1..e]] cat
                 &cat[[ToCyclotomicField(modulus) ^ i : i in [1..e]] : modulus in intModuli] cat
                 [ToCyclotomicField(p) ^ i : i in [1..e]];
common_inverses := [i eq 1 select ToCyclotomicField(gbfvModulus) ^ (-1) else
                                  Self(i - 1) * Self(1) : i in [1..e]] cat
                   &cat[[i eq 1 select ToCyclotomicField(modulus) ^ (-1) else
                                       Self(i - 1) * Self(1) : i in [1..e]] : modulus in intModuli] cat
                   [i eq 1 select ToCyclotomicField(p) ^ (-1) else Self(i - 1) * Self(1) : i in [1..e]];

// Compute inverse of given number
function InvertOverField(element)
    element := ToCyclotomicField(element);      // Make sure that the element is in the field
    return (Index(common_moduli, element) eq 0) select element ^ (-1) else common_inverses[Index(common_moduli, element)];
end function;

// Divide the given polynomials that are known to be divisible in the cyclomtic ring
function DivideOverField(numerator, denominator)
    return Zx!Eltseq(ToCyclotomicField(numerator) * InvertOverField(denominator));
end function;

// Flatten the given polynomial with respect to t
function Flatten(poly, t)
    seq := CenteredReductionRationalSequence(Eltseq(ToCyclotomicField(poly) * InvertOverField(t)));
    return Zx!Eltseq(ToCyclotomicField(t) * (cyclo_field!seq));
end function;

// Scale and round a sequence over 1/q where q is a scalar
function ScaleAndRoundSequence(seq, q)
    return [Z | Round(coeff/q) : coeff in seq];
end function;

// Scale and round a polynomial over qp/q mod f where qp and q are ring elements
function ScaleAndRound(poly, qp, q)
    if Category(q) eq RngIntElt then    // Optimized implementation
        return Zx!ScaleAndRoundSequence(Eltseq((poly * qp) mod f), q);
    else
        return Zx!ScaleAndRoundSequence(Eltseq(ToCyclotomicField(poly) * ToCyclotomicField(qp) * InvertOverField(q)), 1);
    end if;
end function;

// Compute the sum of the squares of the coefficients of the given polynomial
function SquareSum(poly)
    return &+[Z | el ^ 2 : el in Eltseq(Zx!poly)];
end function;

// Swap the i'th and j'th element of the given sequence
function Swap(seq, i, j)
    element := seq[i]; seq[i] := seq[j]; seq[j] := element;
    return seq;
end function;

// Return the maximum value of the sequence (or value) with a minimum of 1
function MaximumOrOne(seq)
    if (Category(seq) eq RngIntElt) or (Category(seq) eq FldReElt) then
        seq := [seq];
    end if;

    // Compute maximum of extended sequence
    return Maximum(seq cat [1]);
end function;

// Decimate the given polynomial
function DecimatePolynomial(polynomial, factor)
    poly_seq := Eltseq(polynomial);
    return Zx![poly_seq[factor * i + 1] : i in [0..(#poly_seq - 1) div factor]];
end function;

// Split the given polynomial in subpolynomials
function SplitPolynomial(polynomial, factor)
    poly_seq := Eltseq(polynomial);
    res := [[Z | ] : i in [1..factor]];
    for index := 1 to #poly_seq do
        Append(~res[((index - 1) mod factor) + 1], poly_seq[index]);
    end for;
    return [Zx | el : el in res];
end function;

// Expand the given polynomial
function ExpandPolynomial(polynomial, factor)
    poly_seq := Eltseq(polynomial);
    return Zx![IsDivisibleBy(i, factor) select poly_seq[i div factor + 1] else 0 : i in [0..factor * (#poly_seq - 1)]];
end function;

// Combine the given polynomials
function CombinePolynomials(polynomials)
    max_deg := Maximum([Degree(polynomial) : polynomial in polynomials]); res := [Z | ];
    poly_seq := [CatZeros(Eltseq(polynomial), max_deg + 1) : polynomial in polynomials];
    for index := 0 to #polynomials * (max_deg + 1) - 1 do
        Append(~res, poly_seq[(index mod #polynomials) + 1][(index div #polynomials) + 1]);
    end for;
    return Zx!res;
end function;



// Error sampled from binomial instead of Gaussian
function BinomialSample(B)
    // Binomial distribution on [-B, B]
    return &+(IntegerToSequence(Random(2^(2*B)-1), 2)) - B;
end function;

// Sample error polynomial
function ErrorPol()
    return Zx![Z | BinomialSample(errorB) : i in [1..n]];
end function;

// Sample random polynomial with coefficients in [0..bound-1]
function RandPol(bound)
    return Zx![Z | Random(bound-1) : i in [1..n]];
end function;

// Sample ternary polynomial with given Hamming weight
function TernaryPol(w)
    c := [Z | 0 : i in [1..n]];
    I := RandomSubset({1..n}, w);
    for i in I do
        c[i] := (-1)^Random(1);
    end for;

    return Zx!c;
end function;



// Compute a prime-power factorization
function PrimePowerFactorization(m)
    return Reverse(Sort([Z | el[1] ^ el[2] : el in Factorization(m)]));
end function;

// Check if factors_m is a pairwise coprime factorization of m
function IsCoprimeFactorization(m, factors_m)
    // Check if product is correct
    if &*factors_m ne m then
        return false;
    end if;

    // Check if factors are pairwise coprime
    for index1 := 1 to #factors_m do
        for index2 := 1 to #factors_m do
            if (index1 ne index2) and (GCD(factors_m[index1], factors_m[index2]) ne 1) then
                return false;
            end if;
        end for;
    end for;
    return true;
end function;

// Compute the largest power of two that is less than or equal to the given number
function FloorPowerOfTwo(element)
    return 2 ^ Floor(Log(2, element));
end function;

// Compute the smallest power of two that is greater than or equal to the given number
function CeilPowerOfTwo(element)
    return 2 ^ Ceiling(Log(2, element));
end function;

// Check if the given parameter is a power of two
function IsPowerOfTwo(m)
    result, p, r := IsPrimePower(2 * m);
    return result and (p eq 2);
end function;



// More encryption parameters
w := CeilPowerOfTwo(Root(q, L));       // Base for relinearization, relin key goes from w^0 to w^(L-1)
noiseLevelRelin := t * w * Sqrt((n / 12) * L * (errorB * n / 2)) *
                   noiseBufferRelin;   // Noise is brought to this level before key switching