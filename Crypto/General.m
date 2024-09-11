// This file stores some helper functions
//--------------------------
load "Crypto/Params.m";

// Encryption parameters
n := EulerPhi(m);   // Degree of f(x)
t := p^e;           // Plaintext modulus during bootstrapping

// Integers and quotient rings
Z := Integers();
Zm := Integers(m);
Zt := Integers(t);

// Polynomial rings
Zx<x> := PolynomialRing(Z);
Zt_poly := PolynomialRing(Zt);
f := Zx!CyclotomicPolynomial(m);

// Real and complex numbers used for error estimation
R := RealField(10);
C := ComplexField(10);



// Convert the given index to a sequence of indices based on the given maxima
function IndexToSequence(index, max_seq)
    index -:= 1;
    result := [Z | ];
    for max in max_seq do
        Append(~result, index mod max);
        index := index div max;
    end for;
    return result;
end function;

// Convert the given sequence of indices to a regular index based on the given maxima
function SequenceToIndex(ind_seq, max_seq)
    result := #ind_seq eq 0 select 0 else ind_seq[#ind_seq];
    for index := 1 to #ind_seq - 1 do
        result *:= max_seq[#ind_seq - index];
        result +:= ind_seq[#ind_seq - index];
    end for;
    return result + 1;
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

// Centered reduction of a sequence mod qi
function CenteredReductionSequence(seq, qi)
    return [Z | MinAbs(coeff mod qi, (coeff mod qi) - qi) : coeff in seq];
end function;

// Centered reduction of a polynomial mod qi
function CenteredReduction(poly, qi)
    return Zx!CenteredReductionSequence(Eltseq(poly), qi);
end function;

// Scale and round a sequence over qp/q
function ScaleAndRoundSequence(seq, qp, q)
    return [Z | Round(qp*coeff/q) : coeff in seq];
end function;

// Scale and round a polynomial over qp/q
function ScaleAndRound(poly, qp, q)
    return Zx!ScaleAndRoundSequence(Eltseq(poly), qp, q);
end function;

// Concatenate zeros to the given array until it reaches the indicated length
function CatZeros(seq, length)
    return seq cat [Z | 0 : i in [1..length - #seq]];
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
    result, p, r := IsPrimePower(m);
    return result and (p eq 2);
end function;



// More encryption parameters
w := CeilPowerOfTwo(Root(q, L));       // Base for relinearization, relin key goes from w^0 to w^(L-1)
noiseLevelRelin := t * w * Sqrt((n / 12) * L * (errorB * n / 2)) *
                   noiseBufferRelin;   // Noise is brought to this level before key switching