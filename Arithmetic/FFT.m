// Precomputation for Bluestein FFT
// Return tuple with
// - W is a primitive 2m-root of unity
// - W ^ (k ^ 2) for k = -m + 1, ..., m - 1
// - W ^ (-(k ^ 2)) for k = -m + 1, ..., m - 1
// - W ^ (-(k ^ 2)) / m for k = 0, ..., m - 1
// - f is the m-th cyclotomic polynomial
// - m and ring that were given as argument
function PrecompBluestein(m, ring: W := 0)
    // Search for 2m-root of unity if not specified
    while W eq 0 do
        W := Random(ring) ^ ((#ring - 1) div (2 * m));
        W := ((W eq 0) or (Order(W) eq 2 * m)) select W else 0;
    end while;

    // Precompute sequences
    seq1 := [ring | (W ^ ((k ^ 2) mod (2 * m))) : k in [-m + 1..m - 1]];
    seq2 := [ring | (W ^ (-(k ^ 2) mod (2 * m))) : k in [-m + 1..m - 1]];
    seq3 := [ring | (W ^ (-(k ^ 2) mod (2 * m))) * ((ring!m) ^ (-1)) : k in [0..m - 1]];

    // Precompute cyclotomic polynomial
    f := Zx!CyclotomicPolynomial(m);

    return <W, seq1, seq2, seq3, f, m, ring>;
end function;

// Compute Bluestein FFT
function BluesteinFFT(list, precomp)
    m := precomp[6]; ring := precomp[7];
    poly_ring := PolynomialRing(ring);

    // Convert elements to ring
    list := PowerSequence(ring)!list;

    // Do operations to compute FFT
    x_q := poly_ring![list[index] * precomp[2][index + m - 1] : index in [1..m]];
    w_q := poly_ring!precomp[3];
    convolution := CatZeros(Eltseq(x_q * w_q), 2 * m - 1);

    return [precomp[2][index + m - 1] * convolution[index + m - 1] : index in [1..m]];
end function;

// Compute inverse Bluestein FFT
function BluesteinFFTInv(list, precomp)
    m := precomp[6]; ring := precomp[7];
    poly_ring := PolynomialRing(ring);

    // Convert elements to ring
    list := PowerSequence(ring)!list;

    // Do operations to compute inverse FFT
    x_q := poly_ring![list[index] * precomp[3][index + m - 1] : index in [1..m]];
    w_q := poly_ring!precomp[2];
    convolution := CatZeros(Eltseq(x_q * w_q), 2 * m - 1);

    return [precomp[4][index] * convolution[index + m - 1] : index in [1..m]];
end function;



// Compute the maximum modulus of the given input in the canonical embedding
precomp_complex := PrecompBluestein(m, C: W := Exp(2 * Pi(C) * C.1 / (2 * m)));
function GetMaxModulus(input)
    seq := BluesteinFFT(CatZeros(Eltseq(input), m), precomp_complex);
    return Maximum([Modulus(seq[pow + 1]) : pow in [0..m - 1] | GCD(pow, m) eq 1]);
end function;



// Compute adjoint element to extension of GF(p) given the generating polynomial
function GetAdjointElement(p, generating_poly)
    if Degree(generating_poly) eq 1 then    // Magma acts strangely if extension field is base field
        return Random(Roots(PolynomialRing(GF(p))!generating_poly))[1];
    else                                    // Otherwise just compute field extension
        return ext<GF(p) | generating_poly>.1;
    end if;
end function;

// Compute a primitive 2m-root of unity over (an extension of) the slot algebra for power-of-two cyclotomics
// Result is returned as an element of Zx
// Also return the updated generating polynomial and whether result is in base ring
function ComputeBluesteinRoot(m, p, e, generating_poly)
    assert IsPowerOfTwo(m); assert GCD(m, p) eq 1;

    // First check whether result is in base ring
    if IsDivisibleBy(p ^ Degree(generating_poly) - 1, 2 * m) then
        // Compute result over field
        root := Zx!Eltseq(Sqrt(GetAdjointElement(p, generating_poly)));

        // Then perform Hensel lifting to get better precision
        for precision := 0 to Ceiling(Log(2, e)) - 1 do
            henselExponent := 2 ^ precision;    // Hensel exponent at start of iteration
            quo_ring<y> := quo<PolynomialRing(Integers(p ^ henselExponent)) | generating_poly>;
            term := ((x - root ^ 2) mod generating_poly) div (p ^ henselExponent);
            term *:= Modinv(2, p ^ henselExponent) * (Zx!(Evaluate(root, y) ^ (-1)));
            term := (term mod generating_poly) mod (p ^ henselExponent);
            root := (root + (p ^ henselExponent) * term) mod (p ^ (2 * henselExponent));
        end for;
        return root mod (p ^ e), generating_poly, true;
    else    // Replace x by x ^ 2
        return x, ExpandPolynomial(generating_poly, 2), false;
    end if;
end function;