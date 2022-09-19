load "Crypto/General.m";

// Precomputation for Bluestein FFT
// Return tuple with
// - W is 2m-root of unity
// - W ^ (k ^ 2) for k = -m + 1, ..., m - 1
// - W ^ (-(k ^ 2)) for k = -m + 1, ..., m - 1
// - W ^ (-(k ^ 2)) / m for k = 0, ..., m - 1
// - f is the mth cyclotomic polynomial
function PrecompBluestein(m, p: W := 0)
    Fp := GF(p);

    // Search for 2m-root of unity
    while (W eq 0) or (Order(W) ne 2 * m) do
        W := Random(Fp) ^ ((p - 1) div (2 * m));
    end while;

    // Precompute sequences
    seq1 := [Fp | (W ^ (k ^ 2)) : k in [-m + 1..m - 1]];
    seq2 := [Fp | (W ^ (-(k ^ 2))) : k in [-m + 1..m - 1]];
    seq3 := [Fp | (W ^ (-(k ^ 2))) * Modinv(m, p) : k in [0..m - 1]];

    // Precompute cyclotomic polynomial
    f := Zx!CyclotomicPolynomial(m);

    return <W, seq1, seq2, seq3, f>;
end function;

// Compute Bluestein FFT
function BluesteinFFT(x, m, p, precomp)
    Fp := GF(p);
    Fp_poly := PolynomialRing(Fp);

    // Convert elements to finite field
    x := PowerSequence(Fp)!x;

    // Do operations to compute FFT
    x_q := Fp_poly![x[index] * precomp[2][index + m - 1] : index in [1..m]];
    w_q := Fp_poly!precomp[3];
    convolution := CatZeros(Eltseq(x_q * w_q), 2 * m - 1);

    return PowerSequence(Z)![precomp[2][index + m - 1] * convolution[index + m - 1] : index in [1..m]];
end function;

// Compute inverse Bluestein FFT
function BluesteinFFTInv(x, m, p, precomp)
    Fp := GF(p);
    Fp_poly := PolynomialRing(Fp);

    // Convert elements to finite field
    x := PowerSequence(Fp)!x;

    // Do operations to compute inverse FFT
    x_q := Fp_poly![x[index] * precomp[3][index + m - 1] : index in [1..m]];
    w_q := Fp_poly!precomp[2];
    convolution := CatZeros(Eltseq(x_q * w_q), 2 * m - 1);

    return PowerSequence(Z)![precomp[4][index] * convolution[index + m - 1] : index in [1..m]];
end function;