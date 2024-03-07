// This file computes the experimental value of can_max in 'Crypto/Params.m' which
// is necessary for noise estimation
// This corresponds to Max([Modulus(Evaluate(sk, xi ^ e)) ^ 2 : e in [0..m - 1] | GCD(e, m) eq 1]) where
// xi is a complex primitive m-th root of unity and sk ranges over the secret key distribution
// This file gives the 80-th percentile for the above quantity
load "Crypto/General.m";

// Precomputation for Bluestein FFT
function PrecompBluestein(m)
    // Precompute sequences
    seq1 := [C | Exp(2 * Pi(C) * C.1 * (k ^ 2) / (2 * m)) : k in [-m + 1..m - 1]];
    seq2 := [C | Exp(2 * Pi(C) * C.1 * (-(k ^ 2)) / (2 * m)) : k in [-m + 1..m - 1]];

    return <seq1, seq2>;
end function;

// Compute Bluestein FFT
function BluesteinFFT(x, m, precomp)
    // Convert elements to polynomial ring over complex numbers
    C_poly := PolynomialRing(C);

    // Do operations to compute FFT
    x_q := C_poly![x[index] * precomp[1][index + m - 1] : index in [1..m]];
    w_q := C_poly!precomp[2];
    convolution := CatZeros(Eltseq(x_q * w_q), 2 * m - 1);

    return [precomp[1][index + m - 1] * convolution[index + m - 1] : index in [1..m]];
end function;

// Compute the maximum squared modulus
function GetMaxSquaredModulus(input, m, precomp)
    seq := BluesteinFFT(CatZeros(input, m), m, precomp); maximum := 0;
    for currentExponent := 0 to m - 1 do
        if (GCD(currentExponent, m) eq 1) and (Modulus(seq[currentExponent + 1]) gt maximum) then
            maximum := Modulus(seq[currentExponent + 1]);
        end if;
    end for;
    return maximum ^ 2;
end function;

// Determine experimentally the value of the largest square entry of the secret key in the canonical
// embedding: Max([Modulus(Evaluate(sk, xi ^ e)) ^ 2 : e in [0..m - 1] | GCD(e, m) eq 1])
nbIterations := 100; list := [];
ind := Round(0.8 * nbIterations);   // Correct estimate in 80 percent of the cases
precomp := PrecompBluestein(m);
for it := 1 to nbIterations do
    "Iteration " cat IntegerToString(it);
    Append(~list, GetMaxSquaredModulus(Eltseq(TernaryPol(h)), m, precomp));
end for;

Sort(~list);
"Experimental value for can_max", list[ind];