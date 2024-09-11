// This file computes the experimental value of can_max in 'Crypto/Params.m' which is necessary for noise estimation
// This corresponds to an estimate of the maximum squared entry of the secret key in the canonical embedding
// This file gives the 80-th percentile for the above quantity
load "Crypto/General.m";
load "Arithmetic/FFT.m";

nbIterations := 100; list := [];
ind := Round(0.8 * nbIterations);   // Correct estimate in 80 percent of the cases
for it := 1 to nbIterations do
    "Iteration " cat IntegerToString(it);
    Append(~list, GetMaxModulus(TernaryPol(h)) ^ 2);
end for;

Sort(~list);
"Experimental value for can_max", list[ind];