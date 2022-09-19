load "Crypto/BFV/BFV.m";

// Determine experimentally the value of the largest square entry of the
// secret key in the canonical embedding:
// Max([Modulus(Evaluate(sk, xi ^ e)) ^ 2 : e in [0..m - 1] | GCD(e, m) eq 1])
nbIterations := 100;
ind := Round(0.8 * nbIterations);   // Correct estimate in 80 percent of the cases
list := [];
for it := 1 to nbIterations do
    "Iteration " cat IntegerToString(it);
    sk, pk := GenKeyPair();
    Append(~list, Maximum([Modulus(Evaluate(sk, xi ^ pow)) ^ 2 : pow in [0..m - 1] | GCD(pow, m) eq 1]));
end for;

Sort(~list);
"Experimental value for can_max", list[ind];