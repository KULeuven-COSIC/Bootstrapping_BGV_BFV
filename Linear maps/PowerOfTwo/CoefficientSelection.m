// Remove the coefficients of the terms that are no power of x^d
// All other coefficients are multiplied by d
function CoefficientSelection(c, switchKeys)
    for i := 0 to Valuation(d, 2) - 1 do
        c := Add(c, ApplyAutomorphismCiphertext(c, (n div (2 ^ i)) + 1, switchKeys[i + 1]));
    end for;
    return c;
end function;

// Evaluate trace to the subring that encodes sparse plaintexts
function EvaluateTrace(c, switchKeys)
    for i := 1 to (p mod 4 eq 1 select Valuation(d, 2) else Valuation(d div 2, 2)) do
        c := Add(c, ApplyAutomorphismCiphertext(c, p ^ (d div (2 ^ i)), switchKeys[i]));
    end for;
    return c;
end function;