// Remove the coefficients of the terms that are no power of x^d
// All other coefficients are multiplied by d
function CoefficientSelection(c, switchKeys)
    res := c;
    for i := 0 to Valuation(d, 2) - 1 do
        res := Add(res, ApplyAutomorphismCiphertext(res, (n div (2 ^ i)) + 1, switchKeys[i + 1]));
    end for;
    return res;
end function;