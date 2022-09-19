load "Digit extraction/Arithmetic.m";
load "Digit extraction/Paterson_Stockmeyer.m";

// Return the lifting polynomial with respect to the parameters p and e
function GetLiftingPolynomial(p, e)
    // First calculate output of the fi polynomials and then construct them
    // based on Newton interpolation
    digits := [[(((z0 ^ p) - ((z0 ^ p) mod (p ^ i))) div (p ^ i)) mod p : i in [1..e]] : z0 in [0..p - 1]];
    polynomials := [&+[&*[x - xi : xi in {0..p - 1} diff {z0}] * Modinv(&*[z0 - xi : xi in {0..p - 1} diff {z0}], p ^ e)
                                                               * digits[z0 + 1][i] : z0 in [0..p - 1]] : i in [1..e]];
    
    // Return the lifting polynomial
    return (x ^ p - &+[polynomials[i] * (p ^ i) : i in [1..e]]) mod (p ^ (e + 1));
end function;

// Return the lowest digit removal polynomial with respect to the parameters p and e
function GetLowestDigitRemovalPolynomial(p, e)
    // Integers mod p ^ e
    Zpe := Integers(p ^ e);
    Zpe_poly := PolynomialRing(Zpe);
    Zpe_y<y> := quo<Zpe_poly | Zpe_poly.1 ^ ((e - 1) * (p - 1) + 2)>;

    // Compute B(y) and Taylor expansion
    B := ((1 + y) ^ p) - (y ^ p) - 1;
    taylor := Eltseq(p * ((1 + y) ^ p) * (&+[(-B) ^ i : i in [0..(e - 1) * (p - 1) + 1]]));
    taylor := CatZeros(taylor, (e - 1) * (p - 1) + 2);

    // Compute the polynomial
    poly := Zx!0;
    ChangeUniverse(~taylor, Z);
    for m := p to (e - 1) * (p - 1) + 1 do
        factor := taylor[m + 1] / Factorial(m);
        poly +:= &*[x - i : i in [0..m - 1]] * Numerator(factor) * Modinv(Denominator(factor), p ^ e);
    end for;
    return poly mod (p ^ e);
end function;

// Return the lowest digit retain polynomial with respect to the parameters p and e
function GetLowestDigitRetainPolynomial(p, e)
    return (x - GetLowestDigitRemovalPolynomial(p, e)) mod (p ^ e);
end function;

// Halevi and Shoup digit extraction algorithm
function HaleviShoupDigitExtraction(u, p, e, v, addFunc, subFunc, mulFunc, div_pFunc, liftingPolynomial)
    // Populate the triangle with digits
    // Less memory is needed if only one column and the result are stored
    col := [u : i in [1..v]];   // Current column of the upper left triangle
    res := u;                   // Result of the digit extraction
    for rowIndex := 0 to v - 1 do
        // Apply lifting polynomial several times to the first element of the row
        for colIndex := 1 to e - rowIndex - 1 do
            col[rowIndex + 1] := PatersonStockmeyer(liftingPolynomial mod (p ^ (colIndex + 1)), col[rowIndex + 1],
                                                    addFunc, mulFunc);

            // Subtract elements on the same diagonal
            if rowIndex + colIndex + 1 le v then
                col[rowIndex + colIndex + 1] := div_pFunc(subFunc(col[rowIndex + colIndex + 1], col[rowIndex + 1]));
            end if;
        end for;
        res := div_pFunc(subFunc(res, col[rowIndex + 1]));
    end for;
    return res;
end function;

// Chen and Han digit extraction algorithm
function ChenHanDigitExtraction(u, p, e, v, addFunc, subFunc, mulFunc, div_pFunc, liftingPolynomial, lowestDigitRetainPolynomials)
    // Populate the triangle with digits
    // Less memory is needed if only one column and the result are stored
    col := [u : i in [1..v]];   // Current column of the upper left triangle
    res := u;                   // Result of the digit extraction
    for rowIndex := 0 to v - 1 do
        // Apply the lowest digit retain polynomial
        rightDigit := PatersonStockmeyer(lowestDigitRetainPolynomials[e - rowIndex], col[rowIndex + 1], addFunc, mulFunc);
        res := div_pFunc(subFunc(res, rightDigit));
        
        // Apply lifting polynomial several times to the first element of the row
        for colIndex := 1 to v - rowIndex - 1 do
            col[rowIndex + 1] := PatersonStockmeyer(liftingPolynomial mod (p ^ (colIndex + 1)), col[rowIndex + 1],
                                                    addFunc, mulFunc);

            // Subtract elements on the same diagonal
            col[rowIndex + colIndex + 1] := div_pFunc(subFunc(col[rowIndex + colIndex + 1], col[rowIndex + 1]));
        end for;
    end for;
    return res;
end function;