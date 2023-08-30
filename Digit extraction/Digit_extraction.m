load "Digit extraction/Arithmetic.m";
load "Digit extraction/Poly_eval.m";

// Return the lifting polynomial with respect to the parameters p and e
function GetLiftingPolynomial(p, e)
    // First calculate output of the fi polynomials and then construct them
    // based on Newton interpolation
    digits := [[(((z0 ^ p) - ((z0 ^ p) mod (p ^ i))) div (p ^ i)) mod p : i in [1..e]] : z0 in [0..p - 1]];
    polynomials := [&+[&*[x - xi : xi in {0..p - 1} diff {z0}] * Modinv(&*[z0 - xi : xi in {0..p - 1} diff {z0}], p ^ e)
                                                               * digits[z0 + 1][i] : z0 in [0..p - 1]] : i in [1..e]];
    
    // Return the lifting polynomial
    poly := (x ^ p - &+[polynomials[i] * (p ^ i) : i in [1..e]]) mod (p ^ (e + 1));
    return (Evaluate(poly, x + ((p - 1) div 2)) - ((p - 1) div 2)) mod (p ^ (e + 1));
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
    return Evaluate(poly, x + ((p - 1) div 2)) mod (p ^ e);
end function;

// Return the lowest digit retain polynomial with respect to the parameters p and e
function GetLowestDigitRetainPolynomial(p, e)
    // Make sure to use balanced digits for odd p
    e_new := (p eq 2) select e + 1 else e;
    poly := (x - GetLowestDigitRemovalPolynomial(p, e_new)) mod (p ^ e_new);
    
    // Make sure that the polynomials have only even or odd coefficients
    if p eq 2 then
        return ((poly + Evaluate(poly, -x)) div 2) mod (p ^ e);
    else
        return ((poly - Evaluate(poly, -x)) div 2) mod (p ^ e);
    end if;
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
            col[rowIndex + 1] := PolyEval(liftingPolynomial mod (p ^ (colIndex + 1)), col[rowIndex + 1], addFunc, mulFunc);

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
        rightDigit := PolyEval(lowestDigitRetainPolynomials[e - rowIndex], col[rowIndex + 1], addFunc, mulFunc);
        res := div_pFunc(subFunc(res, rightDigit));
        
        // Apply lifting polynomial several times to the first element of the row
        for colIndex := 1 to v - rowIndex - 1 do
            col[rowIndex + 1] := PolyEval(liftingPolynomial mod (p ^ (colIndex + 1)), col[rowIndex + 1], addFunc, mulFunc);

            // Subtract elements on the same diagonal
            col[rowIndex + colIndex + 1] := div_pFunc(subFunc(col[rowIndex + colIndex + 1], col[rowIndex + 1]));
        end for;
    end for;
    return res;
end function;

// Our digit extraction algorithm
// This procedure is only briefly mentioned in the paper and discussed in more detail in our
// work on polynomial functions modulo p^e and faster bootstrapping for homomorphic encryption
function OurDigitExtraction(u, p, e, v, addFunc, subFunc, mulFunc, div_pFunc, lowestDigitRetainPolynomials)
    // Populate the triangle with digits
    // Less memory is needed if only one column and the result are stored
    col := [u : i in [1..v]];   // Current column of the upper left triangle
    res := u;                   // Result of the digit extraction
    for rowIndex := 0 to v - 1 do
        exponent := 1; polynomials := []; precisions := [];
        triangleSize := v - rowIndex; rowSize := e - rowIndex;
        while 2 ^ (exponent - 1) lt triangleSize do
            // Compute desired precision
            precision := 2 ^ exponent;
            if precision gt triangleSize then     // If we are outside small triangle already
                if precision lt rowSize then      // If we did not yet reach the entire row size
                    precision := triangleSize;
                else
                    precision := rowSize;
                end if;
            end if;
            
            // Append the desired polynomial to the list
            Append(~polynomials, lowestDigitRetainPolynomials[precision]);
            Append(~precisions, precision);
            
            // Increase exponent for next iteration
            exponent +:= 1;
        end while;

        // Possibly add one more polynomial
        if (precisions eq [] or precisions[#precisions] lt rowSize) then
            Append(~polynomials, lowestDigitRetainPolynomials[rowSize]);
            Append(~precisions, rowSize);
        end if;

        // Extract digits via baby-step/giant-step
        digits := PolyEval(polynomials, col[rowIndex + 1], addFunc, mulFunc);

        // Determine starting values for next rows based on the necessary precision
        for nextRow := rowIndex + 1 to v - 1 do  // Update next rows with the result from above
            // Loop over the result from polynomial evaluation
            for index := 1 to #precisions do
                if precisions[index] + rowIndex ge nextRow + 1 then  // Compare precisions
                    col[nextRow + 1] := div_pFunc(subFunc(col[nextRow + 1], digits[index]));
                    break;
                end if;
            end for;
        end for;

        // Also update the final result
        res := div_pFunc(subFunc(res, digits[#digits]));
    end for;
    return res;
end function;