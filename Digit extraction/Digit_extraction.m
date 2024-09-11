load "Digit extraction/Arithmetic.m";
load "Digit extraction/Poly_eval.m";

// Return the lifting polynomial with respect to the parameters p and e
function GetLiftingPolynomial(p, e)
    // First calculate output of the fi polynomials
    digits := [[((Z!((Integers(p ^ (i + 1))!z0) ^ p)) div (p ^ i)) mod p : i in [1..e]] : z0 in [0..p - 1]];

    // Then construct them based on Newton interpolation
    ring := Integers(p ^ (e + 1)); poly_ring<y> := PolynomialRing(ring);
    full_factor := &*[poly_ring | x - xi : xi in {0..p - 1}];
    polynomials := [poly_ring | ];
    for i := 1 to e do
        tmp := 0;
        for z0 := 0 to p - 1 do
            tmp +:= (full_factor div (y - z0)) * Modinv(Z!(&*[ring | z0 - xi : xi in {0..p - 1} diff {z0}]), p ^ e)
                                               * digits[z0 + 1][i];
        end for;
        Append(~polynomials, tmp);
    end for;
    
    // Return the lifting polynomial
    poly := y ^ p - &+[polynomials[i] * (p ^ i) : i in [1..e]];
    return Zx!(Evaluate(poly, y + ((p - 1) div 2)) - ((p - 1) div 2));
end function;

// Return the lowest digit removal polynomial with respect to the parameters p and e
function GetLowestDigitRemovalPolynomial(p, e)
    degree := (p - 1) * (e - 1) + 1;
    forward_differences := [Z | p eq 2 select index - (index mod 2) else
                                              index - (Z!CenteredReduction(index, p)) : index in [0..degree]];

    // Compute forward differences
    for iteration := 1 to degree do
        for index := 0 to degree - iteration do
            forward_differences[degree - index + 1] -:= forward_differences[degree - index];
            forward_differences[degree - index + 1] := forward_differences[degree - index + 1] mod (p ^ e);
        end for;
    end for;

    // Compute result modulo p ^ e
    ring := Integers(p ^ e); poly_ring<y> := PolynomialRing(ring);
    factor := 1; poly := 0;
    prod := 1; p_factors := 1;
    for index := 1 to degree + 1 do
        poly +:= (forward_differences[index] div p_factors) * Modinv(prod, p ^ e) * factor;
        factor *:= (y - index + 1);
        prod := ((prod * index) div (p ^ Valuation(index, p))) mod (p ^ e);
        p_factors *:= p ^ Valuation(index, p);
    end for;
    return Zx!poly;
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

// Return the lowest digit removal polynomial modulo p ^ 2 over the bounded range [-B, B]
function GetLowestDigitRemovalPolynomialOverRange(p, B)
    base_ring := Integers(p ^ 2);
    poly_ring<x> := PolynomialRing(base_ring);
    base_poly := &*[x - index : index in [-B..B]];
    func_ring<y> := quo<poly_ring | base_poly ^ 2>;

    // Compute result by iteration
    result := 0;
    for index := -B to B do
        result +:= index * (1 - (((y - index) ^ p) ^ (p - 1)));
    end for;

    // Convert digit retain to digit removal polynomial
    return Zx!((poly_ring!(y - result)) mod (p * base_poly));
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
function OurDigitExtraction(u, e, v, addFunc, subFunc, mulFunc, div_pFunc, lowestDigitRetainPolynomials)
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

// Digit extraction algorithm over bounded range
// This is the algorithm from Ma et al. for e = 2 and p > 2
function BoundedRangeDigitExtraction(u, addFunc, mulFunc, div_pFunc, lowestDigitRemovalPolynomialOverRange)
    return div_pFunc(PolyEval(lowestDigitRemovalPolynomialOverRange, u, addFunc, mulFunc));
end function;