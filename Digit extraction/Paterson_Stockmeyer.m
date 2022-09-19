// This file implements the Paterson-Stockmeyer algorithm for evaluating a polynomial of degree at least 1
//--------------------------

// Return the parameters that lead to the smallest number of non-constant multiplications
// Degree of the polynomial is at least k * (2 ^ m)
function GetBestParameters(polynomials: lazy := false)
    // We should have a list of polynomials
    if Category(polynomials) eq Category(Zx!0) then
        polynomials := [polynomials];
    end if;

    d := 0;     // Store the degree
    for polynomial in polynomials do
        d := Maximum(d, Degree(polynomial));    // Compute maximum degree
        if Degree(polynomial) le 0 then
            error "Degrees should be positive.";
        end if;
    end for;

    // Compute best set of parameters by iteration
    bestM := 0;
    bestK := 0;
    bestMultiplications := -1;
    for m := 0 to Ceiling(Log(2, d)) do
        // Compute corresponding k parameter and number of multiplications
        k := Ceiling(d / (2 ^ m));
        if lazy then
            if k eq 1 then
                nbMultiplications := m - 1;
            else
                nbMultiplications := ((k - 1) div 2) + m;
            end if;
        else
            if m eq 0 then
                nbMultiplications := k - 1;
            else
                nbMultiplications := k + m - 2;
            end if;

            // Subtract one for each polynomial
            nbMultiplications -:= #polynomials;
        end if;

        // Add extra number for giant step
        for polynomial in polynomials do
            nbMultiplications +:= Ceiling(Degree(polynomial) / k);
        end for;

        // Check whether the parameters are better than the current best ones
        if (bestMultiplications eq -1) or (nbMultiplications lt bestMultiplications) then
            bestM := m;
            bestK := k;
            bestMultiplications := nbMultiplications;
        end if;
    end for;
    return bestM, bestK, bestMultiplications;
end function;

// Recursive part of Paterson-Stockmeyer algorithm
function PatersonStockmeyerRecursive(coeff, xExp1, xExp2, addFunc, mulFunc, m, k)
    // Base cases
    if #coeff eq 0 then
        return Universe(coeff)!0;
    elif m eq 0 then
        result := Universe(coeff)!0;
        for index := 1 to #coeff do  // Inner loop: baby step
            result := addFunc(result, mulFunc(coeff[index], xExp1[index]));
        end for;
        return result;
    end if;

    // Recursive case
    index := Minimum(k * 2 ^ (m - 1), #coeff);      // Index for splitting up sequence
    rec1 := PatersonStockmeyerRecursive(coeff[1..index], xExp1, xExp2, addFunc, mulFunc, m - 1, k);
    rec2 := PatersonStockmeyerRecursive(coeff[index + 1..#coeff], xExp1, xExp2, addFunc, mulFunc, m - 1, k);
    return addFunc(rec1, mulFunc(rec2, xExp2[m]));
end function;

// Evaluate the given polynomials in the given element: the algorithm is optimized for lowest number of
// multiplications since the depth is already optimal (counting only non-scalar multiplications)
// Both addFunc and mulFunc must be able to evaluate expressions with constant and non-constant operands
// This function can also execute the lazy baby-step/giant-step algorithm if
// - The lazy flag is set to true
// - An appropriate mulFunc is passed
// - An appropriate santizer is passed
function PatersonStockmeyer(polynomials, element, addFunc, mulFunc: lazy := false, sanitizeFunc := func<x | x>)
    // We should have a list of polynomials
    isSinglePoly := false;
    if Category(polynomials) eq Category(Zx!0) then
        isSinglePoly := true;   // Make sure we can return the result as a single polynomial
        polynomials := [polynomials];
    end if;

    // Degrees should be positive
    for polynomial in polynomials do
        if Degree(polynomial) le 0 then
            error "Degrees should be positive.";
        end if;
    end for;

    // Determine the parameters
    m, k := GetBestParameters(polynomials: lazy := lazy);

    // Precompute x ^ exp with exp = 1, ..., k
    xExp1 := [element];
    for exp := 2 to k do
        if (exp mod 2) eq 0 then
            xExp1[exp div 2] := sanitizeFunc(xExp1[exp div 2]);
            Append(~xExp1, mulFunc(xExp1[exp div 2], xExp1[exp div 2]));
        else
            // Choose indices such that the depth is as low as possible
            ind1 := exp div 2;
            ind2 := exp - ind1;

            xExp1[ind1] := sanitizeFunc(xExp1[ind1]);
            xExp1[ind2] := sanitizeFunc(xExp1[ind2]);
            Append(~xExp1, mulFunc(xExp1[ind1], xExp1[ind2]));
        end if;
    end for;

    // Sanitize result for giant step
    if m ne 0 then
        xExp1[#xExp1] := sanitizeFunc(xExp1[#xExp1]);
    end if;

    // Precompute x ^ exp with exp = k, 2 * k, ..., (2 ^ (m - 1)) * k
    xExp2 := [xExp1[#xExp1]];
    for exp := 1 to m - 1 do
        Append(~xExp2, sanitizeFunc(mulFunc(xExp2[exp], xExp2[exp])));
    end for;

    // Return result via sequence of recursive calls
    coeffs := [Eltseq(polynomial) : polynomial in polynomials];
    result := [sanitizeFunc(addFunc(coeff[1], PatersonStockmeyerRecursive(coeff[2..#coeff], xExp1, xExp2, addFunc,
                                                                          mulFunc, m, k))) : coeff in coeffs];

    // Return single element if the polynomial was given in this format
    if isSinglePoly then
        return result[1];
    else
        return result;
    end if;
end function;