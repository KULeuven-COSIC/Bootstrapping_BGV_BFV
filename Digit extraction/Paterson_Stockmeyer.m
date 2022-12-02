// This file implements the Paterson-Stockmeyer algorithm for evaluating a polynomial of degree at least 1
//--------------------------

// Check if the given input is a sequence of polynomials already
// If the input is a single polynomial, we return a sequence containing it
// Convert the given polynomial to a sequence if it is not a sequence already
function IsPolynomialSequence(polynomials)
    isSequence := true;
    if Category(polynomials) eq Category(Zx!0) then
        isSequence := false;
        polynomials := [polynomials];
    end if;
    return isSequence, polynomials;
end function;

// Compute the common spacing of the given polynomials, i.e., the largest value of n
// such that we have poly = f(x^n) for some polynomial f(x)
function GetSpacing(polynomials)
    // We should have a list of polynomials
    _, polynomials := IsPolynomialSequence(polynomials);

    // Compute the actual spacing
    spacing := Degree(polynomials[1]);
    for polynomial in polynomials do
        lastNonZeroIndex := 1;
        seq := Eltseq(polynomial);
        for index := 2 to #seq do
            if seq[index] ne 0 then
                spacing := GCD(spacing, index - lastNonZeroIndex);
                lastNonZeroIndex := index;
            end if;
        end for;
    end for;
    return spacing;
end function;

// Check if the given sequence of polynomials is odd
function AreOddPolynomials(polynomials)
    // We should have a list of polynomials
    _, polynomials := IsPolynomialSequence(polynomials);

    // Check if each individual polynomial is odd
    for polynomial in polynomials do
        seq := Eltseq(polynomial);
        for index := 1 to #seq do
            if (index mod 2 eq 1) and (seq[index] ne 0) then
                return false;
            end if;
        end for;
    end for;
    return true;
end function;

// Return the parameters that lead to the smallest number of non-constant multiplications
// Degree of the polynomial is at least k * (2 ^ m)
function GetBestParameters(polynomials: lazy := false)
    // We should have a list of polynomials
    _, polynomials := IsPolynomialSequence(polynomials);

    d := 0;     // Store the degree
    for polynomial in polynomials do
        d := Maximum(d, Degree(polynomial));    // Compute maximum degree
        if Degree(polynomial) le 0 then
            error "Degrees should be positive.";
        end if;
    end for;

    // Check if all polynomials are odd
    odd := AreOddPolynomials(polynomials);

    // Compute best set of parameters by iteration
    bestM := 0;
    bestK := 0;
    bestMultiplications := -1;
    bestOdd := false;
    for m := 0 to Ceiling(Log(2, d)) do
        // Compute corresponding k parameter and number of multiplications (start with baby step only)
        // Note that we cannot combine lazy rescaling with odd polynomials (different computation in the baby step)
        // --> Lazy rescaling is prioritized since it can be set as a flag in the parameter list
        k := Ceiling(d / (2 ^ m));
        currentOdd := false;
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

            // Possibly use different algorithm if polynomials are odd (only if operation count is better)
            if odd then
                k_odd := k;
                if m eq 0 then
                    nbMultiplicationsOdd := (k_odd div 2) + Floor(Log(2, k_odd));
                else
                    // The optimized procedure only works for even k
                    if (k_odd mod 2 eq 1) then
                        k_odd +:= 1;
                    end if;

                    // Make sure that we can always compute x^k as a product of two factors that were computed in the baby step
                    // This is done by multiplying x^e and x^d where either both e and d are odd or both are a power of 2
                    // Note that this is not always possible if k == 0 (mod 4) and we might have to increase k by 2
                    remaining_exponent := k_odd - FloorPowerOfTwo(k_odd - 1);
                    if ((k_odd mod 4 eq 0) and (not IsPowerOfTwo(remaining_exponent))) then
                        k_odd +:= 2;
                    end if;

                    // Now compute the actual number of multiplications
                    nbMultiplicationsOdd := (k_odd div 2) + Floor(Log(2, k_odd - 1)) + m - 1;
                end if;

                // Check if odd parameters are better
                if nbMultiplicationsOdd lt nbMultiplications then
                    k := k_odd;
                    nbMultiplications := nbMultiplicationsOdd;
                    currentOdd := true;
                end if;
            end if;
        end if;

        // Add extra number for giant step
        for polynomial in polynomials do
            nbMultiplications +:= (Ceiling(Degree(polynomial) / k) - 1);
            if lazy then    // One extra non-scalar multiplication in giant step
                nbMultiplications +:= 1;
                deg_mod := Degree(polynomial) mod k;    // One less non-scalar multiplication if baby step has only linear terms
                if deg_mod ne 0 and deg_mod le ((k + 1) div 2) then
                    nbMultiplications -:= 1;
                end if;
            end if;
        end for;

        // Check whether the parameters are better than the current best ones
        if (bestMultiplications eq -1) or (nbMultiplications lt bestMultiplications) then
            bestM := m;
            bestK := k;
            bestMultiplications := nbMultiplications;
            bestOdd := currentOdd;
        end if;
    end for;
    return bestM, bestK, bestMultiplications, bestOdd;
end function;

// Preprocessing for polynomial evaluation
// Evaluate x^spacing using repeated square and multiply
// Compute updated polynomials accordingly
function PatersonStockmeyerPreprocessing(element, polynomials, mulFunc, sanitizeFunc)
    _, polynomials := IsPolynomialSequence(polynomials);
    spacing := GetSpacing(polynomials);

    // Evaluate x^spacing
    // First compute appropriate powers
    xExp := [element];
    for index := 1 to Floor(Log(2, spacing)) do
        Append(~xExp, sanitizeFunc(mulFunc(xExp[index], xExp[index])));
    end for;

    // Then combine powers in a meaningful result
    emptyResult := true;
    bitSeq := IntegerToSequence(spacing, 2);
    for index := 1 to #bitSeq do
        if bitSeq[index] eq 1 then
            if emptyResult then
                result := xExp[index];
                emptyResult := false;
            else
                result := sanitizeFunc(mulFunc(result, xExp[index]));
            end if;
        end if;
    end for;

    // Compute updated polynomials
    for poly_index := 1 to #polynomials do
        old_seq := Eltseq(polynomials[poly_index]);
        new_seq := [];
        for index := 0 to Degree(polynomials[poly_index]) div spacing do
            Append(~new_seq, old_seq[index * spacing + 1]);
        end for;
        polynomials[poly_index] := Zx!new_seq;
    end for;

    // Remaining element and polynomials to use for evaluation
    return result, polynomials;
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
    isSequence, polynomials := IsPolynomialSequence(polynomials);

    // Degrees should be positive
    for polynomial in polynomials do
        if Degree(polynomial) le 0 then
            error "Degrees should be positive.";
        end if;
    end for;

    // Evaluate x^spacing and update polynomials accordingly
    // Also determine the optimal parameters for the remaining polynomials
    element, polynomials := PatersonStockmeyerPreprocessing(element, polynomials, mulFunc, sanitizeFunc);
    m, k, _, odd := GetBestParameters(polynomials: lazy := lazy);

    // Precompute x ^ exp with exp = 1, ..., k
    xExp1 := [element];
    for exp := 2 to k do
        if odd then
            if (exp mod 2) eq 0 then
                if IsPowerOfTwo(exp) or (exp eq k) then
                    ind1 := (exp mod 4 eq 0) select FloorPowerOfTwo(exp - 1) else (exp div 2);
                    ind2 := exp - ind1;
                    Append(~xExp1, mulFunc(xExp1[ind1], xExp1[ind2]));
                else
                    Append(~xExp1, xExp1[1]);   // Just append garbage
                end if;
            else
                ind1 := FloorPowerOfTwo(exp);
                ind2 := exp - ind1;
                Append(~xExp1, mulFunc(xExp1[ind1], xExp1[ind2]));
            end if;
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
    if isSequence then
        return result;
    else
        return result[1];
    end if;
end function;