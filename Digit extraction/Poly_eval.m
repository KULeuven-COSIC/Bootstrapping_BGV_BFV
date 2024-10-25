// This file implements the baby-step/giant-step algorithm for evaluating a polynomial of degree at least 1
//--------------------------

// Check if the given input is a sequence of polynomials already
// If the input is a single polynomial, we return a sequence containing it
// Convert the given polynomial to a sequence if it is not a sequence already
function IsPolynomialSequence(polynomials)
    isSequence := true;
    if Category(polynomials) eq RngUPolElt then
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

// Preprocessing for polynomial evaluation
// Evaluate x^spacing using repeated square and multiply
// Compute updated polynomials accordingly
function PolyEvalPreprocessing(polynomials, element, mulFunc, sanitizeFunc)
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
        polynomials[poly_index] := Parent(polynomials[poly_index])!new_seq;
    end for;

    // Remaining polynomials and evaluation result
    return polynomials, result;
end function;

// Recursive part of baby-step/giant-step algorithm
// Splitting in three subpolynomials is not implemented
// If allowed_depth is set to zero, the parameter is ignored
function PolyEvalRecursive(coeff, xExp1, xExp2, addFunc, mulFunc, m, k, allowed_depth)
    // Base cases
    if #coeff eq 0 then
        return Universe(coeff)!0;
    elif m eq 0 then
        if (allowed_depth gt 0) and (Ceiling(Log(2, #coeff)) + 1 gt allowed_depth) then
            // Recursive case (only for optimal depth)
            index := FloorPowerOfTwo(#coeff);       // Index for splitting up sequence
            rec1 := PolyEvalRecursive(coeff[1..index], xExp1, xExp2, addFunc, mulFunc, m, k, 0);
            rec2 := PolyEvalRecursive(coeff[index + 1..#coeff], xExp1, xExp2, addFunc, mulFunc, m, k, allowed_depth - 1);
            return (index lt #coeff) select addFunc(rec1, mulFunc(rec2, xExp1[index])) else rec1;
        else
            result := Universe(coeff)!0;
            for index := 1 to #coeff do             // Inner loop: baby step
                if coeff[index] ne 0 then
                    result := addFunc(result, mulFunc(coeff[index], xExp1[index]));
                end if;
            end for;
            return result;
        end if;
    end if;

    // Recursive case
    index := Minimum(k * 2 ^ (m - 1), #coeff);      // Index for splitting up sequence
    rec1 := PolyEvalRecursive(coeff[1..index], xExp1, xExp2, addFunc, mulFunc, m - 1, k, allowed_depth);
    rec2 := PolyEvalRecursive(coeff[index + 1..#coeff], xExp1, xExp2, addFunc, mulFunc, m - 1, k, allowed_depth - 1);
    return (index lt #coeff) select addFunc(rec1, mulFunc(rec2, xExp2[m])) else rec1;
end function;

// Evaluate the given polynomials in the given element using the given parameters
// This function does not implement preprocessing of the polynomials
function PolyEvalGivenParameters(polynomials, element, addFunc, mulFunc, sanitizeFunc, optimal_depth, m, k, odd:
                                 is_ciphertext := false)
    // Precompute x ^ exp with exp = 1, ..., k
    xExp1 := [element];
    for exp := 2 to k do
        // Choose indices such that the depth is as low as possible
        if odd and (exp mod 2) eq 0 then
            if IsPowerOfTwo(exp) or ((exp eq k) and (exp mod 4 eq 2)) then
                ind1 := exp div 2;
            elif exp eq k then
                ind1 := (exp div 2) - 1;
            else
                continue;
            end if;
        else
            ind1 := FloorPowerOfTwo(exp - 1);
        end if;

        // Compute actual multiplication
        ind2 := exp - ind1;
        xExp1[ind1] := sanitizeFunc(xExp1[ind1]);
        xExp1[ind2] := sanitizeFunc(xExp1[ind2]);
        xExp1[exp] := mulFunc(xExp1[ind1], xExp1[ind2]);
    end for;

    // Sanitize result for giant step
    if m ne 0 then
        xExp1[#xExp1] := sanitizeFunc(xExp1[#xExp1]);
    end if;

    // Precompute x ^ exp with exp = k, 2 * k, ..., (2 ^ (m - 1)) * k
    xExp2 := [xExp1[#xExp1]];
    if (Category(CoefficientRing(Parent(polynomials[1]))) ne RngIntElt) and IsCiphertext(element) and is_ciphertext then
        xExp2[1] := CopyCiphertext(xExp2[1]);   // Ciphertext belongs to two arrays and should be in different domain
    end if;
    for exp := 1 to m - 1 do
        Append(~xExp2, sanitizeFunc(mulFunc(xExp2[exp], xExp2[exp])));
    end for;

    // Return result via sequence of recursive calls
    coeffs := [Eltseq(polynomial) : polynomial in polynomials];
    return [sanitizeFunc(addFunc(coeff[1], PolyEvalRecursive(coeff[2..#coeff], xExp1, xExp2, addFunc, mulFunc, m, k,
                                                             optimal_depth select Ceiling(Log(2, #coeff)) else 0))) :
                                                             coeff in coeffs];
end function;

// Return the parameters that lead to the smallest number of non-scalar multiplications
// Degree of the polynomials is at most spacing * k * (2 ^ m)
function GetBestParameters(polynomials: lazy := false, optimal_depth := false)
    // We should have a list of polynomials
    _, polynomials := IsPolynomialSequence(polynomials);

    // Degrees should be positive
    for polynomial in polynomials do
        if Degree(polynomial) le 0 then
            error "Degrees should be positive.";
        end if;
    end for;

    // Spacing and preprocessing
    spacing := GetSpacing(polynomials);
    polynomials, tmp := PolyEvalPreprocessing(polynomials, <{Z | }, true>, mulCountFunc, func<x | x>);

    // Check whether polynomials are odd and compute maximum degree
    odd := AreOddPolynomials(polynomials);
    d := Maximum([Degree(polynomial) : polynomial in polynomials]);

    // Take generic polynomials to count number of multiplications
    // This is to ensure that we don't miss any multiplications
    ring := Parent(polynomials[1]);
    oddPolynomials := [&+[ring | (ring.1)^(2 * i + 1) : i in [0..Degree(polynomial) div 2]] : polynomial in polynomials];
    fullPolynomials := [&+[ring | (ring.1)^i : i in [0..Degree(polynomial)]] : polynomial in polynomials];

    // Compute best set of parameters by iteration
    bestM := 0;
    bestK := 0;
    bestOdd := false;
    bestMultiplications := -1;
    for m := 0 to Ceiling(Log(2, d)) do
        k_min := Ceiling(d / (2 ^ m));
        k_max := Minimum(Maximum(CeilPowerOfTwo(k_min), 2), k_min + 9);     // Limited search space: at most 10 options
        for k := k_min to k_max do
            for currentOdd in {false} join {odd} do
                // Odd evaluation algorithm uses even value of k
                if currentOdd and (k mod 2 eq 1) then
                    continue;
                end if;

                // Compute number of operations and depth
                res := PolyEvalGivenParameters(currentOdd select oddPolynomials else fullPolynomials, tmp, addCountFunc,
                                               lazy select mulLazyCountFunc else mulCountFunc,
                                               lazy select relinCountFunc else func<x | x>, optimal_depth, m, k, currentOdd);

                // Check whether the parameters are better than the current best ones
                currentMultiplications := #(&join[el[1] : el in res]);
                if (bestMultiplications eq -1) or (currentMultiplications lt bestMultiplications) then
                    bestM := m;
                    bestK := k;
                    bestOdd := currentOdd;
                    bestMultiplications := currentMultiplications;
                end if;
            end for;
        end for;
    end for;
    return bestM, bestK, bestOdd, spacing, bestMultiplications;
end function;

// Evaluate the given polynomials in the given element
// Both addFunc and mulFunc must be able to evaluate expressions with scalar and non-scalar operands
// This function uses the optimal depth algorithm if the optimal_depth flag is set to true
// This function can also execute the lazy baby-step/giant-step algorithm if
// - The lazy flag is set to true
// - An appropriate mulFunc is passed
// - An appropriate sanitizer is passed
function PolyEval(polynomials, element, addFunc, mulFunc: sanitizeFunc := func<x | x>, lazy := false, optimal_depth := false)
    // We should have a list of polynomials
    isSequence, polynomials := IsPolynomialSequence(polynomials);

    // Degrees should be positive
    for polynomial in polynomials do
        if Degree(polynomial) le 0 then
            error "Degrees should be positive.";
        end if;
    end for;

    if (Category(CoefficientRing(Parent(polynomials[1]))) eq RngIntElt) and IsCiphertext(element) then
        SetOptimalCoefficientDomain();
    end if;

    // Compute preprocessing step and find best parameters for remaining polynomials
    polynomials, element := PolyEvalPreprocessing(polynomials, element, mulFunc, sanitizeFunc);
    m, k, odd := GetBestParameters(polynomials: lazy := lazy, optimal_depth := optimal_depth);

    // Return single element if the polynomial was given in this format
    result := PolyEvalGivenParameters(polynomials, element, addFunc, mulFunc, sanitizeFunc, optimal_depth, m, k, odd:
                                      is_ciphertext := true);

    if (Category(CoefficientRing(Parent(polynomials[1]))) eq RngIntElt) and IsCiphertext(element) then
        SetOptimalNTTDomain();
    end if;

    return isSequence select result else result[1];
end function;