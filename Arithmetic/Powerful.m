// Convert the given element of the power basis to the powerful basis
function PolynomialToPowerfulBasis(element, factors_m)
    // Set up necessary data structures
    cyclotomicPolynomials := [Zx | CyclotomicPolynomial(factor) : factor in factors_m];
    Zxi := PolynomialRing(Z, #factors_m);
    res := Zxi!0;

    // Parameters for conversion
    k := &+[m div factors_m[index] : index in [1..#factors_m]];
    l := Modinv(k, m);

    // Iterate over each monomial and compute the value in the powerful basis
    seq := Eltseq(element);
    for index := 1 to #seq do
        res +:= seq[index] * (&*[Evaluate((x ^ ((l * (index - 1)) mod factors_m[var]))
                                 mod cyclotomicPolynomials[var], Zxi.var) : var in [1..#factors_m]]);
    end for;
    return res;
end function;

// Convert the given element of the powerful basis to the power basis
function PowerfulBasisToPolynomial(element, factors_m)
    return Evaluate(element, [x ^ (m div factor) : factor in factors_m]) mod f;
end function;

// Return the sum of the basis elements of the powerful basis
function SumPowerfulBasis(factors_m)
    m := &*factors_m; res := Zx!0;
    for index := 1 to m do
        seq_index := IndexToSequence(index, factors_m); value := 1;
        for ind := 1 to #seq_index do
            if seq_index[ind] ge EulerPhi(factors_m[ind]) then
                value := 0;
            end if;
        end for;
        res +:= value * (x ^ (&+[seq_index[ind] * (m div factors_m[ind]) : ind in [1..#seq_index]]));
    end for;
    return res mod f;
end function;