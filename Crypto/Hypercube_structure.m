// This file stores some functions related to the hypercube structure
//--------------------------

// Make sure that we have a valid factorization for the powerful basis ring
factors_m := factors_m eq [] select PrimePowerFactorization(m) else factors_m;
assert IsCoprimeFactorization(m, factors_m);
assert not usePowerOfTwo or IsPowerOfTwo(m);

// Function that decides which version of the linear transformations will be used for thin bootstrapping
// - Return value 1: HElib version
// - Return value 2: SEAL version
// - Return value 3: our version
// - Return value 0: building (bootstrappable) hypercube is not possible
forward AreBootstrappableAnyOrder;
function GetLTVersion()
    if (GCD(m, p) ne 1) or (not IsPrime(p)) then
        return 0;                       // No hypercube possible
    elif not usePowerOfTwo then                     
        if AreBootstrappableAnyOrder(p, m, factors_m) then
            return 1;                   // HElib hypercube
        else
            return 0;                   // No bootstrappable hypercube possible
        end if;
    elif mat_dimensions eq [] then
        return 2;                       // SEAL hypercube
    else
        return 3;                       // Our hypercube
    end if;
end function;

// Get a set S of representatives of (Z/mZ)*/<p>
// Also return the orders of the elements s_i of S in (Z/mZ)* and in (Z/mZ)*/<p, s_1, ..., s_{i-1}>
// Note: this function cannot be used for creating a bootstrappable hypercube structure
function GetHypercubeStructure(p, m)
    S := [];            // Representatives of the group (Z/mZ)*/<p>
    orders := [];       // Sequence of <n1, n2> with n1 the order in (Z/mZ)* and n2 the order in (Z/mZ)*/<p, s_1, ..., s_{i-1}>

    // Current quotient group
    Zm := Integers(m);
    Zm_star, Zm_starToZm := UnitGroup(Zm);
    quotientGroup, Zm_starToQuotientGroup := quo<Zm_star | (Zm_starToZm ^ (-1))(p)>;
    while #quotientGroup ne 1 do
        bestQuotientOrder := 0;
        bestGoodDimension := false;
        for Zm_starElement in Zm_star do
            ZElement := Z!Zm_starToZm(Zm_starElement);                      // Representation of Zm_starElement in Z
            quotientGroupElement := Zm_starToQuotientGroup(Zm_starElement); // Representation of Zm_starElement in quotientGroup

            Zm_starOrder := Order(Zm_starElement);                          // Order of current element in Zm_star
            quotientOrder := Order(quotientGroupElement);                   // Order of current element in quotientGroup
            goodDimension := (Zm_starOrder eq quotientOrder);
            // Check if this element is better then the current best one
            if (quotientOrder gt 1) and ((goodDimension and not bestGoodDimension) or
                                        ((goodDimension eq bestGoodDimension) and (quotientOrder gt bestQuotientOrder))) then
                bestZElement := ZElement;                                   // Representation in Z
                bestQuotientGroupElement := quotientGroupElement;           // Representation in quotientGroup

                bestZm_starOrder := Zm_starOrder;                           // Order in Zm_star
                bestQuotientOrder := quotientOrder;                         // Order in quotientGroup
                bestGoodDimension := goodDimension;
            end if;
        end for;
        
        // Update result
        Append(~S, bestZElement);
        Append(~orders, <bestZm_starOrder, bestQuotientOrder>);

        // Update current quotient group
        quotientGroup, mapping := quo<quotientGroup | bestQuotientGroupElement>;    // Update quotient group
        Zm_starToQuotientGroup := Zm_starToQuotientGroup * mapping;                 // Update corresponding map
    end while;

    return S, orders;
end function;

// Check whether the given parameters are bootstrappable
function AreBootstrappable(p, m, factors_m)
    // Only valid if there are slots
    if (GCD(m, p) ne 1) or (not IsPrime(p)) then
        return false;
    end if;

    // Compute degree d of irreducible factors
    Zm := Integers(m);
    d := Order(Zm!p);

    // Compute parameters for quotient group
    Zmi := Integers(factors_m[1]);
    Zmi_star, Zmi_starToZmi := UnitGroup(Zmi);
    p_star := (Zmi_starToZmi ^ (-1))(p);

    // Check if the orders are the same and the quotient group is cyclic
    if (Order(Zmi!p) eq d) and IsCyclic(quo<Zmi_star | p_star>) then
        for j := 2 to #factors_m do
            // Group should be cyclic
            if not IsCyclic(UnitGroup(Integers(factors_m[j]))) then
                return false;
            end if;
        end for;
        return true;
    end if;
    return false;
end function;

// Check whether the given parameters are bootstrappable in case we are allowed to change their order
// Also return the new factorization order by swapping index 1 and i for the lowest possible i
function AreBootstrappableAnyOrder(p, m, factors_m)
    for index := 1 to #factors_m do
        new_factors_m := Swap(factors_m, 1, index);
        if AreBootstrappable(p, m, new_factors_m) then
            return true, new_factors_m;
        end if;
    end for;
    return false;
end function;

// Compute the hypercube structure based on the given parameters that are bootstrappable
function GetHElibHypercubeStructure(p, m, factors_m)
    // Compute degree d of irreducible factors
    Zm := Integers(m);
    d := Order(Zm!p);

    // Compute elements of S
    S := [];                // Representatives of the group (Z/mZ)*/<p>
    orders := [];           // Sequence of <n1, n2> with n1 the order in (Z/mZ)* and n2 the order in (Z/mZ)*/<p, s_1, ..., s_{i-1}>
    d_prod := 1;            // Current product of factors of d
    for index := 1 to #factors_m do
        // Compute parameters for quotient group
        Zmi := Integers(factors_m[index]);
        Zmi_star, Zmi_starToZmi := UnitGroup(Zmi);
        pd_star := (Zmi_starToZmi ^ (-1))((Zmi!p) ^ d_prod);
        quotientGroup, mapping := quo<Zmi_star | pd_star>;
        generators := Generators(quotientGroup);
        generator := ((#generators eq 0) select 1 else Zmi_starToZmi((mapping ^ (-1))(Random(generators))));

        // Compute next dimension of hypercube structure
        Append(~S, CRT([Z | i eq index select generator else 1 : i in [1..#factors_m]], factors_m));
        Append(~orders, <Order(Zm!S[#S]), EulerPhi(factors_m[index]) div (d div d_prod)>);

        // d_prod eq d for all iterations except for the first one
        d_prod := d;
    end for;
    return S, orders;
end function;

// Compute a hypercube structure that can be used for bootstrapping power-of-two cyclotomics
function GetSEALHypercubeStructure(p, m)
    S := [];            // Representatives of the group (Z/mZ)*/<p>
    orders := [];       // Sequence of <n1, n2> with n1 the order in (Z/mZ)* and n2 the order in (Z/mZ)*/<p, s_1, ..., s_{i-1}>

    // Current quotient group
    Zm := Integers(m);
    Zm_star, Zm_starToZm := UnitGroup(Zm);
    quotientGroup, Zm_starToQuotientGroup := quo<Zm_star | (Zm_starToZm ^ (-1))(p)>;
    if #quotientGroup ne 1 then
        bestDivTwo := Valuation(0, 2);
        for Zm_starElement in Zm_star do
            ZElement := Z!Zm_starToZm(Zm_starElement);                      // Representation of Zm_starElement in Z
            quotientGroupElement := Zm_starToQuotientGroup(Zm_starElement); // Representation of Zm_starElement in quotientGroup

            Zm_starOrder := Order(Zm_starElement);                          // Order of current element in Zm_star
            quotientOrder := Order(quotientGroupElement);                   // Order of current element in quotientGroup
            divTwo := Valuation(ZElement - 1, 2);                           // Number of times the element is divisble by 2
            // Check if this element is better then the current best one
            if (quotientOrder eq 2) and (divTwo lt bestDivTwo) and IsCyclic(quo<quotientGroup | quotientGroupElement>) then
                bestZElement := ZElement;                                   // Representation in Z
                bestQuotientGroupElement := quotientGroupElement;           // Representation in quotientGroup

                bestZm_starOrder := Zm_starOrder;                           // Order in Zm_star
                bestQuotientOrder := quotientOrder;                         // Order in quotientGroup
                bestDivTwo := divTwo;
            end if;
        end for;

        // Update result
        Append(~S, bestZElement);
        Append(~orders, <bestZm_starOrder, bestQuotientOrder>);

        // Update current quotient group
        quotientGroup, mapping := quo<quotientGroup | bestQuotientGroupElement>;    // Update quotient group
        Zm_starToQuotientGroup := Zm_starToQuotientGroup * mapping;                 // Update corresponding map
    end if;

    // Remaining quotient group is cyclic
    if #quotientGroup ne 1 then
        quotientGroupElement := Random(Generators(quotientGroup));
        Zm_starElement := (Zm_starToQuotientGroup ^ (-1))(quotientGroupElement);
        ZElement := Z!Zm_starToZm(Zm_starElement);

        Zm_starOrder := Order(Zm_starElement);
        quotientOrder := Order(quotientGroupElement);

        // Update result
        Append(~S, ZElement);
        Append(~orders, <Zm_starOrder, quotientOrder>);
    end if;

    return S, orders;
end function;

// Compute a hypercube structure that can be used for bootstrapping power-of-two cyclotomics
// The variable mat_dimensions indicates the dimensions of the FFT-like matrices
function GetOurHypercubeStructure(p, m, mat_dimensions)
    // Product of matrix dimensions should be equal to number of slots
    assert &*mat_dimensions eq m div (2 * Order(Integers(m)!p));

    // Half of first matrix dimension is used by representative -1
    if p mod 4 eq 1 then
        if mat_dimensions[1] lt 2 then
            error "To facilitate the implementation, the first matrix dimension must be greater than 1.";
        end if;
        mat_dimensions[1] div:= 2;
    end if;

    // Generators that are powers of 5
    S := [(5 ^ (&*mat_dimensions[1..index - 1])) mod m : index in [1..#mat_dimensions]];
    orders := [<m div (4 * (&*mat_dimensions[1..index - 1])), mat_dimensions[index]> : index in [1..#mat_dimensions]];

    // Optionally add generator -1
    if p mod 4 eq 1 then
        return S cat [-1], orders cat [<2, 2>];
    else
        return S, orders;
    end if;
end function;



// Only build hypercube structure if it is possible to do so
if (GCD(m, p) eq 1) and IsPrime(p) then
    // Info for plaintext space and slots
    d := Order(Zm!p); l := n div d;

    // Build special hypercube structure depending on the parameters
    if GetLTVersion() eq 1 then
        _, factors_m := AreBootstrappableAnyOrder(p, m, factors_m);
        S, orders := GetHElibHypercubeStructure(p, m, factors_m);
    elif GetLTVersion() eq 2 then
        S, orders := GetSEALHypercubeStructure(p, m);
    elif GetLTVersion() eq 3 then
        S, orders := GetOurHypercubeStructure(p, m, mat_dimensions);
    elif GetLTVersion() eq 0 then
        S, orders := GetHypercubeStructure(p, m);
        "Warning: hypercube structure is not bootstrappable.";
    end if;
else
    // These variables are useless
    d := 0; l := 0; S := []; orders := [];
    "Warning: building hypercube structure is not possible.";
end if;