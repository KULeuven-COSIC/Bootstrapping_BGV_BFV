// This file stores some functions related to the hypercube structure
//--------------------------
load "CRT/CRT.m";

// Get a set S of representatives of (Z/mZ)*/<p>
// Also return the orders of the elements s_i of S in (Z/mZ)* and in (Z/mZ)*/<p, s_1, ..., s_i-1>
// Note: this function cannot be used for creating a bootstrappable hypercube structure
function GetHypercubeStructure(p, m)
    S := [];            // Representatives of the group (Z/mZ)*/<p>
    orders := [];       // Sequence of <n1, n2> with n1 the order in (Z/mZ)* and n2 the order in (Z/mZ)*/<p, s_1, ..., s_i-1>

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
    if GCD(m, p) ne 1 then
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
function GetBootstrappableHypercubeStructure(p, m, factors_m)
    // Compute degree d of irreducible factors
    Zm := Integers(m);
    d := Order(Zm!p);

    // Compute elements of S
    S := [];                // Representatives of the group (Z/mZ)*/<p>
    orders := [];           // Sequence of <n1, n2> with n1 the order in (Z/mZ)* and n2 the order in (Z/mZ)*/<p, s_1, ..., s_i-1>
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
function GetPowerOfTwoHypercubeStructure(p, m)
    S := [];            // Representatives of the group (Z/mZ)*/<p>
    orders := [];       // Sequence of <n1, n2> with n1 the order in (Z/mZ)* and n2 the order in (Z/mZ)*/<p, s_1, ..., s_i-1>

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



// Make sure that we have a valid factorization for the powerful basis ring
factors_m := factors_m eq [] select PrimeSquareFactorization(m) else factors_m;
assert IsCoprimeFactorization(m, factors_m);

// Only build hypercube structure if it is possible to do so
if GCD(m, p) eq 1 then
    // Info for plaintext space and slots
    d := Order(Zm!p); l := n div d;

    // Build special hypercube structure depending on the parameters
    if usePowerOfTwo then
        assert IsPowerOfTwo(m);
        S, orders := GetPowerOfTwoHypercubeStructure(p, m);
    elif AreBootstrappableAnyOrder(p, m, factors_m) then
        _, factors_m := AreBootstrappableAnyOrder(p, m, factors_m);
        S, orders := GetBootstrappableHypercubeStructure(p, m, factors_m);
    else
        S, orders := GetHypercubeStructure(p, m);
        "Warning: hypercube structure is not bootstrappable.";
    end if;
else
    // These variables are useless
    d := 0; l := 0; S := []; orders := [];
    "Warning: building hypercube structure is not possible.";
end if;