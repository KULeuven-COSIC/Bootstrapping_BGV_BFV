// Compute the adapted constants for the baby-step/giant-step algorithm in a good dimension
function MatMul1DGoodDimensionAdaptedConstants(constants, dim, henselExponent)
    // Compute parameters
    dim_size := GetDimensionSize(dim);
    g, h := GetBabyGiantParams(dim_size);

    // Compute adapted constants
    adapted_constants := [];
    for k := 0 to h - 1 do
        for j := 0 to g - 1 do
            // Compute which constant to use
            i := j + g * k;
            if i ge dim_size then
                continue;
            end if;

            // Compute rotation
            rot_size := (-g * k) mod dim_size;
            Append(~adapted_constants, RotateSlotsPlaintext(constants[i + 1], dim, rot_size:
                                                            henselExponent := henselExponent));
        end for;
    end for;
    return adapted_constants;
end function;

// Compute the adapted constants for the baby-step/giant-step algorithm in a bad dimension
function MatMul1DBadDimensionAdaptedConstants(constants, dim, henselExponent)
    // Compute parameters
    dim_size := GetDimensionSize(dim);
    g, h := GetBabyGiantParams(dim_size);

    // Compute adapted constants
    adapted_constantsAhead := [];
    adapted_constantsBack := [];
    for k := 0 to h - 1 do
        for j := 0 to g - 1 do
            // Compute which constant to use
            i := j + g * k;
            if i ge dim_size then
                continue;
            end if;

            // Embed mask entries into slots
            maskAhead := GetAdaptedMaskAhead(dim, i, henselExponent);
            maskBack := GetAdaptedMaskBack(dim, i, henselExponent);

            // Compute automorphism
            hyperIndex := Get1DHyperIndex(dim, -g * k);
            Append(~adapted_constantsAhead, ApplyAutomorphismPlaintext(((maskAhead * constants[i + 1]) mod f)
                                                                         mod (p ^ henselExponent),
                                                                         hyperIndex: henselExponent := henselExponent));
            Append(~adapted_constantsBack, ApplyAutomorphismPlaintext(((maskBack * constants[i + 1]) mod f)
                                                                        mod (p ^ henselExponent),
                                                                        hyperIndex: henselExponent := henselExponent));
        end for;
    end for;
    return adapted_constantsAhead, adapted_constantsBack;
end function;

// Apply one-dimensional E-linear transformation to a ciphertext c in a good dimension
// All evaluation keys need to be provided, except for the trivial one
function MatMul1DGoodDimension(c, constants, dim, switchKeys)
    // Trivial implementation (not yet optimized)
    res := MulConstant(c, constants[1]);

    // Apply each rotation separately
    for i := 2 to GetDimensionSize(dim) do
        res := Add(res, MulConstant(RotateSlotsGoodDimension(c, dim, i - 1, switchKeys[i - 1]), constants[i]));
    end for;
    return res;
end function;

// Apply one-dimensional E-linear transformation to a ciphertext c in a good dimension
function MatMul1DGoodDimensionBabyGiant(c, adapted_constants, dim, switchKeys)
    // Baby-step/giant-step logic
    dim_size := GetDimensionSize(dim);
    g, h := GetBabyGiantParams(dim_size);

    // Precompute small number of rotations
    v := [c];
    for j := 1 to g - 1 do
        Append(~v, RotateSlotsGoodDimension(c, dim, j, switchKeys[j]));
    end for;

    // Compute remaining sum
    w := GetZeroCiphertext(c);
    for k := 0 to h - 1 do
        tmp := GetZeroCiphertext(c);
        for j := 0 to g - 1 do
            // Compute which constant to use
            i := j + g * k;
            if i ge dim_size then
                continue;
            end if;

            // Compute inner sum
            tmp := Add(tmp, MulConstant(v[j + 1], adapted_constants[i + 1]));
        end for;

        // Compute outer sum
        if k eq 0 then
            w := Add(w, tmp);
        else
            w := Add(w, RotateSlotsGoodDimension(tmp, dim, g * k, switchKeys[g * k]));
        end if;
    end for;
    return w;
end function;

// Apply one-dimensional E-linear transformation to a ciphertext c in a bad dimension
// All evaluation keys need to be provided, except for the trivial one
function MatMul1DBadDimension(c, constants, dim, switchKeysAhead, switchKeysBack)
    // Trivial implementation (not yet optimized)
    res := MulConstant(c, constants[1]);

    // Apply each rotation separately
    for i := 2 to GetDimensionSize(dim) do
        res := Add(res, MulConstant(RotateSlotsBadDimension(c, dim, i - 1, switchKeysAhead[i - 1],
                                                            switchKeysBack[i - 1]), constants[i]));
    end for;
    return res;
end function;

// Apply one-dimensional E-linear transformation to a ciphertext c in a bad dimension
function MatMul1DBadDimensionBabyGiant(c, adapted_constantsAhead, adapted_constantsBack, dim, switchKeysAhead, switchKeyMinusD)
    // Baby-step/giant-step logic
    dim_size := GetDimensionSize(dim);
    g, h := GetBabyGiantParams(dim_size);

    // Compute c_prime (v_prime from paper)
    hyperIndex := Get1DHyperIndex(dim, -dim_size);
    c_prime := ApplyAutomorphismCiphertext(c, hyperIndex, switchKeyMinusD);

    // Precompute small number of rotations
    v := [c];
    v_prime := [c_prime];
    for j := 1 to g - 1 do
        hyperIndex := Get1DHyperIndex(dim, j);
        Append(~v, ApplyAutomorphismCiphertext(c, hyperIndex, switchKeysAhead[j]));
        Append(~v_prime, ApplyAutomorphismCiphertext(c_prime, hyperIndex, switchKeysAhead[j]));
    end for;

    // Compute remaining sum
    w := GetZeroCiphertext(c);
    for k := 0 to h - 1 do
        tmp := GetZeroCiphertext(c);
        for j := 0 to g - 1 do
            // Compute which constant to use
            i := j + g * k;
            if i ge dim_size then
                continue;
            end if;

            // Compute inner sum
            tmp := Add(tmp, Add(MulConstant(v[j + 1], adapted_constantsAhead[i + 1]),
                                MulConstant(v_prime[j + 1], adapted_constantsBack[i + 1])));
        end for;

        // Compute outer sum
        if k eq 0 then
            w := Add(w, tmp);
        else
            hyperIndex := Get1DHyperIndex(dim, g * k);
            w := Add(w, ApplyAutomorphismCiphertext(tmp, hyperIndex, switchKeysAhead[g * k]));
        end if;
    end for;
    return w;
end function;