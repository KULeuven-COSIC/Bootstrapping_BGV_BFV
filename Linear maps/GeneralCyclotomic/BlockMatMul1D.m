// Compute the adapted constants for the baby-step/giant-step algorithm in a good dimension
function BlockMatMul1DGoodDimensionAdaptedConstants(constants, dim, henselExponent)
    // Compute dimension size
    dim_size := GetDimensionSize(dim);

    // Compute adapted constants
    adapted_constants := [];
    for index := 1 to d * dim_size do
        i, j := IndexToIJ(index, dim);
        Append(~adapted_constants, ApplyFrobeniusPowerPlaintext(constants[index], -j: henselExponent := henselExponent));
    end for;
    return adapted_constants;
end function;

// Compute the adapted constants for the baby-step/giant-step algorithm in a bad dimension
function BlockMatMul1DBadDimensionAdaptedConstants(constants, dim, henselExponent)
    // Compute dimension size
    dim_size := GetDimensionSize(dim);

    // Compute adapted constants
    adapted_constantsAhead := [];
    adapted_constantsBack := [];
    for index := 1 to d * dim_size do
        i, j := IndexToIJ(index, dim);

        // Embed mask entries into slots
        maskAhead := GetAdaptedMaskAhead(dim, i, henselExponent);
        maskBack := GetAdaptedMaskBack(dim, i, henselExponent);

        // Compute adapted constants
        hyperIndex := Get1DHyperIndex(dim, dim_size);
        tmp := ApplyFrobeniusPowerPlaintext(constants[index], -j: henselExponent := henselExponent);
        Append(~adapted_constantsAhead, ((tmp * maskAhead) mod f) mod (p ^ henselExponent));
        Append(~adapted_constantsBack, ApplyAutomorphismPlaintext(((tmp * maskBack) mod f) mod (p ^ henselExponent),
                                                                    hyperIndex: henselExponent := henselExponent));
    end for;
    return adapted_constantsAhead, adapted_constantsBack;
end function;

// Apply one-dimensional Zpr-linear transformation to a ciphertext c in a good dimension
// All evaluation keys need to be provided, except for the trivial one
function BlockMatMul1DGoodDimension(c, constants, dim, rotationSwitchKeys, frobeniusSwitchKeys)
    // Trivial implementation (not yet optimized)
    res := GetZeroCiphertext(c);

    // Apply each rotation and Frobenius map separately
    for index := 1 to d * GetDimensionSize(dim) do
        i, j := IndexToIJ(index, dim);

        // Rotation
        cNew := c;
        if i ne 0 then
            cNew := RotateSlotsGoodDimension(cNew, dim, i, rotationSwitchKeys[i]);
        end if;

        // Frobenius
        if j ne 0 then
            cNew := ApplyFrobeniusPowerCiphertext(cNew, j, frobeniusSwitchKeys[j]);
        end if;

        res := Add(res, MulConstant(cNew, constants[index]));
    end for;
    return res;
end function;

// Apply one-dimensional Zpr-linear transformation to a ciphertext c in a good dimension
// All evaluation keys need to be provided, except for the trivial one
function BlockMatMul1DGoodDimensionBabyGiant(c, adapted_constants, dim, rotationSwitchKeys, frobeniusSwitchKeys)
    // Baby-step/giant-step logic
    dim_size := GetDimensionSize(dim);
    w := [GetZeroCiphertext(c) : i in [1..d]];

    // Precompute small number of rotations
    for i := 0 to dim_size - 1 do
        v := c;
        if i ne 0 then
            v := RotateSlotsGoodDimension(c, dim, i, rotationSwitchKeys[i]);
        end if;

        for j := 0 to d - 1 do
            w[j + 1] := Add(w[j + 1], MulConstant(v, adapted_constants[IJToIndex(i, j, dim)]));
        end for;
    end for;

    // Compute remaining sum using Frobenius maps
    res := w[1];
    for j := 1 to d - 1 do
        res := Add(res, ApplyFrobeniusPowerCiphertext(w[j + 1], j, frobeniusSwitchKeys[j]));
    end for;
    return res;
end function;

// Apply one-dimensional Zpr-linear transformation to a ciphertext c in a bad dimension
// All evaluation keys need to be provided, except for the trivial one
function BlockMatMul1DBadDimension(c, constants, dim, rotationSwitchKeysAhead, rotationSwitchKeysBack, frobeniusSwitchKeys)
    // Trivial implementation (not yet optimized)
    res := GetZeroCiphertext(c);

    // Apply each rotation and Frobenius map separately
    for index := 1 to d * GetDimensionSize(dim) do
        i, j := IndexToIJ(index, dim);

        // Rotation
        cNew := c;
        if i ne 0 then
            cNew := RotateSlotsBadDimension(cNew, dim, i, rotationSwitchKeysAhead[i], rotationSwitchKeysBack[i]);
        end if;

        // Frobenius
        if j ne 0 then
            cNew := ApplyFrobeniusPowerCiphertext(cNew, j, frobeniusSwitchKeys[j]);
        end if;

        res := Add(res, MulConstant(cNew, constants[index]));
    end for;
    return res;
end function;

// Apply one-dimensional Zpr-linear transformation to a ciphertext c in a bad dimension
// All evaluation keys need to be provided, except for the trivial one
function BlockMatMul1DBadDimensionBabyGiant(c, adapted_constantsAhead, adapted_constantsBack, dim,
                                            switchKeysAhead, switchKeyMinusD, frobeniusSwitchKeys)
    // Baby-step/giant-step logic
    dim_size := GetDimensionSize(dim);
    u := [GetZeroCiphertext(c) : j in [1..d]];
    u_prime := [GetZeroCiphertext(c) : j in [1..d]];

    // Precompute small number of rotations
    for i := 0 to dim_size - 1 do
        v := c;
        if i ne 0 then
            hyperIndex := Get1DHyperIndex(dim, i);
            v := ApplyAutomorphismCiphertext(c, hyperIndex, switchKeysAhead[i]);
        end if;

        for j := 0 to d - 1 do
            u[j + 1] := Add(u[j + 1], MulConstant(v, adapted_constantsAhead[IJToIndex(i, j, dim)]));
            u_prime[j + 1] := Add(u_prime[j + 1], MulConstant(v, adapted_constantsBack[IJToIndex(i, j, dim)]));
        end for;
    end for;

    // Compute remaining sum using Frobenius maps and one regular automorphism
    res := u[1];
    res_prime := u_prime[1];
    for j := 1 to d - 1 do
        res := Add(res, ApplyFrobeniusPowerCiphertext(u[j + 1], j, frobeniusSwitchKeys[j]));
        res_prime := Add(res_prime, ApplyFrobeniusPowerCiphertext(u_prime[j + 1], j, frobeniusSwitchKeys[j]));
    end for;
    hyperIndex := Get1DHyperIndex(dim, -dim_size);
    return Add(res, ApplyAutomorphismCiphertext(res_prime, hyperIndex, switchKeyMinusD));
end function;