// Perform linear transformation on plaintext slots
// --> Not restricted to one-dimensional transformations
// --> We assume that the given ciphertexts are sparsely packed
//--------------------------

/*** Algorithms for Chen/Han linear transformations ***/

// Apply linear transformation to a ciphertext c using automorphisms from S
// All evaluation keys need to be provided, except for the trivial one
function MatMul(c, constants, switchKeys)
    // Trivial implementation (not yet optimized)
    res := MulConstant(c, constants[1]);

    // Apply each rotation separately
    for i := 2 to l do
        res := Add(res, MulConstant(ApplyAutomorphismCiphertext(c, IndexToHypercube(i), switchKeys[i - 1]), constants[i]));
    end for;
    return res;
end function;

// Compute the adapted constants for the baby-step/giant-step algorithm
function MatMulAdaptedConstants(constants, henselExponent)
    // Compute parameters
    dim_sizes := [GetDimensionSize(dim) : dim in [1..GetNbDimensions()]];
    g_seq, h_seq := GetGeneralBabyGiantParams(dim_sizes);

    // Compute adapted constants
    adapted_constants := [];
    for k := 1 to &*h_seq do
        // Sequence of k
        k_seq := IndexToSequence(k, h_seq);

        for j := 1 to &*g_seq do
            // Sequence of j and i
            j_seq := IndexToSequence(j, g_seq);
            i_seq := [j_seq[ind] + g_seq[ind] * k_seq[ind] : ind in [1..#j_seq]];

            // Skip the current iteration if we are not in the valid range
            skip := false;
            for index := 1 to #dim_sizes do
                if i_seq[index] ge dim_sizes[index] then
                    skip := true;
                end if;
            end for;

            // We can skip the current iteration
            if skip then
                continue;
            end if;

            // Compute rotation
            rot_size := [-g_seq[ind] * k_seq[ind] : ind in [1..#g_seq]];
            adapted_constants[HypercubeToIndex(i_seq)] :=
                              ApplyAutomorphismPlaintext(constants[HypercubeToIndex(i_seq)], rot_size:
                                                         henselExponent := henselExponent);
        end for;
    end for;
    return adapted_constants;
end function;

// Apply linear transformation to a ciphertext c using automorphisms from S
function MatMulBabyGiant(c, adapted_constants, switchKeys)
    // Baby-step/giant-step logic
    dim_sizes := [GetDimensionSize(dim) : dim in [1..GetNbDimensions()]];
    g_seq, h_seq := GetGeneralBabyGiantParams(dim_sizes);

    // Precompute small number of rotations
    v := [c];
    for j := 2 to &*g_seq do
        Append(~v, ApplyAutomorphismCiphertext(c, IndexToSequence(j, g_seq),
                                               switchKeys[HypercubeToIndex(IndexToSequence(j, g_seq)) - 1]));
    end for;

    // Compute remaining sum
    w := GetZeroCiphertext(c);
    for k := 1 to &*h_seq do
        // Sequence of k
        k_seq := IndexToSequence(k, h_seq);
        tmp := GetZeroCiphertext(c);
        for j := 1 to &*g_seq do
            // Sequence of j and i
            j_seq := IndexToSequence(j, g_seq);
            i_seq := [j_seq[ind] + g_seq[ind] * k_seq[ind] : ind in [1..#j_seq]];

            // Skip the current iteration if we are not in the valid range
            skip := false;
            for index := 1 to #dim_sizes do
                if i_seq[index] ge dim_sizes[index] then
                    skip := true;
                end if;
            end for;

            // We can skip the current iteration
            if skip then
                continue;
            end if;

            // Compute inner sum
            tmp := Add(tmp, MulConstant(v[j], adapted_constants[HypercubeToIndex(i_seq)]));
        end for;

        // Compute outer sum
        if k eq 1 then
            w := Add(w, tmp);
        else
            rot_size := [g_seq[ind] * k_seq[ind] : ind in [1..#g_seq]];
            w := Add(w, ApplyAutomorphismCiphertext(tmp, rot_size, switchKeys[HypercubeToIndex(rot_size) - 1]));
        end if;
    end for;
    return w;
end function;



/*** Algorithms for our linear transformations ***/

// Convert rot_size to exponent
function RotToExp(generators, rot_size)
    return Z!(&*[(Zm!generators[i]) ^ rot_size[i] : i in [1..#generators]]);
end function;

// Convert exponent to rot_size via iterative search
function ExpToRot(generators, dim_sizes, exp)
    for index := 1 to &*dim_sizes do
        rot_size := IndexToSequence(index, dim_sizes);
        if RotToExp(generators, rot_size) eq exp then
            return rot_size;
        end if;
    end for;

    error "Converting rot_size to exponent is not possible.";
end function;

// Compute generators and dimension sizes
function ComputeGenSizes(dimensions)
    return [GetInverseHypercubeRepresentative([index eq dim select 1 else 0 : index in [1..GetNbDimensions()]]) :
                                               dim in dimensions], [GetDimensionSize(dim) : dim in dimensions];
end function;

/*** Good dimensions ***/

// Apply linear transformation to a ciphertext c in multiple dimensions
// Each dimension is specified by a generator (and can hence also be the Frobenius dimension)
// All evaluation keys need to be provided, except for the trivial one
function MatMulGeneralGoodDimension(c, constants, generators, dim_sizes, switchKeys)
    // Trivial implementation (not yet optimized)
    res := MulConstant(c, constants[1]);

    // Apply each rotation separately
    for i := 2 to &*dim_sizes do
        res := Add(res, MulConstant(ApplyAutomorphismCiphertext(c, RotToExp(generators, IndexToSequence(i, dim_sizes)),
                                                                switchKeys[i - 1]), constants[i]));
    end for;
    return res;
end function;

// Apply linear transformation to a ciphertext c in 2 dimensions
// All evaluation keys need to be provided, except for the trivial one
function MatMul2DGoodDimension(c, constants, dimensions, switchKeys)
    generators, dim_sizes := ComputeGenSizes(dimensions);
    return MatMulGeneralGoodDimension(c, constants, generators, dim_sizes, switchKeys);
end function;

// Compute the adapted constants for the baby-step/giant-step algorithm
function MatMulGeneralGoodDimensionAdaptedConstants(constants, generators, dim_sizes, henselExponent)
    // Compute parameters
    g_seq, h_seq := GetGeneralBabyGiantParams(dim_sizes);

    // Compute adapted constants
    adapted_constants := [];
    for k := 1 to &*h_seq do
        // Sequence of k
        k_seq := IndexToSequence(k, h_seq);

        for j := 1 to &*g_seq do
            // Sequence of j and i
            j_seq := IndexToSequence(j, g_seq);
            i_seq := [j_seq[ind] + g_seq[ind] * k_seq[ind] : ind in [1..#j_seq]];

            // Skip the current iteration if we are not in the valid range
            skip := false;
            for index := 1 to #dim_sizes do
                if i_seq[index] ge dim_sizes[index] then
                    skip := true;
                end if;
            end for;

            // We can skip the current iteration
            if skip then
                continue;
            end if;

            // Compute multiplication and rotation
            rot_size := [-g_seq[ind] * k_seq[ind] : ind in [1..#g_seq]];
            adapted_constants[SequenceToIndex(i_seq, dim_sizes)] :=
                              ApplyAutomorphismPlaintext(constants[SequenceToIndex(i_seq, dim_sizes)],
                                                         RotToExp(generators, rot_size): henselExponent := henselExponent);
        end for;
    end for;
    return adapted_constants;
end function;

// Compute the adapted constants for the baby-step/giant-step algorithm
function MatMul2DGoodDimensionAdaptedConstants(constants, dimensions, henselExponent)
    generators, dim_sizes := ComputeGenSizes(dimensions);
    return MatMulGeneralGoodDimensionAdaptedConstants(constants, generators, dim_sizes, henselExponent);
end function;

// Apply linear transformation to a ciphertext c in multiple dimensions
// Each dimension is specified by a generator (and can hence also be the Frobenius dimension)
function MatMulGeneralGoodDimensionBabyGiant(c, adapted_constants, generators, dim_sizes, switchKeys)
    // Compute parameters
    g_seq, h_seq := GetGeneralBabyGiantParams(dim_sizes);

    // Precompute small number of rotations
    v := [c];
    for j := 2 to &*g_seq do
        rot_size := IndexToSequence(j, g_seq);
        Append(~v, ApplyAutomorphismCiphertext(c, RotToExp(generators, rot_size),
                                               switchKeys[SequenceToIndex(rot_size, dim_sizes) - 1]));
    end for;

    // Compute remaining sum
    w := GetZeroCiphertext(c);
    for k := 1 to &*h_seq do
        // Sequence of k
        k_seq := IndexToSequence(k, h_seq);
        tmp := GetZeroCiphertext(c);
        for j := 1 to &*g_seq do
            // Sequence of j and i
            j_seq := IndexToSequence(j, g_seq);
            i_seq := [j_seq[ind] + g_seq[ind] * k_seq[ind] : ind in [1..#j_seq]];

            // Skip the current iteration if we are not in the valid range
            skip := false;
            for index := 1 to #dim_sizes do
                if i_seq[index] ge dim_sizes[index] then
                    skip := true;
                end if;
            end for;

            // We can skip the current iteration
            if skip then
                continue;
            end if;

            // Compute inner sum
            tmp := Add(tmp, MulConstant(v[j], adapted_constants[SequenceToIndex(i_seq, dim_sizes)]));
        end for;

        // Compute outer sum
        if k eq 1 then
            w := Add(w, tmp);
        else
            rot_size := [g_seq[ind] * k_seq[ind] : ind in [1..#g_seq]];
            w := Add(w, ApplyAutomorphismCiphertext(tmp, RotToExp(generators, rot_size),
                                                    switchKeys[SequenceToIndex(rot_size, dim_sizes) - 1]));
        end if;
    end for;
    return w;
end function;

// Apply linear transformation to a ciphertext c in 2 dimensions
function MatMul2DGoodDimensionBabyGiant(c, adapted_constants, dimensions, switchKeys)
    generators, dim_sizes := ComputeGenSizes(dimensions);
    return MatMulGeneralGoodDimensionBabyGiant(c, adapted_constants, generators, dim_sizes, switchKeys);
end function;

/*** Bad dimensions ***/

// Apply linear transformation to a ciphertext c in multiple dimensions
// Only the last dimension can be a bad dimension (and it must be specified explicitly)
// Each dimension is specified by a generator (and can hence also be the Frobenius dimension)
// All evaluation keys need to be provided, except for the trivial one
function MatMulGeneralBadDimension(c, constants, generators, dim_sizes, bad_dimension, switchKeysAhead, switchKeysBack)
    // Trivial implementation (not yet optimized)
    res := MulConstant(c, constants[1]);

    // Apply each rotation separately
    for i := 2 to &*dim_sizes do
        rot_size := IndexToSequence(i, dim_sizes);
        res := Add(res, MulConstant(RotateSlotsGeneral(c, RotToExp(generators, rot_size), bad_dimension, rot_size[#rot_size],
                                    switchKeysAhead[i - 1], switchKeysBack[i - 1]), constants[i]));
    end for;
    return res;
end function;

// Apply linear transformation to a ciphertext c in 2 dimensions
// The first dimension must be a good dimension
// All evaluation keys need to be provided, except for the trivial one
function MatMul2DBadDimension(c, constants, dimensions, switchKeysAhead, switchKeysBack)
    generators, dim_sizes := ComputeGenSizes(dimensions);
    return MatMulGeneralBadDimension(c, constants, generators, dim_sizes, dimensions[2], switchKeysAhead, switchKeysBack);
end function;

// Compute the adapted constants for the baby-step/giant-step algorithm
function MatMulGeneralBadDimensionAdaptedConstants(constants, generators, dim_sizes, bad_dimension, henselExponent)
    // Compute parameters
    g_seq, h_seq := GetGeneralBabyGiantParams(dim_sizes);

    // Compute adapted constants
    adapted_constantsAhead := [];
    adapted_constantsBack := [];
    for k := 1 to &*h_seq do
        // Sequence of k
        k_seq := IndexToSequence(k, h_seq);

        for j := 1 to &*g_seq do
            // Sequence of j and i
            j_seq := IndexToSequence(j, g_seq);
            i_seq := [j_seq[ind] + g_seq[ind] * k_seq[ind] : ind in [1..#j_seq]];

            // Skip the current iteration if we are not in the valid range
            skip := false;
            for index := 1 to #dim_sizes do
                if i_seq[index] ge dim_sizes[index] then
                    skip := true;
                end if;
            end for;

            // We can skip the current iteration
            if skip then
                continue;
            end if;

            // Embed mask entries into slots
            maskAhead := GetAdaptedMaskAhead(bad_dimension, i_seq[#i_seq], henselExponent);
            maskBack := GetAdaptedMaskBack(bad_dimension, i_seq[#i_seq], henselExponent);

            // Compute multiplication and rotation
            exp := RotToExp(generators, [-g_seq[ind] * k_seq[ind] : ind in [1..#g_seq]]);
            adapted_constantsAhead[SequenceToIndex(i_seq, dim_sizes)] :=
                                   ApplyAutomorphismPlaintext(((constants[SequenceToIndex(i_seq, dim_sizes)] *
                                                                maskAhead) mod f) mod (p ^ henselExponent), exp:
                                                                henselExponent := henselExponent);
            adapted_constantsBack[SequenceToIndex(i_seq, dim_sizes)] :=
                                  ApplyAutomorphismPlaintext(((constants[SequenceToIndex(i_seq, dim_sizes)] *
                                                               maskBack) mod f) mod (p ^ henselExponent), exp:
                                                               henselExponent := henselExponent);
        end for;
    end for;
    return adapted_constantsAhead, adapted_constantsBack;
end function;

// Compute the adapted constants for the baby-step/giant-step algorithm
function MatMul2DBadDimensionAdaptedConstants(constants, dimensions, henselExponent)
    generators, dim_sizes := ComputeGenSizes(dimensions);
    return MatMulGeneralBadDimensionAdaptedConstants(constants, generators, dim_sizes, dimensions[2], henselExponent);
end function;

// Apply linear transformation to a ciphertext c in multiple dimensions
// Only the last dimension can be a bad dimension (and it must be specified explicitly)
// Each dimension is specified by a generator (and can hence also be the Frobenius dimension)
function MatMulGeneralBadDimensionBabyGiant(c, adapted_constantsAhead, adapted_constantsBack, generators, dim_sizes,
                                            bad_dimension, switchKeysAhead, switchKeyMinusD)
    // Compute parameters
    g_seq, h_seq := GetGeneralBabyGiantParams(dim_sizes);

    // Compute c_prime (v_prime from paper)
    hyperIndex := Get1DHyperIndex(bad_dimension, -dim_sizes[#dim_sizes]);
    c_prime := ApplyAutomorphismCiphertext(c, hyperIndex, switchKeyMinusD);

    // Precompute small number of rotations
    v := [c];
    v_prime := [c_prime];
    for j := 2 to &*g_seq do
        rot_size := IndexToSequence(j, g_seq);
        exp := RotToExp(generators, rot_size);
        Append(~v, ApplyAutomorphismCiphertext(c, exp, switchKeysAhead[SequenceToIndex(rot_size, dim_sizes) - 1]));
        Append(~v_prime, ApplyAutomorphismCiphertext(c_prime, exp, switchKeysAhead[SequenceToIndex(rot_size, dim_sizes) - 1]));
    end for;

    // Compute remaining sum
    w := GetZeroCiphertext(c);
    for k := 1 to &*h_seq do
        // Sequence of k
        k_seq := IndexToSequence(k, h_seq);
        tmp := GetZeroCiphertext(c);
        for j := 1 to &*g_seq do
            // Sequence of j and i
            j_seq := IndexToSequence(j, g_seq);
            i_seq := [j_seq[ind] + g_seq[ind] * k_seq[ind] : ind in [1..#j_seq]];

            // Skip the current iteration if we are not in the valid range
            skip := false;
            for index := 1 to #dim_sizes do
                if i_seq[index] ge dim_sizes[index] then
                    skip := true;
                end if;
            end for;

            // We can skip the current iteration
            if skip then
                continue;
            end if;

            // Compute inner sum
            tmp := Add(tmp, Add(MulConstant(v[j], adapted_constantsAhead[SequenceToIndex(i_seq, dim_sizes)]),
                                MulConstant(v_prime[j], adapted_constantsBack[SequenceToIndex(i_seq, dim_sizes)])));
        end for;

        // Compute outer sum
        if k eq 1 then
            w := Add(w, tmp);
        else
            rot_size := [g_seq[ind] * k_seq[ind] : ind in [1..#g_seq]];
            w := Add(w, ApplyAutomorphismCiphertext(tmp, RotToExp(generators, rot_size),
                                                    switchKeysAhead[SequenceToIndex(rot_size, dim_sizes) - 1]));
        end if;
    end for;
    return w;
end function;

// Apply linear transformation to a ciphertext c in 2 dimensions
// The first dimension must be a good dimension
function MatMul2DBadDimensionBabyGiant(c, adapted_constantsAhead, adapted_constantsBack, dimensions,
                                       switchKeysAhead, switchKeyMinusD)
    generators, dim_sizes := ComputeGenSizes(dimensions);
    return MatMulGeneralBadDimensionBabyGiant(c, adapted_constantsAhead, adapted_constantsBack, generators, dim_sizes,
                                              dimensions[2], switchKeysAhead, switchKeyMinusD);
end function;

/*** Key switching keys ***/

// Generate required key switching keys
function MatMulGeneralBabyGiantSwitchKeys(sk, generators, dim_sizes: bad_dimension := 0)
    g_seq, h_seq := GetGeneralBabyGiantParams(dim_sizes);
    keys := [];

    for j := 2 to &*g_seq do
        rot_size := IndexToSequence(j, g_seq);
        keys[SequenceToIndex(rot_size, dim_sizes) - 1] := GenSwitchKey(sk, RotToExp(generators, rot_size));
    end for;

    for k := 2 to &*h_seq do
        k_seq := IndexToSequence(k, h_seq);
        rot_size := [g_seq[ind] * k_seq[ind] : ind in [1..#g_seq]];
        keys[SequenceToIndex(rot_size, dim_sizes) - 1] := GenSwitchKey(sk, RotToExp(generators, rot_size));
    end for;

    if bad_dimension eq 0 then
        return keys;
    else
        return keys, GenSwitchKey(sk, Get1DHyperIndex(bad_dimension, -GetDimensionSize(bad_dimension)));
    end if;
end function;

// Generate required key switching keys
function MatMul2DBabyGiantSwitchKeys(sk, dimensions: is_good_dimension := true)
    generators, dim_sizes := ComputeGenSizes(dimensions);
    return MatMulGeneralBabyGiantSwitchKeys(sk, generators, dim_sizes:
                                            bad_dimension := (is_good_dimension select 0 else dimensions[2]));
end function;

/*** Unpacking and repacking ***/

// Unpack the slots of the given ciphertext
function UnpackSlotsPowerOfTwo(c, switchKeys)
    result := [c];

    // Usual iterations
    for i := 1 to (p mod 4 eq 1 select Valuation(d, 2) else Valuation(d div 2, 2)) do
        tmp := result; result := [];
        for ctxt in tmp do
            auto_ctxt := ApplyAutomorphismCiphertext(ctxt, Modexp(p, d div (2 ^ i), m), switchKeys[i]);
            Append(~result, Add(ctxt, auto_ctxt));
            Append(~result, MulConstant(Sub(ctxt, auto_ctxt), -(x ^ (n - (2 ^ (i - 1))))));
        end for;
    end for;

    // One extra iteration is necessary with larger exponent
    if p mod 4 eq 3 then
        tmp := result; result := [];
        for ctxt in tmp do
            auto_ctxt := ApplyAutomorphismCiphertext(ctxt, p, switchKeys[#switchKeys]);
            Append(~result, Add(ctxt, auto_ctxt));
            Append(~result, MulConstant(Sub(ctxt, auto_ctxt), -(x ^ (n div 2))));
        end for;
    end if;
    return result;
end function;

// Repack the slots of the given sequence of ciphertexts
function RepackSlotsPowerOfTwo(c_seq)
    result := c_seq;

    // One extra iteration is necessary with larger exponent
    if p mod 4 eq 3 then
        tmp := result; result := [];
        for index := 1 to #tmp div 2 do
            Append(~result, Add(tmp[2 * index - 1], MulConstant(tmp[2 * index], x ^ (n div 2))));
        end for;
    end if;

    // Usual iterations
    top := p mod 4 eq 1 select Valuation(d, 2) else Valuation(d div 2, 2);
    for i := 1 to top do
        tmp := result; result := [];
        for index := 1 to #tmp div 2 do
            Append(~result, Add(tmp[2 * index - 1], MulConstant(tmp[2 * index], x ^ (2 ^ (top - i)))));
        end for;
    end for;
    return result[1];
end function;