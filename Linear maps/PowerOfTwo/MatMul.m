// Perform linear transformation on plaintext slots
// --> Not restricted to one-dimensional transformations
// --> We assume that the given ciphertexts are sparsely packed
//--------------------------

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
                              ApplyAutomorphism(constants[HypercubeToIndex(i_seq)], p ^ henselExponent, rot_size);
        end for;
    end for;
    return adapted_constants;
end function;

// Apply one-dimensional E-linear transformation to a ciphertext c
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

// Apply one-dimensional E-linear transformation to a ciphertext c
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
            tmp := Add(tmp, MulConstant(v[SequenceToIndex(j_seq, g_seq)], adapted_constants[HypercubeToIndex(i_seq)]));
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