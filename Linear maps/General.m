// Return the baby-step/giant-step parameters as a function of the given size
function GetBabyGiantParams(size)
    g := Ceiling(Sqrt(size));
    h := Ceiling(size / g);
    return g, h;
end function;

// Return the baby-step/giant-step parameters for general linear transformations
function GetGeneralBabyGiantParams(sizes)
    if #sizes eq 0 then
        return [Z | ], [Z | ];
    end if;

    // Use the following heuristic: we only split the largest dimension
    // over the baby-step and the giant-step, and find the optimal way
    // of doing this by looking at each possible alternative
    size := &*sizes;
    max_size, max_index := Maximum(sizes);
    divisors := Divisors(size div max_size);
    cost := [];     // Count cost as number of automorphisms
    for divisor in divisors do
        g := Ceiling(Sqrt(size) / divisor);
        h := Ceiling(max_size / g);
        Append(~cost, g * divisor + h * (size div max_size div divisor));
    end for;

    // Find best possible divisor
    _, index := Minimum(cost);
    divisor := divisors[index];

    // Parameters for largest dimension
    g_final := Ceiling(Sqrt(size) / divisor);
    h_final := Ceiling(max_size / g_final);

    // Loop over each dimension to find the best parameters
    g_seq := [];
    h_seq := [];
    for currentSize in Remove(sizes, max_index) do
        // Extract one factor of the divisor
        factor := GCD(currentSize, divisor);
        divisor div:= factor;

        // Append factor and its complement to the lists
        Append(~g_seq, factor);
        Append(~h_seq, currentSize div factor);
    end for;

    // Insert parameters for largest dimension in the right place
    Insert(~g_seq, max_index, g_final);
    Insert(~h_seq, max_index, h_final);
    return g_seq, h_seq;
end function;

// Convert the given index to i and j
function IndexToIJ(index, dim)
    ind_seq := IndexToSequence(index, [GetDimensionSize(dim), d]);
    return ind_seq[1], ind_seq[2];
end function;

// Convert the given i and j to a regular index
function IJToIndex(i, j, dim)
    return SequenceToIndex([i, j], [GetDimensionSize(dim), d]);
end function;