// Compute n x n W-matrix
function ComputeWMatrix(n, W_8n, ring)
    return SparseMatrix(ring, n, n, [<i + 1, i + 1, W_8n ^ (5 ^ i)> : i in [0..n - 1]]);
end function;

// Decompose S-matrix (of dimension m/4 x m/4)
function ComputeSFactors(m, W_m, ring)
    n := m div 4;
    if n eq 1 then
        return [];
    else
        res := [VerticalJoin(HorizontalJoin(IdentitySparseMatrix(ring, n div 2), ComputeWMatrix(n div 2, W_m, ring)),
                             HorizontalJoin(IdentitySparseMatrix(ring, n div 2), -ComputeWMatrix(n div 2, W_m, ring)))];
        tmp := ComputeSFactors(m div 2, W_m ^ 2, ring);
        for index := 1 to #tmp do
            Append(~res, VerticalJoin(HorizontalJoin(tmp[index], SparseMatrix(ring, n div 2, n div 2)),
                                      HorizontalJoin(SparseMatrix(ring, n div 2, n div 2), tmp[index])));
        end for;
        return res;
    end if;
end function;

// Extend result to full CRT-matrix (of dimension m/2 x m/2)
function ComputeCRTFactors(m, W_m, ring)
    SFactors1 := ComputeSFactors(m, W_m, ring);
    SFactors2 := ComputeSFactors(m, W_m ^ (-1), ring);

    result := [];
    for index := 1 to #SFactors1 do
        Append(~result, VerticalJoin(HorizontalJoin(SFactors1[index], SparseMatrix(ring, m div 4, m div 4)),
                                     HorizontalJoin(SparseMatrix(ring, m div 4, m div 4), SFactors2[index])));
    end for;
    Append(~result, VerticalJoin(
                    HorizontalJoin(IdentitySparseMatrix(ring, m div 4), (W_m ^ (m div 4)) * IdentitySparseMatrix(ring, m div 4)),
                    HorizontalJoin(IdentitySparseMatrix(ring, m div 4), (W_m ^ (-m div 4)) * IdentitySparseMatrix(ring, m div 4))));
    return result;
end function;



/* Functionality for improved GBFV bootstrapping */

// Circular bit shift to the left
function CircularBitShift(dim, nb_positions, number)
    // Convert to binary and compute bit shift
    bit_size := Round(Log(2, dim)); nb_positions mod:= bit_size;
    seq := CatZeros(IntegerToSequence(number, 2), bit_size);
    res := seq[#seq - nb_positions + 1..#seq] cat seq[1..#seq - nb_positions];
    return SequenceToInteger(res, 2);
end function;

// Circular bit shift matrix
function ComputeBitShiftMatrix(dim, nb_positions, ring)
    matrix := SparseMatrix(ring, dim, dim);
    for col := 1 to dim do
        matrix[CircularBitShift(dim, nb_positions, col - 1) + 1][col] := 1;
    end for;
    return matrix;
end function;

// Convert the given sparse matrix in standard basis to our natural basis or vice versa
// If the given matrix is square then it is considered as a linear transformation
// If the given matrix has only one column then it is considered as a vector
function ChangeMatBasis(matrix: standard_to_natural := true)
    assert (NumberOfRows(matrix) eq NumberOfColumns(matrix)) or (NumberOfColumns(matrix) eq 1);
    dim := NumberOfRows(matrix); permutation_matrix := SparseMatrix(Parent(matrix[1][1]), dim, dim);
    for row := 1 to dim do
        minor := (row - 1) div (dim div 2); major := (row - 1) mod (dim div 2);
        permutation_matrix[row][minor + 2 * major + 1] := 1;
    end for;

    // Result is different if we convert from standard to natural basis or vice versa
    if standard_to_natural then
        permutation_matrix := Transpose(permutation_matrix);
    end if;
    matrix := permutation_matrix * matrix;

    // If matrix is square then we also post-multiply
    if NumberOfRows(matrix) eq NumberOfColumns(matrix) then
        matrix *:= Transpose(permutation_matrix);
    end if;
    return matrix;
end function;

// Extend size of matrix by interleaving it with zeros
function InterleaveMatrix(matrix, spacing)
    result := SparseMatrix(Parent(matrix[1][1]), NumberOfRows(matrix) * spacing, NumberOfColumns(matrix) * spacing);
    for el in Eltseq(matrix) do
        result[(el[1] - 1) * spacing + 1][(el[2] - 1) * spacing + 1] := el[3];
    end for;
    return result;
end function;

// Extend size of matrix by repeating it multiple times on the diagonal
// The repetition number should be a power of two
function RepeatMatrix(matrix, repetition)
    assert IsPowerOfTwo(repetition);
    for iteration := 1 to Round(Log(2, repetition)) do
        zero_matrix := SparseMatrix(Parent(matrix[1][1]), NumberOfRows(matrix), NumberOfColumns(matrix));
        matrix := VerticalJoin(HorizontalJoin(matrix, zero_matrix), HorizontalJoin(zero_matrix, matrix));
    end for;
    return matrix;
end function;

// Compute matrix decomposition for improved GBFV SlotToCoeff or its inverse
// W is a primitive 2*n_double_prime-th root of unity
function ComputeGBFVFactors(n_prime, n_double_prime, W, ring, henselExponent, inverse)
    if n_double_prime eq 1 then
        return [];
    end if;

    // Compute original CRT matrix shifted by permutation matrix
    nb_positions := ((n_double_prime ^ 2) gt n_prime) select Round(Log(2, n_prime div n_double_prime)) else 0;
    P_mat := ComputeBitShiftMatrix(n_double_prime, nb_positions, ring);
    factors := ComputeCRTFactors(2 * n_double_prime, W, ring);
    factors := [InterleaveMatrix(Transpose(P_mat) * ChangeMatBasis(inverse select
                ChangeRingToExtensionAlgebra(InvertMatrixOverSlotAlgebra(factor, henselExponent), ring) else factor) *
                P_mat, n_prime div n_double_prime) : factor in factors];

    // Offsets for the matrix factors (the spacing between two slots that should be mapped to one another)
    nb_ntt := Round(Log(2, n_double_prime));
    offsets := [((2 ^ i) * (n_prime div n_double_prime)) div 2 : i in [1..nb_ntt]];
    offsets := Reverse(offsets[#offsets - nb_positions + 1..#offsets] cat offsets[1..#offsets - nb_positions]);
    are_offsets_good := [false : i in [1..nb_ntt]];     // Good offsets in this regime are automatically detected

    // Compute basic matrix that implements the desired permutation (irrespective of the iteration)
    basic_dimension := 2 * n_double_prime * Maximum(n_prime div (n_double_prime ^ 2), 1);
    basic_matrix := SparseMatrix(ring, basic_dimension, basic_dimension);
    for slot_index := 1 to basic_dimension div 4 do
        basic_matrix[2 * slot_index - 1][2 * slot_index - 1] := 1;    // Keep first half and move second half one position forward
        basic_matrix[(basic_dimension div 2) + 2 * slot_index][(basic_dimension div 2) + 2 * slot_index - 1] := 1;
    end for;

    // Each iteration interleaves and repeats with a different amount
    nb_permutations := Round(Log(2, Minimum(n_double_prime, n_prime div n_double_prime)));
    for iteration := 1 to nb_permutations do
        nb_repeat := 2 ^ (iteration - 1); offset := 2 ^ (nb_permutations - iteration);
        Insert(~factors, 1, InterleaveMatrix(RepeatMatrix(inverse select Transpose(basic_matrix) else basic_matrix, nb_repeat),
                                             n_prime div (nb_repeat * basic_dimension)));
        Insert(~offsets, 1, offset); Insert(~are_offsets_good, 1, true);
    end for;
    return (inverse select Reverse(factors) else factors), (inverse select Reverse(offsets) else offsets),
           (inverse select Reverse(are_offsets_good) else are_offsets_good);
end function;