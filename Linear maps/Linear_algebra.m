// Some linear algebra functions that Magma doesn't support by default
//--------------------------

// Invert the given matrix of which the entries are themselves matrices over Z
function InvertMatrixOverMatrix(matrix, henselExponent)
    // Dimension of the problem
    outer_dim := NumberOfRows(matrix);
    inner_dim := NumberOfRows(matrix[1][1]);

    // Consider the matrix as a block matrix such that Magma can invert it
    mat := ChangeRing(BlockMatrix(outer_dim, outer_dim, Eltseq(matrix)), Integers(p ^ henselExponent));
    inverse := ChangeRing(mat ^ (-1), Z);

    // Convert back to the original format
    return Matrix(outer_dim, outer_dim, [Submatrix(inverse, inner_dim * (index div outer_dim) + 1,
                                                            inner_dim * (index mod outer_dim) + 1, inner_dim, inner_dim) :
                                         index in [0..outer_dim ^ 2 - 1]]);
end function;

// Invert the given matrix over the slot algebra
// The entries of the matrix should be elements of Zx
function InvertMatrixOverSlotAlgebra(matrix, henselExponent)
    assert henselExponent le e;

    // First invert the matrix over a finite field
    Fp_ext := ext<GF(p) | GetFirstSlotFactor()>;
    dim := NumberOfRows(matrix);
    inv := Matrix(dim, dim, [Fp_ext | Eltseq(el) : el in Eltseq(matrix)]) ^ (-1);

    // Now work over the slot algebra
    Zt_F1<y> := GetSlotAlgebra(henselExponent);
    matrix := Matrix(dim, dim, [Zt_F1 | Eltseq(el) : el in Eltseq(matrix)]);
    inv := Matrix(dim, dim, [Zt_F1 | Eltseq(el) : el in [Zx | Eltseq(el) : el in Eltseq(inv)]]);
    I := DiagonalMatrix([Zt_F1 | 1 : i in [1..dim]]);

    // Perform Hensel lifting
    prec := henselExponent;
    while prec gt 1 do
        inv := inv - inv * (matrix * inv - I);
        prec := (prec + 1) div 2;
    end while;
    return ChangeRing(inv, Zx);
end function;

// Solve the full rank system Ax = b over the slot algebra
// Both A and b must be specified as matrices over Zx
// It is allowed that b is a full matrix instead of a column matrix
function SolveSystem(A, b, henselExponent)
    assert henselExponent le e;

    // Trivial implementation: multiply inverse of A with b
    inverse := InvertMatrixOverSlotAlgebra(A, henselExponent);
    return [el mod GetFirstSlotFactor() mod (p ^ henselExponent) : el in Eltseq(Transpose(inverse * b))];
end function;