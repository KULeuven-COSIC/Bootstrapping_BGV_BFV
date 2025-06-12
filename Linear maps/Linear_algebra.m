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

// Change the ring of the given matrix to some extension algebra
function ChangeRingToExtensionAlgebra(matrix, ring)
    if Category(matrix) eq MtrxSprs then
        return SparseMatrix(NumberOfRows(matrix), NumberOfColumns(matrix),
                            [<el[1], el[2], ring!Eltseq(Zx!Eltseq(el[3]))> : el in Eltseq(matrix)]);
    else
        return Matrix(NumberOfRows(matrix), NumberOfColumns(matrix), [ring | Eltseq(Zx!Eltseq(el)) : el in Eltseq(matrix)]);
    end if;
end function;

// Invert the given matrix over the slot algebra
// The entries of the matrix should be changeable to Zx and this function will also return a matrix with entries in Zx
// If the specified matrix is sparse then the computed one will also be sparse
function InvertMatrixOverSlotAlgebra(matrix, henselExponent)
    assert henselExponent le e;

    // First invert the matrix over a finite field
    matrix := ChangeRing(matrix, Zx);
    Fp_ext := ext<GF(p) | GetFirstSlotFactor()>;
    inv := ChangeRingToExtensionAlgebra(matrix, Fp_ext) ^ (-1);

    // Now work over the slot algebra
    Zt_F1<y> := GetSlotAlgebra(henselExponent);
    matrix := ChangeRingToExtensionAlgebra(matrix, Zt_F1);
    inv := ChangeRingToExtensionAlgebra(inv, Zt_F1);
    I := (Category(matrix) eq MtrxSprs) select IdentitySparseMatrix(Zt_F1, NumberOfRows(matrix)) else
                                               IdentityMatrix(Zt_F1, NumberOfRows(matrix));

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



// Compute the constants for a Zpr-linear map on E based on d linear independent input-output pairs
// The function returns a sequence c such that the map is given by theta -> c[1] * theta + ... + c[d] * sigma^(d - 1)(theta)
// where sigma denotes the Frobenius map
// It is allowed to pass multiple outputs by chaining all elements in one sequence (the result will then be chained as well)
function GetMapConstants(inputs, outputs, henselExponent)
    // Solve a system of linear equations to determine the map
    Zt_F1<y> := GetSlotAlgebra(henselExponent);
    matrix := &cat[[Evaluate(inputs[equation], y ^ Modexp(p, i, m)) : i in [0..d - 1]] : equation in [1..d]];
    return SolveSystem(Matrix(Zx, d, d, matrix), Transpose(Matrix(Zx, #outputs div d, d, outputs)), henselExponent);
end function;

// Convert the given constants for a Zpr-linear map on E to a matrix
// The matrix is with respect to the standard basis 1, x, ..., x ^ (d - 1)
function MapToMatrix(constants, henselExponent)
    Zt := Integers(p ^ henselExponent);
    Zt_F1<y> := GetSlotAlgebra(henselExponent);

    // Evaluate the linear map for inputs of the form x ^ pow
    matrix := [Zt | ];
    for pow := 0 to d - 1 do
        matrix cat:= Eltseq(&+[Evaluate(constants[i + 1], y) * (y ^ (Modexp(p, i, m) * pow mod m)) : i in [0..d - 1]]);
        matrix := CatZeros(matrix, d * (pow + 1));
    end for;
    return Transpose(Matrix(Z, d, d, matrix));
end function;

// The variable matrices is a sequence of objects called 'matrix' for which we compute the following:
// Compute the constants of a Zpr-linear map on E based on the given matrix
// The matrix is with respect to the standard basis 1, x, ..., x ^ (d - 1)
function MatricesToMaps(matrices, henselExponent)
    Zt := Integers(p ^ henselExponent);

    // Set up a system of equations to compute the constants
    inputs := [Zx | ];  // Compute inputs (they do not depend on matrix)
    for equation := 0 to d - 1 do
        Append(~inputs, x ^ equation);
    end for;
    outputs := [Zx | ]; // Compute outputs (they do depend on matrix)
    for matrix in matrices do
        for equation := 0 to d - 1 do
            Append(~outputs, Eltseq(ChangeRing(matrix, Zt) * Matrix(Zt, d, 1, [i eq equation select 1 else 0 : i in [0..d - 1]])));
        end for;
    end for;
    return GetMapConstants(inputs, outputs, henselExponent);
end function;