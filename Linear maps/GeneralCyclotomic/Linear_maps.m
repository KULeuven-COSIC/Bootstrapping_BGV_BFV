// Compute the constants necessary during the linear transformations
//--------------------------
assert GetLTVersion() ne 0;
load "Linear maps/General.m";
load "Linear maps/Linear_algebra.m";
load "Linear maps/GeneralCyclotomic/MatMulSlots.m";
load "Linear maps/GeneralCyclotomic/MatMul1D.m";
load "Linear maps/GeneralCyclotomic/BlockMatMul1D.m";

// Compute the constants for a one-dimensional Zpr-linear transformation
// in the given dimension which is specified by the given matrices
// If sigma denotes the entry-wise Frobenius map on a vector, then the transformation
// is given by v -> matrices[1] * v + ... + matrices[d] * sigma^(d - 1)(v)
function EmbedMatricesInSlots(matrices, dim, henselExponent)
    dim_size := GetDimensionSize(dim);
    res := [];

    // For each rotation index i and Frobenius index j, we compute one constant
    for index_ij := 1 to d * dim_size do
        i, j := IndexToIJ(index_ij, dim);
        slotContent := [];

        // Find the constant in each slot by looking at the appropriate matrix diagonal
        for index := 1 to l do
            hyperIndex := IndexToHypercube(index);
            dimIndex := hyperIndex[dim];
            Append(~slotContent, matrices[j + 1][dimIndex + 1][((dimIndex - i) mod dim_size) + 1]);
        end for;
        Append(~res, EmbedInSlots(slotContent: henselExponent := henselExponent));
    end for;
    return res;
end function;

// Return the matrices for the first stage of the evaluation map
// If sigma denotes the entry-wise Frobenius map on a vector, then the resulting matrices are such
// that the transformation is given by v -> matrices[1] * v + ... + matrices[d] * sigma^(d - 1)(v)
function GetEvalStage_1Matrices(dim, henselExponent)
    dim_size := GetDimensionSize(dim);
    Zt_F1<y> := GetSlotAlgebra(henselExponent);
    zeta_dim := y ^ (m div factors_m[dim]);

    // Determine the evaluation matrix for the given stage by solving a system of linear equations
    M_ij_inputs := [Zx | ];     // First compute left-hand side (it does not depend on row and col)
    for equation := 0 to d - 1 do
        // Constants are encoded using the normal element
        Append(~M_ij_inputs, Evaluate(GetNormalElement(), y ^ Modexp(p, equation, m)));
    end for;
    M_ij_outputs := [Zx | ];    // Then compute right-hand side (it does depend on row and col)
    for row := 0 to dim_size - 1 do
        zeta_dim_row := zeta_dim ^ GetHypercubeRepresentative(Get1DHyperIndex(dim, row));
        for col := 0 to dim_size - 1 do
            // Solve a system of linear equations to determine the map M_ij
            for equation := 0 to d - 1 do
                Append(~M_ij_outputs, zeta_dim_row ^ (col + dim_size * equation));
            end for;
        end for;
    end for;

    // Determine the map by solving the system
    constants := GetMapConstants(M_ij_inputs, M_ij_outputs, henselExponent);
    matrix_entries := [[Zx | ] : i in [1..d]];
    for row := 0 to dim_size - 1 do
        for col := 0 to dim_size - 1 do
            for i := 1 to d do
                Append(~matrix_entries[i], constants[i + d * col + dim_size * d * row]);
            end for;
        end for;
    end for;
    return [Matrix(dim_size, dim_size, matrix_entries[i]) : i in [1..d]];
end function;

// Compute the constants for the first stage of the evaluation map
function EvalStage_1Constants(dim, henselExponent)
    return EmbedMatricesInSlots(GetEvalStage_1Matrices(dim, henselExponent), dim, henselExponent);
end function;

// Compute the constants for the first stage of the inverse evaluation map
function EvalInvStage_1Constants(dim, henselExponent)
    dim_size := GetDimensionSize(dim);

    // Get the slot constants in matrix format and invert it
    matrices := GetEvalStage_1Matrices(dim, henselExponent);
    matrixOverMatrix := Matrix(dim_size, dim_size, [MapToMatrix([matrices[i][(index div dim_size) + 1]
                                                                            [(index mod dim_size) + 1] : i in [1..d]],
                                                                henselExponent) : index in [0..dim_size ^ 2 - 1]]);
    matrixOverMatrixInverse := InvertMatrixOverMatrix(matrixOverMatrix, henselExponent);
    matricesInverse := [ZeroMatrix(Zx, dim_size, dim_size) : i in [1..d]];

    // Now put the inverse constants in the sequence of matrices
    constants := MatricesToMaps(Eltseq(matrixOverMatrixInverse), henselExponent);
    for row := 0 to dim_size - 1 do
        for col := 0 to dim_size - 1 do
            // Convert the computed constants into a sequence of matrices
            for i := 1 to d do
                matricesInverse[i][row + 1][col + 1] := constants[i + d * col + dim_size * d * row];
            end for;
        end for;
    end for;
    return EmbedMatricesInSlots(matricesInverse, dim, henselExponent);
end function;



// Compute the constants for a one-dimensional E-linear transformation
// in the given dimension which is specified by the given matrix
function EmbedMatrixInSlots(matrix, dim, henselExponent)
    dim_size := GetDimensionSize(dim);
    res := [];

    // For each rotation index i, we compute one constant
    for i := 0 to dim_size - 1 do
        slotContent := [];

        // Find the constant in each slot by looking at the appropriate matrix diagonal
        for index := 1 to l do
            hyperIndex := IndexToHypercube(index);
            dimIndex := hyperIndex[dim];
            Append(~slotContent, matrix[dimIndex + 1][((dimIndex - i) mod dim_size) + 1]);
        end for;
        Append(~res, EmbedInSlots(slotContent: henselExponent := henselExponent));
    end for;
    return res;
end function;

// Return the matrix for the dim-th stage of the evaluation map
function GetEvalStage_dimMatrix(dim, henselExponent)
    dim_size := GetDimensionSize(dim);
    Zt_F1<y> := GetSlotAlgebra(henselExponent);
    zeta_dim := y ^ (m div factors_m[dim]);

    // Polynomial evaluation matrix in powers of zeta_dim
    matrix_entries := [Zx | ];
    for row := 0 to dim_size - 1 do
        for col := 0 to dim_size - 1 do
            Append(~matrix_entries, (zeta_dim ^ GetHypercubeRepresentative(Get1DHyperIndex(dim, row))) ^ col);
        end for;
    end for;
    return Matrix(dim_size, dim_size, matrix_entries);
end function;

// Compute the constants for the dim-th stage of the evaluation map
function EvalStage_dimConstants(dim, henselExponent)
    return EmbedMatrixInSlots(GetEvalStage_dimMatrix(dim, henselExponent), dim, henselExponent);
end function;

// Compute the constants for the dim-th stage of the inverse evaluation map
function EvalInvStage_dimConstants(dim, henselExponent)
    matrix := GetEvalStage_dimMatrix(dim, henselExponent);
    return EmbedMatrixInSlots(InvertMatrixOverSlotAlgebra(matrix, henselExponent), dim, henselExponent);
end function;



// Compute the constants for unpacking the slots
function UnpackConstants(henselExponent)
    Zt_F1<y> := GetSlotAlgebra(henselExponent);

    // Set up a system of equations to compute the constants
    inputs := [Zx | ];
    outputs := [Zx | ];
    for equation := 0 to d - 1 do
        Append(~inputs, Evaluate(GetNormalElement(), y ^ (p ^ equation)));
        Append(~outputs, equation eq 0 select 1 else 0);
    end for;

    // Determine the map by solving the system
    constants := GetMapConstants(inputs, outputs, henselExponent);
    return [EmbedInSlots([constants[i] : j in [1..l]]: henselExponent := henselExponent) : i in [1..d]];
end function;

// Compute the constants for repacking the slots
function RepackConstants(henselExponent)
    return [i eq 1 select EmbedInSlots([GetNormalElement() : j in [1..l]]: henselExponent := henselExponent) else
                          ApplyFrobeniusPowerPlaintext(Self(i - 1), 1: henselExponent := henselExponent) : i in [1..d]];
end function;



// Chain a one-dimensional Zpr-linear transformation with a slot-wise Zpr-linear transformation which maps onto Zpr
// The result is a one-dimensional E-linear transformation which needs to be combined with the slot-wise trace map
function ChainTransformations(oneDimConstants, slotConstant, dim, henselExponent)
    res := [Zx | ];
    for i := 0 to GetDimensionSize(dim) - 1 do
        Append(~res, &+[ApplyFrobeniusPowerPlaintext(slotConstant * oneDimConstants[IJToIndex(i, -k mod d, dim)]
                                                     mod f mod (p ^ henselExponent), k: henselExponent := henselExponent) :
                                                     k in [0..d - 1]] mod (p ^ henselExponent));
    end for;
    return res;
end function;