// Compute the constants necessary during the linear transformations
//--------------------------
assert GetLTVersion() ne 0;
load "Linear maps/General.m";
load "Linear maps/Linear_algebra.m";
load "Linear maps/PowerOfTwo/MatMul.m";
load "Linear maps/PowerOfTwo/CoefficientSelection.m";
load "Linear maps/PowerOfTwo/EvalMap.m";

/*** Chen/Han linear transformations ***/

// Compute the constants for the sparse evaluation map based on l linear independent input-output pairs
function GetSparseEvalConstants(inputs, outputs, henselExponent)
    // Set up system of equations
    Zt_F1<y> := GetSlotAlgebra(henselExponent);
    constants := [[] : ind in [1..l]];
    for slotIndex := 1 to l do
        matrix := Matrix(Zx, l, l, &cat[[Evaluate(inputs[row], y ^ (GetHypercubeRepresentative(slotIndex) *
                                                                    GetInverseHypercubeRepresentative(col))) :
                                                                    col in [1..l]] : row in [1..l]]);
        vector := Matrix(Zx, l, 1, [Evaluate(outputs[ind], y ^ GetHypercubeRepresentative(slotIndex)) : ind in [1..l]]);
        solution := SolveSystem(matrix, vector, henselExponent);

        // Put solution in the slots
        for index := 1 to l do
            Append(~constants[index], solution[index]);
        end for;
    end for;
    return [EmbedInSlots(constants[ind]: henselExponent := henselExponent) : ind in [1..l]];
end function;

// Compute the constants for the sparse linear transformation
function SparseConstants(henselExponent)
    // Compute two vectors of length l such that v_i --> w_i
    v := [EmbedInSlots([ind1 eq ind2 select 1 else 0: ind2 in [1..l]]: henselExponent := henselExponent): ind1 in [1..l]];
    w := [x ^ (d * (ind - 1)) : ind in [1..l]];

    return GetSparseEvalConstants(v, w, henselExponent);
end function;

// Compute the constants for the inverse sparse linear transformation
function SparseInvConstants(henselExponent)
    // Compute two vectors of length l such that w_i --> v_i
    v := [EmbedInSlots([ind1 eq ind2 select 1 else 0: ind2 in [1..l]]: henselExponent := henselExponent): ind1 in [1..l]];
    w := [d * (x ^ (d * (ind - 1))) : ind in [1..l]];

    return GetSparseEvalConstants(w, v, henselExponent);
end function;



/*** Our linear transformations ***/

// Multiply sequence of sparse l x l matrices
function MultiplySparseMatrices(factors, ring)
    return (#factors eq 0) select IdentitySparseMatrix(ring, l) else &*factors;
end function;

/*** E-linear maps ***/

// Compute the constants for a two-dimensional E-linear transformation
// in the given dimensions which is specified by the given matrix
// The same matrix is used for each hypercolumn
function Embed2DMatrixInSlots(matrix, dimensions, henselExponent)
    dim_sizes := [GetDimensionSize(dim) : dim in dimensions];
    res := [];

    // For each rotation index i, we compute one constant
    for i := 1 to &*dim_sizes do
        i_seq := IndexToSequence(i, dim_sizes);
        slotContent := [];

        // Complicated way to compute constant because rotations are two-dimensional
        for index := 1 to l do
            hyperIndex := IndexToHypercube(index);
            fromIndex := SequenceToIndex([(hyperIndex[dimensions[j]] - i_seq[j]) mod dim_sizes[j] : j in [1..2]], dim_sizes);
            toIndex := SequenceToIndex([hyperIndex[dim] : dim in dimensions], dim_sizes);
            Append(~slotContent, matrix[toIndex][fromIndex]);
        end for;
        Append(~res, EmbedInSlots(slotContent: henselExponent := henselExponent));
    end for;
    return res;
end function;

// Compute the constants for a two-dimensional E-linear transformation
// in the given dimensions which is specified by the given matrix
// The matrix specifies the full linear transformation over all slots
function EmbedSparse2DMatrixInSlots(matrix, dimensions, henselExponent)
    dim_sizes := [GetDimensionSize(dim) : dim in dimensions];
    res := [];

    // For each rotation index i, we compute one constant
    for i := 1 to &*dim_sizes do
        i_seq := IndexToSequence(i, dim_sizes);
        slotContent := [];

        // Complicated way to compute constant because rotations are two-dimensional
        for toIndex := 1 to l do
            hyperIndex := IndexToHypercube(toIndex);
            fromIndex := HypercubeToIndex([var in dimensions select (hyperIndex[var] - i_seq[Position(dimensions, var)]) mod
                                                                     dim_sizes[Position(dimensions, var)]
                                                             else hyperIndex[var] : var in [1..GetNbDimensions()]]);
            Append(~slotContent, matrix[toIndex][fromIndex]);
        end for;
        Append(~res, EmbedInSlots(slotContent: henselExponent := henselExponent));
    end for;
    return res;
end function;

// Compute the constants for the first stage of the decomposed sparse evaluation map
// The corresponding sparse matrix is returned as a second value
function SparseEvalStage_1Constants(dimensions, henselExponent)
    // Decompose the FFT-like map
    Zt_F1<y> := GetSlotAlgebra(henselExponent);
    factors := ComputeCRTFactors(m div d, y ^ d, Zt_F1);

    // Take multiple stages together
    matrix := MultiplySparseMatrices(factors[#factors - Valuation(&*[GetDimensionSize(dim) : dim in dimensions], 2) + 1..
                                             #factors], Zt_F1);
    return EmbedSparse2DMatrixInSlots(matrix, dimensions, henselExponent), matrix;
end function;

// Compute the constants for the first stage of the decomposed sparse inverse evaluation map
// The corresponding sparse matrix is returned as a second value
function SparseEvalInvStage_1Constants(dimensions, henselExponent)
    // Decompose the FFT-like map
    Zt_F1<y> := GetSlotAlgebra(henselExponent);
    factors := ComputeCRTFactors(m div d, y ^ d, Zt_F1);

    // Take multiple stages together
    matrix := MultiplySparseMatrices(factors[#factors - Valuation(&*[GetDimensionSize(dim) : dim in dimensions], 2) + 1..
                                             #factors], Zt_F1);
    matrix := InvertMatrixOverSlotAlgebra(matrix, henselExponent); size := NumberOfRows(matrix);
    matrix := SparseMatrix(size, size, [<el[1], el[2], Evaluate(el[3], y)> : el in Eltseq(matrix)]);
    return EmbedSparse2DMatrixInSlots(matrix, dimensions, henselExponent), matrix;
end function;

// Compute the constants for a one-dimensional E-linear transformation
// in the given dimensions which is specified by the given matrix
// The matrix specifies the full linear transformation over all slots
function EmbedSparseMatrixInSlots(matrix, dim, henselExponent)
    dim_size := GetDimensionSize(dim);
    res := [];

    // For each rotation index i, we compute one constant
    for i := 0 to dim_size - 1 do
        slotContent := [];

        // Complicated way to compute constant because rotations are two-dimensional
        for toIndex := 1 to l do
            hyperIndex := IndexToHypercube(toIndex);
            fromIndex := HypercubeToIndex([var eq dim select (hyperIndex[var] - i) mod dim_size
                                                      else hyperIndex[var] : var in [1..GetNbDimensions()]]);
            Append(~slotContent, matrix[toIndex][fromIndex]);
        end for;
        Append(~res, EmbedInSlots(slotContent: henselExponent := henselExponent));
    end for;
    return res;
end function;

// Compute the constants for the dim-th stage of the decomposed sparse evaluation map
// The corresponding sparse matrix is returned as a second value
function SparseEvalStage_dimConstants(dim, henselExponent)
    // Decompose the FFT-like map
    Zt_F1<y> := GetSlotAlgebra(henselExponent);
    if p mod 4 eq 1 then
        factors := ComputeCRTFactors(m div d, y ^ d, Zt_F1);
    else
        factors := ComputeSFactors(2 * m div d, y ^ (d div 2), Zt_F1);
    end if;

    // Take multiple stages together
    nb_prev := Valuation(&*mat_dimensions[1..dim - 1], 2);
    matrix := MultiplySparseMatrices(factors[#factors - nb_prev - Valuation(GetDimensionSize(dim), 2) + 1..
                                             #factors - nb_prev], Zt_F1);
    return EmbedSparseMatrixInSlots(matrix, dim, henselExponent), matrix;
end function;

// Compute the constants for the dim-th stage of the decomposed sparse inverse evaluation map
// The corresponding sparse matrix is returned as a second value
function SparseEvalInvStage_dimConstants(dim, henselExponent)
    // Decompose the FFT-like map
    Zt_F1<y> := GetSlotAlgebra(henselExponent);
    if p mod 4 eq 1 then
        factors := ComputeCRTFactors(m div d, y ^ d, Zt_F1);
    else
        factors := ComputeSFactors(2 * m div d, y ^ (d div 2), Zt_F1);
    end if;

    // Take multiple stages together
    nb_prev := Valuation(&*mat_dimensions[1..dim - 1], 2);
    matrix := MultiplySparseMatrices(factors[#factors - nb_prev - Valuation(GetDimensionSize(dim), 2) + 1..
                                             #factors - nb_prev], Zt_F1);
    matrix := InvertMatrixOverSlotAlgebra(matrix, henselExponent); size := NumberOfRows(matrix);
    matrix := SparseMatrix(size, size, [<el[1], el[2], Evaluate(el[3], y)> : el in Eltseq(matrix)]);
    return EmbedSparseMatrixInSlots(matrix, dim, henselExponent), matrix;
end function;

/*** Slot-wise Z-linear maps ***/

// Compute the ring constants for a slot-wise Z-linear transformation
// which is specified by the given E-constants
function EmbedSlotWiseConstantsInSlots(constants, henselExponent)
    return [EmbedInSlots([constants[j + d * index] : index in [0..l - 1]]: henselExponent := henselExponent) : j in [1..d]];
end function;

// Compute the ring constants for the slot-wise Z-linear transformation M^(-1)
// The set of E-constants is returned as a second value
function ComputeMInvConstants(henselExponent)
    if p mod 4 eq 1 then
        inputs := [x ^ j : j in [0..d - 1]];
        outputs := &cat[[x ^ ((GetHypercubeRepresentative(index) * j) mod m) : j in [0..d - 1]] : index in [1..l]];
    else
        inputs := [j lt d div 2 select x ^ j else x ^ ((m div 4) + j - (d div 2)) : j in [0..d - 1]];
        outputs := &cat[[j lt d div 2 select x ^ ((GetHypercubeRepresentative(index) * j) mod m)
                                      else x ^ ((GetHypercubeRepresentative(index) * ((m div 4) + j - (d div 2))) mod m) :
                         j in [0..d - 1]] : index in [1..l]];
    end if;

    // Find the constants
    constants := GetMapConstants(inputs, outputs, henselExponent);
    return EmbedSlotWiseConstantsInSlots(constants, henselExponent), constants;
end function;

// Compute the ring constants for the slot-wise Z-linear transformation M
function ComputeMConstants(henselExponent)
    _, inverse_constants := ComputeMInvConstants(henselExponent);
    matrices := [];
    for index := 1 to l do
        matrix := MapToMatrix(inverse_constants[d * (index - 1) + 1..d * index], henselExponent);
        Append(~matrices, ChangeRing(ChangeRing(matrix, Integers(p ^ henselExponent)) ^ (-1), Z));
    end for;

    // Find the constants
    return EmbedSlotWiseConstantsInSlots(MatricesToMaps(matrices, henselExponent), henselExponent);
end function;

/*** Merging multiple maps into one ***/

// Merge the inner and outer map such that their generators are concatenated
// The variable inner_map_first (true or false) indicates whether the inner map is the first one in the concatenation
// From the outer dimensions, only the last one can be a bad dimension (it must be specified via outer_bad_dimension)
// Note: this function does not turn a bad dimension into a good one (this has to be done manually afterwards)
function MergeMaps(inner_constants, inner_generators, inner_dim_sizes, outer_constants, outer_generators, outer_dim_sizes,
                   inner_map_first, henselExponent: outer_bad_dimension := 0)
    // Concatenate generators and dim_sizes
    generators := inner_map_first select inner_generators cat outer_generators else outer_generators cat inner_generators;
    dim_sizes := inner_map_first select inner_dim_sizes cat outer_dim_sizes else outer_dim_sizes cat inner_dim_sizes;

    // Compute new constants one by one
    constants := [];
    for index := 1 to &*dim_sizes do
        seq := IndexToSequence(index, dim_sizes);
        inner_seq := inner_map_first select seq[1..#inner_generators] else seq[#outer_generators + 1..#seq];
        outer_seq := inner_map_first select seq[#inner_generators + 1..#seq] else seq[1..#outer_generators];

        // Multiply two constants
        inner_constant := inner_constants[SequenceToIndex(inner_seq, inner_dim_sizes)];
        outer_constant := outer_constants[SequenceToIndex(outer_seq, outer_dim_sizes)];

        // Inner constant needs to be adapted for outer automorphism
        exp := RotToExp(outer_generators, outer_seq);
        if outer_bad_dimension eq 0 then
            inner_constant := ApplyAutomorphismPlaintext(inner_constant, exp: henselExponent := henselExponent);
        else
            inner_constant := RotateSlotsGeneralPlaintext(inner_constant, exp, outer_bad_dimension, outer_seq[#outer_seq]:
                                                          henselExponent := henselExponent);
        end if;

        // Multiply constants and append to sequence
        Append(~constants, ((inner_constant * outer_constant) mod f) mod (p ^ henselExponent));
    end for;
    return constants, generators, dim_sizes;
end function;

// Merge the old set of generators into the new one
// Only the last old dimension can be a bad dimension (it must be specified via old_bad_dimension)
// All new dimensions must be good dimensions
function MergeGenerators(old_constants, old_generators, old_dim_sizes, new_generators, new_dim_sizes, henselExponent:
                         old_bad_dimension := 0)
    // Store new constants
    new_constants := [Zx | 0 : index in [1..&*new_dim_sizes]];
    for old_index := 1 to &*old_dim_sizes do
        old_seq := IndexToSequence(old_index, old_dim_sizes); exp := RotToExp(old_generators, old_seq);
        new_seq := ExpToRot(new_generators, new_dim_sizes, exp); new_index := SequenceToIndex(new_seq, new_dim_sizes);

        // Split old constant in one or two parts
        if old_bad_dimension eq 0 then
            new_constants[new_index] +:= old_constants[old_index];
        else
            // New constant ahead
            maskAhead := GetAdaptedMaskAhead(old_bad_dimension, old_seq[#old_seq], henselExponent);
            new_constants[new_index] +:= (maskAhead * old_constants[old_index]) mod f;
            new_constants[new_index] := new_constants[new_index] mod (p ^ henselExponent);

            // New constant back
            maskBack := GetAdaptedMaskBack(old_bad_dimension, old_seq[#old_seq], henselExponent);
            old_seq[#old_seq] -:= GetDimensionSize(old_bad_dimension); exp := RotToExp(old_generators, old_seq);
            new_seq := ExpToRot(new_generators, new_dim_sizes, exp); new_index := SequenceToIndex(new_seq, new_dim_sizes);
            new_constants[new_index] +:= (maskBack * old_constants[old_index]) mod f;
            new_constants[new_index] := new_constants[new_index] mod (p ^ henselExponent);
        end if;
    end for;
    return new_constants;
end function;

/* GBFV linear transformations */

// Precompute list that converts hypercube representative to index in our natural ordering
function RepresentativeToIndexList()
    res := []; currentIndex := 0;
    for major := 0 to (n_prime div 2) - 1 do
        for minor := 0 to 1 do
            currentIndex +:= 1;
            representative := ((((-1) ^ minor) * Modexp(5, major, 2 * n_prime))) mod (2 * n_prime);
            res[(representative div 2) + 1] := currentIndex;
        end for;
    end for;
    return res;
end function;

// Convert the given hypercube representative to an index in our natural ordering
precompRepresentativeToIndex := RepresentativeToIndexList();
function RepresentativeToIndex(representative)
    assert representative mod 2 eq 1;   // Input should be odd
    return precompRepresentativeToIndex[((representative mod (2 * n_prime)) div 2) + 1];
end function;

// Compute the constants for an arbitrary linear transformation over a base field or base ring
// The matrix must be specified in our natural basis and should be square of size n_prime
// Symmetry will be applied if the matrix is too small to fit in the R-LWE ring
function EmbedGeneralMatrixInSlots(matrix, generators, dim_sizes, henselExponent: dim_good := [false : i in generators])
    assert NumberOfRows(matrix) eq NumberOfColumns(matrix);
    assert NumberOfRows(matrix) eq n_prime;
    res := [];

    // Compute loop sizes and starting points
    loop_sizes := [dim_good[i] select dim_sizes[i] else 2 * dim_sizes[i] - 1 : i in [1..#generators]];
    minima := [dim_good[i] select 0 else -dim_sizes[i] + 1 : i in [1..#generators]];

    // For each rotation index i, we compute one constant
    for i := 1 to &*loop_sizes do
        i_seq := IndexToSequence(i, loop_sizes: minima := minima);
        auto_exp := RotToExp(generators, i_seq); slotContent := [];

        // Compute matrix indices
        for toIndex := 1 to l do
            toRep := GetHypercubeRepresentative(toIndex); fromRep := toRep * auto_exp;
            Append(~slotContent, matrix[RepresentativeToIndex(toRep)][RepresentativeToIndex(fromRep)]);
        end for;
        Append(~res, EmbedInSlots(slotContent: henselExponent := henselExponent));

        // Put the used entries to zero so that they cannot be reused
        for toIndex := 1 to l do
            toRep := GetHypercubeRepresentative(toIndex); fromRep := toRep * auto_exp;
            matrix[RepresentativeToIndex(toRep)][RepresentativeToIndex(fromRep)] := 0;
        end for;
    end for;

    // We should have used all matrix elements by now
    assert #Eltseq(matrix) eq 0;
    return res;
end function;

// Convert the given offsets and good/bad indicators to generators and updated good/bad indicators
// The optional argument positive_exponents indicates whether 5 or 5 ^ (-1) will be used as a generator
// Note: good in this context simply means that we do not need the inverse generator to implement the linear transformation
function OffsetsToGenerators(offsets, are_offsets_good, positive_exponents)
    // Combine sequences into one and sort
    comb := [<offsets[i], are_offsets_good[i]> : i in [1..#offsets]];
    Sort(~comb, func<x, y | x[1] - y[1]>);

    // Reproduce two sequences
    offsets := [comb[i][1] : i in [1..#comb]];
    are_offsets_good := [comb[i][2] : i in [1..#comb]];

    // Loop over all offsets are join consecutive ones if possible
    g := positive_exponents select 5 else Modinv(5, 2 * n_prime);
    generators := []; dim_sizes := []; dim_good := [];
    for index := 1 to #offsets do
        // Check if we can merge dimension with the previous one
        if (index gt 1) and (offsets[index] gt 2) and (offsets[index] eq 2 * offsets[index - 1]) then
            dim_sizes[#dim_sizes] *:= 2; dim_good[#dim_good] and:= are_offsets_good[index];
            dim_good[#dim_good] or:= (offsets[index] eq (n_prime div 2));
        elif offsets[index] eq 1 then   // New automorphism in minor dimension
            Append(~generators, -1); Append(~dim_sizes, 2); Append(~dim_good, true);
        else                            // New automorphism in major dimension
            Append(~generators, Modexp(g, offsets[index] div 2, 2 * n_prime));
            Append(~dim_sizes, 2); Append(~dim_good, are_offsets_good[index] or (offsets[index] eq (n_prime div 2)));
        end if;
    end for;
    return generators, dim_sizes, dim_good;
end function;

// Compute the constants for the decomposed sparse evaluation map of GBFV
function GBFVSparseEvalConstants(stage, henselExponent)
    if n_double_prime eq 1 then
        return [], [], [], [];
    end if;

    // Decompose the FFT-like map
    Zt_F1<y> := GetSlotAlgebra(henselExponent);
    factors, offsets, are_offsets_good := ComputeGBFVFactors(n_prime, n_double_prime, y ^ (n div n_double_prime),
                                                             Zt_F1, henselExponent, false);

    // Take multiple stages together
    start_index := #factors - Valuation(&*gbfv_mat_dimensions[1..stage], 2) + 1;
    end_index := #factors - Valuation(&*gbfv_mat_dimensions[1..stage - 1], 2);
    matrix := MultiplySparseMatrices(factors[start_index..end_index], Zt_F1);
    generators, dim_sizes, dim_good := OffsetsToGenerators(offsets[start_index..end_index],
                                                           are_offsets_good[start_index..end_index], false);

    // Finally compute the relevant constants
    return EmbedGeneralMatrixInSlots(matrix, generators, dim_sizes, henselExponent:
                                     dim_good := dim_good), generators, dim_sizes, dim_good;
end function;

// Compute the constants for the decomposed sparse inverse evaluation map of GBFV
function GBFVSparseEvalInvConstants(stage, henselExponent)
    if n_double_prime eq 1 then
        return [], [], [], [];
    end if;

    // Decompose the FFT-like map
    Zt_F1<y> := GetSlotAlgebra(henselExponent);
    factors, offsets, are_offsets_good := ComputeGBFVFactors(n_prime, n_double_prime, y ^ (n div n_double_prime),
                                                             Zt_F1, henselExponent, true);

    // Take multiple stages together
    start_index := Valuation(&*gbfv_mat_dimensions[1..stage - 1], 2) + 1;
    end_index := Valuation(&*gbfv_mat_dimensions[1..stage], 2);
    matrix := MultiplySparseMatrices(factors[start_index..end_index], Zt_F1);
    generators, dim_sizes, dim_good := OffsetsToGenerators(offsets[start_index..end_index],
                                                           are_offsets_good[start_index..end_index], true);

    // Finally compute the relevant constants
    return EmbedGeneralMatrixInSlots(matrix, generators, dim_sizes, henselExponent:
                                     dim_good := dim_good), generators, dim_sizes, dim_good;
end function;