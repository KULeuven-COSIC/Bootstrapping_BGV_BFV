load "Crypto/BFV/BFV.m";
load "Linear maps/PowerOfTwo/Linear_maps.m";
load "Linear maps/GeneralCyclotomic/Linear_maps.m";

assert GetLTVersion() eq 2 or GetLTVersion() eq 3;

// Compute ring structure present on the slots
Zt_F1<y> := GetSlotAlgebra(e);

sk, pk := GenKeyPair();

// Test sparse linear transformations
mmm := EmbedInSlots([Random(t - 1) : ind in [1..l]]);
parts := GetPlaintextParts(mmm);
c := Encrypt(mmm, t, pk);

// Only perform next test for SEAL LT version
if GetLTVersion() eq 2 then
adapted_constants := MatMulAdaptedConstants(SparseConstants(e), e);
switchKeys := [];
for pos := 2 to l do
    Append(~switchKeys, GenSwitchKey(sk, IndexToHypercube(pos)));
end for;
cNew := MatMulBabyGiant(c, adapted_constants, switchKeys);
plaintext := CatZeros(Eltseq(Decrypt(cNew, sk)), n);
result := true;
for index := 1 to n do
    if not IsDivisibleBy(index - 1, d) and plaintext[index] ne 0 then
        result := false;
    end if;
end for;
adapted_constants := MatMulAdaptedConstants(SparseInvConstants(e), e);
cNew := MatMulBabyGiant(cNew, adapted_constants, switchKeys);
"Test sparse linear transformation", result and ((d * Decrypt(cNew, sk)) mod t) eq Decrypt(c, sk);
end if;

// Only perform next test for our LT version if it can be done in one stage and there is complete splitting
if (GetLTVersion() eq 3) and (#mat_dimensions eq 1) and (p mod m eq 1) then
// Construct Eval matrix
dimensions := [1, 2];
dim_sizes := [GetDimensionSize(dim) : dim in dimensions];
matrix := Matrix(Z, l, l, &cat[[y ^ (col * GetHypercubeRepresentative(row)) : col in [0..l - 1]] : row in [1..l]]);
constants := Embed2DMatrixInSlots(matrix, dimensions, e);
adapted_constants := MatMul2DGoodDimensionAdaptedConstants(constants, dimensions, e);

// Generate key switching keys
switchKeysAhead := [];
for index := 2 to &*dim_sizes do
    positions := IndexToSequence(index, [GetDimensionSize(dim) : dim in dimensions]);
    hyperIndexAhead := [var in dimensions select positions[Find(dimensions, var)] else 0 : var in [1..GetNbDimensions()]];
    Append(~switchKeysAhead, GenSwitchKey(sk, hyperIndexAhead));
end for;

// Test on random ciphertext
res := Decrypt(MatMul2DGoodDimensionBabyGiant(c, adapted_constants, dimensions, switchKeysAhead), sk);
result := true;
for element in Eltseq(res) do
    if not (element in parts) then
        result := false;
    end if;
end for;
"Test slot-to-coefficient transformation", result;
end if;

// Only perform next test for our LT version if it can be done in one stage and there is almost complete splitting
if (GetLTVersion() eq 3) and (#mat_dimensions eq 1) and (((p + 1) mod m eq 0) or ((p + (m div 2) + 1) mod m eq 0)) then
// Fully packed slots
parts := GetPlaintextParts(RandPol(t));
mmm := EmbedInSlots([Zx | Evaluate(part, y ^ (m div 4)) : part in parts]);
c := Encrypt(mmm, t, pk);

// Construct Eval matrix
dimension := 1; dim_size := GetDimensionSize(dimension);
matrix := Matrix(Zt_F1, l, l, &cat[[y ^ (col * GetHypercubeRepresentative(row)) : col in [0..l - 1]] : row in [1..l]]);
constants := EmbedMatrixInSlots(matrix, dimension, e);
adapted_constants := MatMul1DGoodDimensionAdaptedConstants(constants, dimension, e);

// Generate key switching keys
switchKeysAhead := [];
for index := 2 to dim_size do
    Append(~switchKeysAhead, GenSwitchKey(sk, IndexToHypercube(index)));
end for;

// Test on random ciphertext
res := Decrypt(MatMul1DGoodDimensionBabyGiant(c, adapted_constants, dimension, switchKeysAhead), sk);
pre_parts := &cat[Eltseq(part) : part in parts] cat [0];
result := true;
for element in Eltseq(res) do
    if not (element in pre_parts) then
        result := false;
    end if;
end for;
"Test slot-to-coefficient transformation", result;
end if;

// Only perform next test for our LT version if there is complete splitting
if (GetLTVersion() eq 3) and (p mod m eq 1) then
// Test sparse 2D matrix transformation in first and last dimension
dimensions := [GetNbDimensions(), 1];
dim_sizes := [GetDimensionSize(dim) : dim in dimensions];
constants, matrix := SparseEvalStage_1Constants(dimensions, e); mat_size := NumberOfRows(matrix);
matrix := SparseMatrix(mat_size, mat_size, [<el[1], el[2], Evaluate(el[3], y)> : el in Eltseq(ChangeRing(matrix, Zx))]);
adapted_constantsAhead, adapted_constantsBack := MatMul2DBadDimensionAdaptedConstants(constants, dimensions, e);

// Generate switch keys
switchKeysAhead := [];
switchKeyMinusD := GenSwitchKey(sk, Get1DHyperIndex(dimensions[2], -dim_sizes[2]));
for index := 2 to &*dim_sizes do
    positions := IndexToSequence(index, dim_sizes);
    hyperIndexAhead := [var in dimensions select positions[Find(dimensions, var)] else 0 : var in [1..GetNbDimensions()]];
    Append(~switchKeysAhead, GenSwitchKey(sk, hyperIndexAhead));
end for;

// Run linear transformation
res := GetPlaintextParts(Decrypt(MatMul2DBadDimensionBabyGiant(c, adapted_constantsAhead, adapted_constantsBack,
                                                               dimensions, switchKeysAhead, switchKeyMinusD), sk));
"Test first stage of slot-to-coefficient transformation", [Evaluate(Zx!el, y) : el in res] eq
                                                           Eltseq(matrix * Matrix(Zt_F1, #parts, 1, parts));
end if;

// Only perform next tests for our LT version if there are multiple stages and complete splitting
if (GetLTVersion() eq 3) and (#mat_dimensions gt 1) and (p mod m eq 1) then
// Test sparse matrix transformation in second dimension
dim := 2; dim_size := GetDimensionSize(dim);
constants, matrix := SparseEvalStage_dimConstants(dim, e); mat_size := NumberOfRows(matrix);
matrix := SparseMatrix(mat_size, mat_size, [<el[1], el[2], Evaluate(el[3], y)> : el in Eltseq(ChangeRing(matrix, Zx))]);
adapted_constantsAhead, adapted_constantsBack := MatMul1DBadDimensionAdaptedConstants(constants, dim, e);

// Generate switch keys
switchKeysAhead := [];
switchKeyMinusD := GenSwitchKey(sk, Get1DHyperIndex(dim, -dim_size));
for pos := 1 to dim_size - 1 do
    Append(~switchKeysAhead, GenSwitchKey(sk, Get1DHyperIndex(dim, pos)));
end for;

// Run linear transformation
res := GetPlaintextParts(Decrypt(MatMul1DBadDimensionBabyGiant(c, adapted_constantsAhead, adapted_constantsBack,
                                                               dim, switchKeysAhead, switchKeyMinusD), sk));
"Test second stage of slot-to-coefficient transformation", [Evaluate(Zx!el, y) : el in res] eq
                                                            Eltseq(matrix * Matrix(Zt_F1, #parts, 1, parts));

// Test sparse matrix transformation in last dimension
dim := GetNbDimensions() - 1; dim_size := GetDimensionSize(dim);
constants, matrix := SparseEvalStage_dimConstants(dim, e); mat_size := NumberOfRows(matrix);
matrix := SparseMatrix(mat_size, mat_size, [<el[1], el[2], Evaluate(el[3], y)> : el in Eltseq(ChangeRing(matrix, Zx))]);
adapted_constants := MatMul1DGoodDimensionAdaptedConstants(constants, dim, e);

// Generate switch keys
switchKeysAhead := [];
for pos := 1 to dim_size - 1 do
    Append(~switchKeysAhead, GenSwitchKey(sk, Get1DHyperIndex(dim, pos)));
end for;

// Run linear transformation
res := GetPlaintextParts(Decrypt(MatMul1DGoodDimensionBabyGiant(c, adapted_constants, dim, switchKeysAhead), sk));
"Test last stage of slot-to-coefficient transformation", [Evaluate(Zx!el, y) : el in res] eq
                                                          Eltseq(matrix * Matrix(Zt_F1, #parts, 1, parts));
end if;

// Take fully packed plaintext
mmm := RandPol(t);
parts := GetPlaintextParts(mmm);
c := Encrypt(mmm, t, pk);

// Only perform next tests for our LT version if there is almost complete splitting
if (GetLTVersion() eq 3) and (((p + 1) mod m eq 0) or ((p + (m div 2) + 1) mod m eq 0)) then
// Test sparse matrix transformation in first dimension
dim := 1; dim_size := GetDimensionSize(dim);
constants, matrix := SparseEvalStage_dimConstants(dim, e); mat_size := NumberOfRows(matrix);
matrix := SparseMatrix(mat_size, mat_size, [<el[1], el[2], Evaluate(el[3], y)> : el in Eltseq(ChangeRing(matrix, Zx))]);
adapted_constantsAhead, adapted_constantsBack := MatMul1DBadDimensionAdaptedConstants(constants, dim, e);

// Generate switch keys
switchKeysAhead := [];
switchKeyMinusD := GenSwitchKey(sk, Get1DHyperIndex(dim, -dim_size));
for pos := 1 to dim_size - 1 do
    Append(~switchKeysAhead, GenSwitchKey(sk, Get1DHyperIndex(dim, pos)));
end for;

// Run linear transformation
pre_parts := [Evaluate(part, y) : part in parts];
res := GetPlaintextParts(Decrypt(MatMul1DBadDimensionBabyGiant(c, adapted_constantsAhead, adapted_constantsBack,
                                                               dim, switchKeysAhead, switchKeyMinusD), sk));
"Test first stage of slot-to-coefficient transformation", [Evaluate(Zx!el, y) : el in res] eq
                                                           Eltseq(matrix * Matrix(Zt_F1, #parts, 1, pre_parts));

// Test sparse matrix transformation in last dimension
dim := GetNbDimensions(); dim_size := GetDimensionSize(dim);
constants, matrix := SparseEvalStage_dimConstants(dim, e); mat_size := NumberOfRows(matrix);
matrix := SparseMatrix(mat_size, mat_size, [<el[1], el[2], Evaluate(el[3], y)> : el in Eltseq(ChangeRing(matrix, Zx))]);
adapted_constants := MatMul1DGoodDimensionAdaptedConstants(constants, dim, e);

// Generate switch keys
switchKeysAhead := [];
for pos := 1 to dim_size - 1 do
    Append(~switchKeysAhead, GenSwitchKey(sk, Get1DHyperIndex(dim, pos)));
end for;

// Run linear transformation
res := GetPlaintextParts(Decrypt(MatMul1DGoodDimensionBabyGiant(c, adapted_constants, dim, switchKeysAhead), sk));
"Test last stage of slot-to-coefficient transformation", [Evaluate(Zx!el, y) : el in res] eq
                                                          Eltseq(matrix * Matrix(Zt_F1, #parts, 1, pre_parts));
end if;

// Generate switch keys
frobeniusSwitchKeys := [];
for exp := 1 to d - 1 do
    Append(~frobeniusSwitchKeys, GenSwitchKey(sk, Modexp(p, exp, m)));
end for;

// Take fully packed plaintext
mmm := RandPol(t);
c := Encrypt(mmm, t, pk);

// Check if both maps are inverse of each other
adapted_constants := MatMulSlotsAdaptedConstants(ComputeMConstants(e), e);
adapted_constants_inverse := MatMulSlotsAdaptedConstants(ComputeMInvConstants(e), e);
res := Decrypt(MatMulSlotsBabyGiant(MatMulSlotsBabyGiant(c, adapted_constants, frobeniusSwitchKeys),
                                                         adapted_constants_inverse, frobeniusSwitchKeys), sk);

"Test M cancels its inverse", res eq mmm;