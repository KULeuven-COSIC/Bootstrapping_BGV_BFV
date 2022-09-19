// Compute the constants necessary during the linear transformations
//--------------------------
load "Linear maps/General.m";
load "Linear maps/Linear_algebra.m";
load "Linear maps/PowerOfTwo/MatMul.m";
load "Linear maps/PowerOfTwo/CoefficientSelection.m";

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
    assert usePowerOfTwo;
    
    // Compute two vectors of length l such that v_i --> w_i
    v := [EmbedInSlots([ind1 eq ind2 select 1 else 0: ind2 in [1..l]]: henselExponent := henselExponent): ind1 in [1..l]];
    w := [x ^ (d * (ind - 1)) : ind in [1..l]];

    return GetSparseEvalConstants(v, w, henselExponent);
end function;

// Compute the constants for the inverse sparse linear transformation
function SparseInvConstants(henselExponent)
    assert usePowerOfTwo;

    // Compute two vectors of length l such that w_i --> v_i
    v := [EmbedInSlots([ind1 eq ind2 select 1 else 0: ind2 in [1..l]]: henselExponent := henselExponent): ind1 in [1..l]];
    w := [d * (x ^ (d * (ind - 1))) : ind in [1..l]];

    return GetSparseEvalConstants(w, v, henselExponent);
end function;