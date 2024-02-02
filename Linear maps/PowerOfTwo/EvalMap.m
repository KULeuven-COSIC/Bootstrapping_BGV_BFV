// Compute the bit-reversed number
function BitReverse(number, nb_digits)
    return SequenceToInteger(Reverse(IntegerToSequence(number, 2, nb_digits)), 2);
end function;

// Compute n x n S-matrix
function ComputeSMatrix(n, W_4n, ring)
    return Matrix(ring, n, n, &cat[[W_4n ^ ((5 ^ row) * BitReverse(col, Valuation(n, 2))) : col in [0..n - 1]] :
                                                                                            row in [0..n - 1]]);
end function;

// Compute n x n W-matrix
function ComputeWMatrix(n, W_8n, ring)
    return DiagonalMatrix(ring, n, [W_8n ^ (5 ^ i) : i in [0..n - 1]]);
end function;

// Decompose S-matrix (of dimension m/4 x m/4)
function ComputeSFactors(m, W_m, ring)
    n := m div 4;
    if n eq 2 then
        return [ComputeSMatrix(n, W_m, ring)];
    else
        res := [BlockMatrix(2, 2, [IdentityMatrix(ring, n div 2), ComputeWMatrix(n div 2, W_m, ring),
                                   IdentityMatrix(ring, n div 2), -ComputeWMatrix(n div 2, W_m, ring)])];
        tmp := ComputeSFactors(m div 2, W_m ^ 2, ring);
        for index := 1 to #tmp do
            Append(~res, KroneckerProduct(IdentityMatrix(ring, 2), tmp[index]));
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
        Append(~result, BlockMatrix(2, 2, [SFactors1[index], ZeroMatrix(ring, m div 4, m div 4),
                                           ZeroMatrix(ring, m div 4, m div 4), SFactors2[index]]));
    end for;
    Append(~result, BlockMatrix(2, 2, [IdentityMatrix(ring, m div 4), (W_m ^ (m div 4)) * IdentityMatrix(ring, m div 4),
                                       IdentityMatrix(ring, m div 4), (W_m ^ (-m div 4)) * IdentityMatrix(ring, m div 4)]));
    return result;
end function;