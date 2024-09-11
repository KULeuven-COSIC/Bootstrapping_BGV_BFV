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