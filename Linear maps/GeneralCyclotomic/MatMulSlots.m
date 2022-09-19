// Compute the adapted constants for the baby-step/giant-step algorithm
function MatMulSlotsAdaptedConstants(constants, henselExponent)
    g, h := GetBabyGiantParams(d);

    // Compute adapted constants
    adapted_constants := [];
    for k := 0 to h - 1 do
        for j := 0 to g - 1 do
            // Compute which constant to use
            i := j + g * k;
            if i ge d then
                continue;
            end if;

            // Compute Frobenius
            frob_size := (-g * k) mod d;
            Append(~adapted_constants, ApplyFrobeniusPowerPlaintext(constants[i + 1], frob_size:
                                                                    henselExponent := henselExponent));
        end for;
    end for;
    return adapted_constants;
end function;

// Apply slot-wise Zpr-linear transformation to a ciphertext c
// All evaluation keys need to be provided, except for the trivial one
function MatMulSlots(c, constants, switchKeys)
    // Trivial implementation (not yet optimized)
    res := MulConstant(c, constants[1]);

    // Apply each Frobenius map separately
    for i := 2 to d do
        res := Add(res, MulConstant(ApplyFrobeniusPowerCiphertext(c, i - 1, switchKeys[i - 1]), constants[i]));
    end for;
    return res;
end function;

// Apply slot-wise Zpr-linear transformation to a ciphertext c
function MatMulSlotsBabyGiant(c, adapted_constants, switchKeys)
    // Baby-step/giant-step logic
    g, h := GetBabyGiantParams(d);

    // Precompute small number of Frobenius maps
    v := [c];
    for j := 1 to g - 1 do
        Append(~v, ApplyFrobeniusPowerCiphertext(c, j, switchKeys[j]));
    end for;

    // Compute remaining sum
    w := GetZeroCiphertext(c);
    for k := 0 to h - 1 do
        tmp := GetZeroCiphertext(c);
        for j := 0 to g - 1 do
            // Compute which constant to use
            i := j + g * k;
            if i ge d then
                continue;
            end if;

            // Compute inner sum
            tmp := Add(tmp, MulConstant(v[j + 1], adapted_constants[i + 1]));
        end for;

        // Compute outer sum
        if k eq 0 then
            w := Add(w, tmp);
        else
            w := Add(w, ApplyFrobeniusPowerCiphertext(tmp, g * k, switchKeys[g * k]));
        end if;
    end for;
    return w;
end function;



// Unpack the slots of the given ciphertext
function UnpackSlots(c, constants, switchKeys)
    // List of consecutive applications of the Frobenius map to
    // the given ciphertext
    frobeniusMaps := [c];
    for i := 1 to d - 1 do
        Append(~frobeniusMaps, ApplyFrobeniusPowerCiphertext(c, i, switchKeys[i]));
    end for;

    // Compute all results
    res := [];
    for j := 0 to d - 1 do
        // Compute current result
        current_result := GetZeroCiphertext(c);
        for i := 1 to d do
            current_result := Add(current_result, MulConstant(frobeniusMaps[i], constants[((i + j - 1) mod d) + 1]));
        end for;
        Append(~res, current_result);
    end for;
    return res;
end function;

// Repack the slots of the given sequence of ciphertexts
function RepackSlots(c_seq, repackConstants)
    c := GetZeroCiphertext(c_seq[1]);
    for i := 1 to d do
        c := Add(c, MulConstant(c_seq[i], repackConstants[i]));
    end for;
    return c;
end function;



// Compute the slot-wise trace map on all slots of the given ciphertext
function SlotwiseTrace(c, frobeniusSwitchKeys)
    result := c;
    exponent := 1;
    for bit in Remove(Reverse(IntegerToSequence(d, 2)), 1) do
        result := Add(ApplyFrobeniusPowerCiphertext(result, exponent, frobeniusSwitchKeys[exponent]), result);
        if bit eq 1 then
            result := Add(ApplyFrobeniusPowerCiphertext(result, 1, frobeniusSwitchKeys[1]), c);
        end if;
        exponent := 2 * exponent + bit;
    end for;
    return result;
end function;