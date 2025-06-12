load "Bootstrapping/GBFV_better_recrypt.m";

// Encrypt strings
function EncryptStrings(str_a, str_b, alphabet_size, pk)
    assert alphabet_size le 36;
    assert #str_a eq #str_b;
    assert &and[#str_a[i] eq #str_b[i] : i in [1..#str_a]];

    // Compute length of string and list
    len_str := CeilPowerOfTwo(Maximum([#str : str in str_a]));
    len_lst := n_double_prime div len_str;
    assert #str_a le len_lst;

    // Pad with extra characters
    padding := ["A" ^ len_str : i in [#str_a + 1..len_lst]];
    str_a := [str cat ("A" ^ (len_str - #str)) : str in str_a] cat padding;
    str_b := [str cat ("A" ^ (len_str - #str)) : str in str_b] cat padding;

    parts_a := []; parts_b := [];
    for slot := 0 to n - 1 do
        if slot mod (n div n_double_prime) eq 0 then
            index := slot div (n div n_double_prime);
            ind_1 := index mod len_lst; ind_2 := index div len_lst;
            Append(~parts_a, StringToInteger(str_a[ind_1 + 1][ind_2 + 1], alphabet_size));
            Append(~parts_b, StringToInteger(str_b[ind_1 + 1][ind_2 + 1], alphabet_size));
        else
            Append(~parts_a, 0); Append(~parts_b, 0);
        end if;
    end for;
    return Encrypt(EmbedInSlots(parts_a: henselExponent := 1), gbfvModulus, pk),
           Encrypt(EmbedInSlots(parts_b: henselExponent := 1), gbfvModulus, pk);
end function;

// Decrypt relevant results
function DecryptEditDistances(ctxt_edit, sk, nb_words)
    parts := GetPlaintextParts(Decrypt(ctxt_edit, sk): henselExponent := 1);
    return [Z | parts[(n div n_double_prime) * i + 1] : i in [0..nb_words - 1]];
end function;



// Compute chunk size
// A chunk refers to the capacity reserved for one character in each string
function ChunkSize(len_str)
    return n div len_str;
end function;

// Compute how many characters are already filled before iteration k
function TotalFilled(len_str, k)
    if k le len_str then
        return (k - 1) * (k - 2) div 2;
    else
        return (len_str * (len_str - 1) + (3 * len_str - k + 2) * (k - len_str - 1)) div 2;
    end if;
end function;

// Compute how many characters are filled in the target ciphertext
function TargetFilled(len_str, nb_total_filled)
    return nb_total_filled mod len_str;
end function;

// Compute how many ciphertexts are filled so far
function CiphertextsFilled(len_str, nb_total_filled)
    return nb_total_filled div len_str;
end function;

// Compute how many characters are filled in the input ciphertext of iteration k
function InputFilled(len_str, k)
    if k le len_str then
        return k - 1;
    else
        return 2 * len_str - k + 1;
    end if;
end function;

// Compute how many characters are left empty at the start of the input ciphertext
function InputEmpty(len_str, k)
    if k le len_str then
        return 0;
    else
        return k - len_str - 1;
    end if;
end function;



// Precompute evaluation keys
function PrecompKeys(sk, len_str)
    chunk_size := ChunkSize(len_str);
    expand_keys := [[], [], []]; extract_keys := [];
    for index := 2 to 2 * len_str do
        for i := 1 to 2 do          // We need to generate keys for forward and reverse direction
            nb_total_filled := TotalFilled(len_str, index);
            nb_target_filled := TargetFilled(len_str, nb_total_filled);
            nb_input_empty := InputEmpty(len_str, i eq 1 select index else (2 * len_str - index + 2));
            Append(~expand_keys[i], GenSwitchKey(sk, GetInverseHypercubeRepresentative((((nb_target_filled - nb_input_empty) *
                                                                                          chunk_size) mod n) + 1)));

            // Also generate keys for delta extraction
            if i eq 1 then
                Append(~extract_keys, GenSwitchKey(sk, GetHypercubeRepresentative(((nb_target_filled * chunk_size) mod n) + 1)));
            end if;
        end for;
    end for;
    for index := 1 to len_str do    // Additional keys for reverting the array
        Append(~expand_keys[3], GenSwitchKey(sk, GetInverseHypercubeRepresentative((((1 - 2 * index) * chunk_size) mod n) + 1)));
    end for;

    // Interleaved rotation keys
    key_right := GenSwitchKey(sk, GetInverseHypercubeRepresentative(chunk_size + 1));
    key_left := GenSwitchKey(sk, GetHypercubeRepresentative(chunk_size + 1));
    boot_shift_key := GenSwitchKey(sk, GetHypercubeRepresentative(n div 2 + 1));

    return expand_keys, extract_keys, key_right, key_left, boot_shift_key;
end function;

// Reverse order of slots
function ReverseCharacters(ctxt, len_str, reverse_keys)
    chunk_size := ChunkSize(len_str);
    res := GetZeroCiphertext(ctxt);
    for index := 1 to len_str do
        ctxt_extract := MulConstant(ctxt, EmbedInSlots([(i le (index - 1) * chunk_size) or
                                                        (i gt index * chunk_size) select 0 else 1 : i in [1..n]]:
                                                         henselExponent := 1));
        res := Add(res, ApplyAutomorphismCiphertext(ctxt_extract,
                        GetInverseHypercubeRepresentative((((1 - 2 * index) * chunk_size) mod n) + 1), reverse_keys[index]));
    end for;
    return res;
end function;

// Create len_str ciphertexts by duplicating elements
function ExpandCharacters(ctxt, len_str, expand_keys: reverse := false)
    if reverse then     // Reverse order of elements
        ctxt := ReverseCharacters(ctxt, len_str, expand_keys[3]);
    end if;

    chunk_size := ChunkSize(len_str); nb_total_filled := 0;
    res := [GetZeroCiphertext(ctxt) : i in [1..len_str]];
    for index := 2 to 2 * len_str do
        // Possibly reverse order of iteration
        k := reverse select (2 * len_str - index + 2) else index;
        nb_target_filled := TargetFilled(len_str, nb_total_filled);
        nb_ctxt_filled := CiphertextsFilled(len_str, nb_total_filled);
        nb_input_filled := InputFilled(len_str, k);
        nb_input_empty := InputEmpty(len_str, k);

        // Move elements to the right place
        ctxt_move := ApplyAutomorphismCiphertext(ctxt,
                     GetInverseHypercubeRepresentative((((nb_target_filled - nb_input_empty) * chunk_size) mod n) + 1),
                     expand_keys[reverse select 2 else 1][index - 1]);

        // Add to first target ciphertext
        res[nb_ctxt_filled + 1] := Add(res[nb_ctxt_filled + 1], MulConstant(ctxt_move,
                                   EmbedInSlots([(i le nb_target_filled * chunk_size) or
                                                 (i gt (nb_target_filled + nb_input_filled) * chunk_size) select 0 else 1 :
                                                  i in [1..n]]: henselExponent := 1)));

        // Possibly also add to second target ciphertext if it doesn't fit in the first one
        if nb_target_filled + nb_input_filled gt len_str then
            res[nb_ctxt_filled + 2] := Add(res[nb_ctxt_filled + 2], MulConstant(ctxt_move,
                                       EmbedInSlots([(i gt (nb_target_filled + nb_input_filled - len_str) * chunk_size) select 0
                                                      else 1 : i in [1..n]]: henselExponent := 1)));
        end if;

        // Increase total number of filled characters
        nb_total_filled +:= nb_input_filled;
    end for;
    return res;
end function;

// Compute equality function
function PrecompDeltas(ctxt_a, ctxt_b, len_str, alphabet_size, expand_keys, rk)
    Zpy<y> := PolynomialRing(Integers(p));
    poly := &*[y - i : i in {-alphabet_size + 1..alphabet_size - 1} diff {0}];
    poly *:= (Evaluate(poly, 0) ^ (-1)); poly := Zx!poly;

    ctxt_a_expand := ExpandCharacters(ctxt_a, len_str, expand_keys);
    ctxt_b_expand := ExpandCharacters(ctxt_b, len_str, expand_keys: reverse := true);
    return [PolyEval(poly, Sub(ctxt_a_expand[i], ctxt_b_expand[i]),
                     addFunc, func<x, y | mulFunc(x, y, rk)>: optimal_depth := true) : i in [1..#ctxt_a_expand]];
end function;

// Extract input for minimum function
function ExtractMinusDelta(ctxt_list, k, len_str, extract_keys)
    chunk_size := ChunkSize(len_str);
    nb_total_filled := TotalFilled(len_str, k);
    nb_target_filled := TargetFilled(len_str, nb_total_filled);
    nb_ctxt_filled := CiphertextsFilled(len_str, nb_total_filled);
    nb_input_filled := InputFilled(len_str, k);

    // Extract from first target ciphertext
    res := MulConstant(ctxt_list[nb_ctxt_filled + 1], EmbedInSlots([(i le nb_target_filled * chunk_size) or
                                                                    (i gt (nb_target_filled + nb_input_filled) * chunk_size)
                                                                     select 0 else -1 : i in [1..n]]: henselExponent := 1));

    // Possibly also extract from second target ciphertext
    if nb_target_filled + nb_input_filled gt len_str then
        res := Add(res, MulConstant(ctxt_list[nb_ctxt_filled + 2],
                                    EmbedInSlots([(i gt (nb_target_filled + nb_input_filled - len_str) * chunk_size) select 0
                                                   else -1 : i in [1..n]]: henselExponent := 1)));
    end if;

    // Move elements to the right place
    return ApplyAutomorphismCiphertext(res, GetHypercubeRepresentative(((nb_target_filled * chunk_size) mod n) + 1),
                                       extract_keys[k - 1]);
end function;

// Evaluate polynomial g
function EvaluateMinimum(x, y, z, rk: folding_constant := 1)
    hy := Mul(SubConstantCiphertext(y, 1), y, rk);
    hz := Mul(SubConstantCiphertext(z, 1), z, rk);
    return Add(MulConstant(x, folding_constant), Mul(MulConstant(AddConstant(x, 1), Modinv(4, p) * folding_constant),
                                                     Add(Add(MulConstant(hy, 2), MulConstant(hz, 2)), Mul(hy, hz, rk)), rk));
end function;

// Bootstrap two sparse ciphertexts simultaneously
function CombinedGBFVBetterRecrypt(ctxt1, ctxt2, recrypt_variables, boot_shift_key)
    ctxt := Add(ctxt1, ApplyAutomorphismCiphertext(ctxt2, GetHypercubeRepresentative(n div 2 + 1), boot_shift_key));
    ctxt := GBFVBetterRecrypt(ctxt, recrypt_variables);
    return ctxt, ApplyAutomorphismCiphertext(ctxt, GetHypercubeRepresentative(n div 2 + 1), boot_shift_key);
end function;

// Edit distance computation using GBFV
function EditDistance(ctxt_a, ctxt_b, len_str, alphabet_size, recrypt_variables, expand_keys, extract_keys, key_right, key_left,
                      boot_shift_key, rk: iterations_per_bootstrap := 1)
    assert alphabet_size le 36;

    // Initialize variables
    chunk_size := ChunkSize(len_str);
    ctxt_h := GetZeroCiphertext(ctxt_a); ctxt_v := GetZeroCiphertext(ctxt_a); ctxt_acc := GetZeroCiphertext(ctxt_a);
    ctxt_h := AddConstant(ctxt_h, EmbedInSlots([i le chunk_size select 1 else 0 : i in [1..n]]: henselExponent := 1));
    ctxt_v := AddConstant(ctxt_v, EmbedInSlots([i le chunk_size select 1 else 0 : i in [1..n]]: henselExponent := 1));
    ctxt_acc := AddConstant(ctxt_acc, EmbedInSlots([i le chunk_size select len_str else 0 : i in [1..n]]: henselExponent := 1));
    deltas := PrecompDeltas(ctxt_a, ctxt_b, len_str, alphabet_size, expand_keys, rk);

    // Compute mask
    mask := EmbedInSlots([i le (n div 2) select 1 else 0 : i in [1..n]]: henselExponent := 1);
    for k := 2 to len_str do
        // Extract delta and compute minimum
        ctxt_minus_delta := ExtractMinusDelta(deltas, k, len_str, extract_keys);
        if (iterations_per_bootstrap gt 1) and (k - 1 le len_str div 2) then
            ctxt_min := EvaluateMinimum(ctxt_minus_delta, ctxt_h, ctxt_v, rk: folding_constant := mask);
        else
            ctxt_min := EvaluateMinimum(ctxt_minus_delta, ctxt_h, ctxt_v, rk);
        end if;

        // Bootstrap here if iterations_per_bootstrap is 1
        if iterations_per_bootstrap eq 1 then
            ctxt_min := GBFVBetterRecrypt(ctxt_min, recrypt_variables);
        end if;

        // Mask both ciphertexts
        if (iterations_per_bootstrap gt 1) and (k - 1 le len_str div 2) then
            ctxt_h := MulConstant(ctxt_h, mask);
            ctxt_v := MulConstant(ctxt_v, mask);
        end if;

        // Update anti-diagonal state
        ctxt_t := Sub(ctxt_min, ctxt_v);
        ctxt_v := Sub(ctxt_min, ctxt_h);

        // Bootstrap here if iterations_per_bootstrap is greater than 1
        if k mod iterations_per_bootstrap eq 1 then
            if k le len_str div 2 then
                ctxt_t, ctxt_v := CombinedGBFVBetterRecrypt(ctxt_t, ctxt_v, recrypt_variables, boot_shift_key);
            else
                ctxt_t := GBFVBetterRecrypt(ctxt_t, recrypt_variables);
                ctxt_v := GBFVBetterRecrypt(ctxt_v, recrypt_variables);
            end if;
        end if;

        // Continue updating anti-diagonal state
        ctxt_t := AddConstant(ctxt_t, EmbedInSlots([i le (k - 1) * chunk_size select 1 else 0 :
                                                    i in [1..n]]: henselExponent := 1));
        ctxt_v := AddConstant(ctxt_v, EmbedInSlots([i le k * chunk_size select 1 else 0 :
                                                    i in [1..n]]: henselExponent := 1));
        ctxt_h := AddConstant(ApplyAutomorphismCiphertext(ctxt_t, GetInverseHypercubeRepresentative(chunk_size + 1), key_right),
                              EmbedInSlots([i le chunk_size select 1 else 0 : i in [1..n]]: henselExponent := 1));
    end for;
    for k := len_str + 1 to 2 * len_str do
        // Extract delta and compute minimum
        ctxt_minus_delta := ExtractMinusDelta(deltas, k, len_str, extract_keys);
        if (iterations_per_bootstrap gt 1) and (2 * len_str - k + 1 le len_str div 2) then
            ctxt_min := EvaluateMinimum(ctxt_minus_delta, ctxt_h, ctxt_v, rk: folding_constant := mask);
        else
            ctxt_min := EvaluateMinimum(ctxt_minus_delta, ctxt_h, ctxt_v, rk);
        end if;

        // Bootstrap here if iterations_per_bootstrap is 1
        if (iterations_per_bootstrap eq 1) and (k ne 2 * len_str) then
            ctxt_min := GBFVBetterRecrypt(ctxt_min, recrypt_variables);
        end if;

        // Mask both ciphertexts
        if (iterations_per_bootstrap gt 1) and (2 * len_str - k + 1 le len_str div 2) then
            ctxt_h := MulConstant(ctxt_h, mask);
            ctxt_v := MulConstant(ctxt_v, mask);
        end if;

        // Update anti-diagonal state
        ctxt_t := Sub(ctxt_min, ctxt_h);
        ctxt_h := Sub(ctxt_min, ctxt_v);

        // Bootstrap here if iterations_per_bootstrap is greater than 1
        if (k mod iterations_per_bootstrap eq 1) and (k ne 2 * len_str) then
            if 2 * len_str - k + 1 le len_str div 2 then
                ctxt_t, ctxt_h := CombinedGBFVBetterRecrypt(ctxt_t, ctxt_h, recrypt_variables, boot_shift_key);
            else
                ctxt_t := GBFVBetterRecrypt(ctxt_t, recrypt_variables);
                ctxt_h := GBFVBetterRecrypt(ctxt_h, recrypt_variables);
            end if;
        end if;

        // Continue updating anti-diagonal state
        ctxt_t := AddConstant(ctxt_t, EmbedInSlots([i le (2 * len_str - k + 1) * chunk_size select 1 else 0 :
                                                    i in [1..n]]: henselExponent := 1));
        ctxt_h := AddConstant(ctxt_h, EmbedInSlots([i le (2 * len_str - k) * chunk_size select 1 else 0 :
                                                    i in [1..n]]: henselExponent := 1));
        ctxt_v := ApplyAutomorphismCiphertext(ctxt_t, GetHypercubeRepresentative(chunk_size + 1), key_left);
        ctxt_acc := Add(ctxt_acc, ctxt_t);
    end for;
    return MulConstant(ctxt_acc, EmbedInSlots([i le chunk_size select 1 else 0 : i in [1..n]]: henselExponent := 1));
end function;