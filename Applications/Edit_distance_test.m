load "Applications/Edit_distance.m";

// Basic checks
assert scheme eq "BFV";
assert GetLTVersion() eq 4;
assert (r eq 1) and (e eq 2);
assert IsPowerOfTwo(n_prime) and IsPowerOfTwo(n_double_prime);
assert (n_prime le n) and (n_double_prime lt n_prime);
assert &*gbfv_mat_dimensions eq Minimum(n_prime, n_double_prime ^ 2);
assert (#gbfv_mat_dimensions eq 0) or (Minimum(gbfv_mat_dimensions) gt 1);

// Check if the used moduli are in the cyclotomic ring
assert &and[ToCyclotomicField(allModuli[index + 1]) * InvertOverField(allModuli[index]) in MaximalOrder(cyclo_field) :
            index in [1..#allModuli - 1]];

// Check if decomposition parameters are consistent with intermediate moduli
assert #intModuli lt Maximum(#gbfv_mat_dimensions, 1);
assert gbfvExponent * n_prime eq n_double_prime * n;
assert (#gbfv_mat_dimensions eq 0) or
       (&and[intExponents[index] * &*gbfv_mat_dimensions[#gbfv_mat_dimensions - #intExponents + index..#gbfv_mat_dimensions] *
             Maximum(n_prime div (n_double_prime ^ 2), 1) ge n : index in [1..#intExponents]]);

// Only full packing case is implemented
assert n eq n_prime;



// Strings to compare
alphabet_size_encrypt := 36;
alphabet_size_evaluate := 128;
str_a := ["FHE"];
str_b := ["HFE"];

// Key generation
len_str := CeilPowerOfTwo(Maximum([#str : str in str_a]));
sk, pk := GenKeyPair(); rk := GenRelinKey(sk);
recrypt_variables := GenerateGBFVBetterRecryptVariables(sk, pk, B);
expand_keys, extract_keys, key_right, key_left, boot_shift_key := PrecompKeys(sk, len_str);



// Encryption, edit distance computation and decryption
ctxt_a, ctxt_b := EncryptStrings(str_a, str_b, alphabet_size_encrypt, pk);
timer := StartTiming();
ctxt_edit := EditDistance(ctxt_a, ctxt_b, len_str, alphabet_size_evaluate, recrypt_variables, expand_keys, extract_keys, key_right,
                          key_left, boot_shift_key, rk: iterations_per_bootstrap := 2);
StopTiming(timer: message := "edit distance");
DecryptEditDistances(ctxt_edit, sk, #str_a);



// Check correctness
expected_result := ScaleAndRound(Decrypt(ctxt_edit, sk), p, gbfvModulus) mod p;
Decrypt(SetPlaintextModulus(ctxt_edit, p), sk: print_result := false, check_correctness := true,
                                               expected_result := expected_result) eq expected_result;

load "Traces/Post_processing.m";