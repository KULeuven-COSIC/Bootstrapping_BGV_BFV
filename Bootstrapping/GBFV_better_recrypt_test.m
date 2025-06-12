load "Bootstrapping/GBFV_better_recrypt.m";

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



sk, pk := GenKeyPair();
rk := GenRelinKey(sk);

// Switch to lowest modulus before bootstrapping
// --> Not possible to go to extremely low modulus, because of linear maps
msq := (ExpandPolynomial(RandPol(p), n div n_prime) mod f) mod p;
csq := Encrypt(ScaleAndRound(msq, p, gbfvModulus), p, pk);
csq := SetPlaintextModulus(csq, gbfvModulus);
if enableModSwitch then
    csq := ModSwitch(csq, 2 ^ 100);
end if;



// Compute square so that initial capacity drops a little bit
msq := ((msq ^ 2) mod f) mod p;
csq := Mul(csq, csq, rk);



// Bootstrapping info
recrypt_variables := GenerateGBFVBetterRecryptVariables(sk, pk, B);

// Test recryption
t := Cputime();
res := GBFVBetterRecrypt(csq, recrypt_variables);
expected_result := ScaleAndRound(msq, p, gbfvModulus) mod p;

"";
"Time for GBFV bootstrapping", Cputime(t);
"Test GBFV bootstrapping", Decrypt(SetPlaintextModulus(res, p), sk: print_result := false, check_correctness := true,
                                                                    expected_result := expected_result) eq expected_result;
"Total noise in bootstrapped ciphertext", ErrorC(res, sk);

"Error after bootstrapping on canonical embedding", ErrorCanC(res, sk);
"Estimated error after bootstrapping on canonical embedding", EstimatedErrorCanC(res);

load "Traces/Post_processing.m";