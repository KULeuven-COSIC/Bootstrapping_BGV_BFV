load "Bootstrapping/GBFV_recrypt.m";

assert (r eq 1) and (e eq 2);
assert ToCyclotomicField(p) * InvertOverField(gbfvModulus) in MaximalOrder(cyclo_field);
sk, pk := GenKeyPair();
rk := GenRelinKey(sk);



// Switch to lowest modulus before bootstrapping
// --> Not possible to go to extremely low modulus, because of linear maps
msq := ScaleAndRound(RandPol(p), p, gbfvModulus);
csq := Encrypt(msq, p, pk);
if enableModSwitch then
    csq := ModSwitch(csq, 2 ^ 100);
end if;



// Compute square so that initial capacity drops a little bit
msq := ((msq ^ 2) mod f) mod p;
csq := Mul(csq, csq, rk);



// Bootstrapping variables
//recrypt_variables := GenerateThinRecryptVariables(sk, pk, r, e, B);
recrypt_variables := GenerateGBFVRecryptVariables(sk, pk, B);

// Test recryption
t := Cputime();
//res := GBFVRecryptBlackBox(csq, recrypt_variables);
res := GBFVRecrypt(csq, recrypt_variables);

"";
"Time for GBFV bootstrapping", Cputime(t);
"Test GBFV bootstrapping", Decrypt(res, sk: print_result := false, check_correctness := true, expected_result := msq) eq msq;
"Total noise in bootstrapped ciphertext", ErrorC(res, sk);

"Error after bootstrapping on canonical embedding", ErrorCanC(res, sk);
"Estimated error after bootstrapping on canonical embedding", EstimatedErrorCanC(res);

load "Traces/Post_processing.m";