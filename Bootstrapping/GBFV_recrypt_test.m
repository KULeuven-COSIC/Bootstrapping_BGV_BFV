load "Bootstrapping/GBFV_recrypt.m";

assert (r eq 1) and (e eq 2);
sk, pk := GenKeyPair();



// Switch to lowest modulus before bootstrapping
// --> Not possible to go to extremely low modulus, because of linear maps
msq := RandPol(p);
csq := Encrypt(msq, x ^ gbfvExponent - gbfvCoefficient, pk);
if enableModSwitch then
    csq := ModSwitch(csq, 2 ^ 100);
end if;



// Bootstrapping variables
//recrypt_variables := GenerateThinRecryptVariables(sk, pk, r, e, B);
recrypt_variables := GenerateGBFVRecryptVariables(sk, pk, B);

// Test recryption
t := Cputime();
//res := GBFVRecryptBlackBox(csq, recrypt_variables);
res := GBFVRecrypt(csq, recrypt_variables);

"";
"Time for GBFV bootstrapping", Cputime(t);
"Test GBFV bootstrapping", Decrypt(res, sk) eq Flatten(msq, x ^ gbfvExponent - gbfvCoefficient);
"Total noise in bootstrapped ciphertext", ErrorC(res, sk);

"Error after bootstrapping on canonical embedding", ErrorCanC(res, sk);
"Estimated error after bootstrapping on canonical embedding", EstimatedErrorCanC(res);