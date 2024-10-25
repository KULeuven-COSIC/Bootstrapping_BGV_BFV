// Load your favorite scheme
load "Crypto/BFV/BFV.m";
//load "Crypto/BGV/BGV.m";

// Load thin recryption functionality
load "Bootstrapping/Thin_recrypt.m";

sk, pk := GenKeyPair();
rk := GenRelinKey(sk);



// Switch to lowest modulus before bootstrapping
// --> Not possible to go to extremely low modulus, because of linear maps
msq := EmbedInSlots([Random(p ^ r - 1) : i in [1..l]]: henselExponent := r);
csq := Encrypt(msq, p ^ r, pk);
if scheme eq "BFV" then
    if enableModSwitch then
        csq := ModSwitch(csq, 2 ^ 100);                                     // BFV
    end if;
else
    csq := ModSwitch(csq, baseModulus ^ Round(Log(baseModulus, 2 ^ 100)));  // BGV
end if;



// Compute square so that initial capacity drops a little bit
msq := ((msq ^ 2) mod f) mod p;
csq := Mul(csq, csq, rk);



// Bootstrapping variables
recrypt_variables := GenerateThinRecryptVariables(sk, pk, r, e, B);

// Test recryption
t := Cputime();
res := ThinRecrypt(csq, recrypt_variables);

"";
"Time for thin bootstrapping", Cputime(t);
"Test thin bootstrapping", Decrypt(res, sk: print_result := false, check_correctness := true, expected_result := msq) eq msq;
"Total noise in bootstrapped ciphertext", ErrorC(res, sk);

"Error after bootstrapping on canonical embedding", ErrorCanC(res, sk);
"Estimated error after bootstrapping on canonical embedding", EstimatedErrorCanC(res);

load "Traces/Post_processing.m";