// Load your favorite scheme
load "Crypto/BFV/BFV.m";
//load "Crypto/BGV/BGV.m";

// Load recryption functionality
load "Bootstrapping/Thin_recrypt.m";

assert usePowerOfTwo or AreBootstrappable(p, m, factors_m);

sk, pk := GenKeyPair();



// Switch to lowest modulus before bootstrapping
// --> Not possible to go to extremely low modulus, because of linear maps
henselExponentPlaintext := 1;
henselExponentCiphertext := 8;
msq := EmbedInSlots([Random(p ^ henselExponentPlaintext - 1) : i in [1..l]]: henselExponent := henselExponentPlaintext);
if scheme eq "BFV" then
    csq := ModSwitch(Encrypt(msq, p ^ henselExponentPlaintext, pk), 2 ^ 100);                                         // BFV
else
    csq := ModSwitch(Encrypt(msq, p ^ henselExponentPlaintext, pk), baseModulus ^ Round(Log(baseModulus, 2 ^ 100)));  // BGV
end if;



// Bootstrapping variables
recrypt_variables := GenerateThinRecryptVariables(sk, pk, henselExponentPlaintext, henselExponentCiphertext);

// Test recryption
t := Cputime();
res := ThinRecrypt(csq, recrypt_variables);

"";
"Time for thin bootstrapping", Cputime(t);
"Test thin bootstrapping", Decrypt(res, sk) eq msq;
"Total noise in bootstrapped ciphertext", ErrorC(res, sk);

"Error after bootstrapping on canonical embedding", ErrorCanC(res, sk);
"Estimated error after bootstrapping on canonical embedding", EstimatedErrorCanC(res);