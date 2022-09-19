// Load your favorite scheme
load "Crypto/BFV/BFV.m";
//load "Crypto/BGV/BGV.m";

// Load recryption functionality
load "Bootstrapping/Recrypt.m";

assert not usePowerOfTwo and AreBootstrappable(p, m, factors_m);

sk, pk := GenKeyPair();



// Test which modulus is the lowest possible to switch to
henselExponentPlaintext := 1;
henselExponentCiphertext := 8;



// Message to recrypt
msq := RandPol(p ^ henselExponentPlaintext);
if scheme eq "BFV" then
    csq := ModSwitch(Encrypt(msq, p ^ henselExponentPlaintext, pk), 2 ^ 100);                                         // BFV
else
    csq := ModSwitch(Encrypt(msq, p ^ henselExponentPlaintext, pk), baseModulus ^ Round(Log(baseModulus, 2 ^ 100)));  // BGV
end if;

// Bootstrapping info
recrypt_variables := GenerateRecryptVariables(sk, pk, henselExponentPlaintext, henselExponentCiphertext);

// Test recryption
t := Cputime();
res := Recrypt(csq, recrypt_variables);

"";
"Time for bootstrapping", Cputime(t);
"Test bootstrapping", Decrypt(res, sk) eq msq;
"Total noise in bootstrapped ciphertext", ErrorC(res, sk);

"Error after bootstrapping on canonical embedding", ErrorCanC(res, sk);
"Estimated error after bootstrapping on canonical embedding", EstimatedErrorCanC(res);