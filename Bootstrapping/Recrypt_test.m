// Load your favorite scheme
load "Crypto/BFV/BFV.m";
//load "Crypto/BGV/BGV.m";

// Load recryption functionality
load "Bootstrapping/Recrypt.m";

sk, pk := GenKeyPair();



// Message to recrypt
msq := RandPol(p ^ r);
csq := Encrypt(msq, p ^ r, pk);
if scheme eq "BFV" then
    if enableModSwitch then
        csq := ModSwitch(csq, 2 ^ 100);                                     // BFV
    end if;
else
    csq := ModSwitch(csq, baseModulus ^ Round(Log(baseModulus, 2 ^ 100)));  // BGV
end if;

// Bootstrapping info
recrypt_variables := GenerateRecryptVariables(sk, pk, r, e, B);

// Test recryption
t := Cputime();
res := Recrypt(csq, recrypt_variables);

"";
"Time for bootstrapping", Cputime(t);
"Test bootstrapping", Decrypt(res, sk) eq msq;
"Total noise in bootstrapped ciphertext", ErrorC(res, sk);

"Error after bootstrapping on canonical embedding", ErrorCanC(res, sk);
"Estimated error after bootstrapping on canonical embedding", EstimatedErrorCanC(res);