load "Bootstrapping/GBFV_recrypt.m";

assert (r eq 1) and (e eq 2);
sk, pk := GenKeyPair();



// Switch to lowest modulus before bootstrapping
// --> Not possible to go to extremely low modulus, because of linear maps
nb_packed := n div gbfvExponent; msq_list := [RandPol(p) : i in [1..nb_packed]];
csq_list := [Encrypt(msq, x ^ gbfvExponent - gbfvCoefficient, pk) : msq in msq_list];
if enableModSwitch then
    for index := 1 to nb_packed do
        csq_list[index] := ModSwitch(csq_list[index], 2 ^ 100);
    end for;
end if;



// Bootstrapping variables
recrypt_variables := GenerateGBFVBatchRecryptVariables(sk, pk, B);

// Test recryption
t := Cputime();
res := GBFVBatchRecrypt(csq_list, recrypt_variables);

"";
"Time for GBFV batch bootstrapping", Cputime(t);

correctness := true;
for index := 1 to nb_packed do
    correctness and:= (Decrypt(res[index], sk) eq Flatten(msq_list[index], x ^ gbfvExponent - gbfvCoefficient));
end for;

"Test GBFV batch bootstrapping", correctness;
"Total noise in bootstrapped ciphertext", ErrorC(res[1], sk);

"Error after bootstrapping on canonical embedding", ErrorCanC(res[1], sk);
"Estimated error after bootstrapping on canonical embedding", EstimatedErrorCanC(res[1]);