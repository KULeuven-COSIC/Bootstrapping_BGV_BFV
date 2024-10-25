load "Bootstrapping/GBFV_recrypt.m";

assert (r eq 1) and (e eq 2);
sk, pk := GenKeyPair();
rk := GenRelinKey(sk);



// Switch to lowest modulus before bootstrapping
// --> Not possible to go to extremely low modulus, because of linear maps
nb_packed := n div gbfvExponent; msq_list := [RandPol(p) : i in [1..nb_packed]];
msq_list_adapted := [ScaleAndRound(msq_list[i], p, x ^ gbfvExponent - gbfvCoefficient) mod p : i in [1..nb_packed]];
csq_list := [Encrypt(msq, p, pk) : msq in msq_list_adapted];
if enableModSwitch then
    for index := 1 to nb_packed do
        csq_list[index] := ModSwitch(csq_list[index], 2 ^ 100);
    end for;
end if;



// Compute square so that initial capacity drops a little bit
msq_list_adapted := [((msq ^ 2) mod f) mod p : msq in msq_list_adapted];
csq_list := [Mul(csq, csq, rk) : csq in csq_list];



// Bootstrapping variables
recrypt_variables := GenerateGBFVBatchRecryptVariables(sk, pk, B);

// Test recryption
t := Cputime();
res := GBFVBatchRecrypt(csq_list, recrypt_variables);

"";
"Time for GBFV batch bootstrapping", Cputime(t);

correctness := true;
for index := 1 to nb_packed do
    correctness and:= (Decrypt(res[index], sk: print_result := false, check_correctness := true,
                                               expected_result := msq_list_adapted[index]) eq msq_list_adapted[index]);
end for;

"Test GBFV batch bootstrapping", correctness;
"Total noise in bootstrapped ciphertext", ErrorC(res[1], sk);

"Error after bootstrapping on canonical embedding", ErrorCanC(res[1], sk);
"Estimated error after bootstrapping on canonical embedding", EstimatedErrorCanC(res[1]);

load "Traces/Post_processing.m";