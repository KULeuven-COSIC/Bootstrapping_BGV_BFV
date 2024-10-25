load "Crypto/BFV/BFV.m";

sk, pk := GenKeyPair();
rk := GenRelinKey(sk);

ctxt1 := [Encrypt(RandPol(p ^ r), p ^ r, pk) : i in [1..25]];
ctxt2 := [Encrypt(RandPol(p ^ r), p ^ r, pk) : i in [1..25]];

SetOptimalCoefficientDomain();

timer := StartTiming();
for iteration := 1 to 25 do
    res := Add(ctxt1[iteration], ctxt2[iteration]);
end for;
StopTiming(timer: message := "add low level");

timer := StartTiming();
for iteration := 1 to 25 do
    res := Mul(ctxt1[iteration], ctxt2[iteration], rk);
end for;
StopTiming(timer: message := "multiply ctxt-ctxt low level");

timer := StartTiming();
for iteration := 1 to 25 do
    exp := 2 * Random(1, m div 2) - 1;
    res := ApplyAutomorphismCiphertext(ctxt1[iteration], exp, GenSwitchKey(sk, exp));
end for;
StopTiming(timer: message := "automorphism low level");

SetOptimalNTTDomain();

// Ignore the following timing because ciphertext is not yet in NTT domain
timer := StartTiming();
for iteration := 1 to 25 do
    res := MulConstant(ctxt1[iteration], RandPol(p ^ r));
end for;
StopTiming(timer: message := "multiply ptxt-ctxt low level (ignore)");

// Ciphertext is in NTT domain now
timer := StartTiming();
for iteration := 1 to 25 do
    res := MulConstant(ctxt1[iteration], RandPol(p ^ r));
end for;
StopTiming(timer: message := "multiply ptxt-ctxt low level");

load "Traces/Post_processing.m";