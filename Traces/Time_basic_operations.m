load "Crypto/BFV/BFV.m";
load "Bootstrapping/Thin_recrypt.m";

sk, pk := GenKeyPair();
bootKey := GenBootKeyRecrypt(sk, pk, e);

ctxt := [Encrypt(RandPol(p ^ r), p ^ r, pk) : i in [1..25]];
res := Encrypt(RandPol(p ^ r), p ^ r, pk);

timer := StartTiming();
for iteration := 1 to 512 do
    res := Add(res, MulConstant(Random(ctxt), RandPol(p ^ r)));
end for;
StopTiming(timer: message := "multiply-accumulate low level");

timer := StartTiming();
for iteration := 1 to 50 do
    index := 2 * Random(1, 250) + 1;
    res := ApplyAutomorphismCiphertext(res, index, GenSwitchKey(sk, index));
end for;
StopTiming(timer: message := "automorphism low level");

ctxt := [HomomorphicInnerProduct(el, bootKey, 0) : el in ctxt];
res := HomomorphicInnerProduct(res, bootKey, 0);

timer := StartTiming();
for iteration := 1 to 512 do
    res := Add(res, MulConstant(Random(ctxt), RandPol(p ^ r)));
end for;
StopTiming(timer: message := "multiply-accumulate high level");

timer := StartTiming();
for iteration := 1 to 50 do
    index := 2 * Random(1, 250) + 1;
    res := ApplyAutomorphismCiphertext(res, index, GenSwitchKey(sk, index));
end for;
StopTiming(timer: message := "automorphism high level");

load "Traces/Post_processing.m";