load "Crypto/BFV/BFV.m";
load "Bootstrapping/Thin_recrypt.m";

sk, pk := GenKeyPair();
bootKey := GenBootKeyRecrypt(sk, pk, e);

// Generate switch keys
frobeniusSwitchKeys := [];
for exp := 1 to d - 1 do
    Append(~frobeniusSwitchKeys, GenSwitchKey(sk, Modexp(p, exp, m)));
end for;

c := Encrypt(RandPol(p ^ r), p ^ r, pk);

unpackConstants := UnpackConstants(r);
repackConstants := RepackConstants(r);

PrintNoiseBudget(c: message := "initial");

timer := StartTiming();
unpacked_result := UnpackSlots(c, unpackConstants, frobeniusSwitchKeys);
StopTiming(timer: message := "unpacking");

PrintNoiseBudget(unpacked_result[1]: message := "after unpacking");

timer := StartTiming();
res := RepackSlots(unpacked_result, repackConstants);
StopTiming(timer: message := "repacking");

PrintNoiseBudget(res: message := "after repacking");

load "Traces/Post_processing.m";