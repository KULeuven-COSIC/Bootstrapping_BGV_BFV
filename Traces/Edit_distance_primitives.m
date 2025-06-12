load "Crypto/BFV/BFV.m";
load "Digit extraction/Arithmetic.m";
load "Digit extraction/Poly_eval.m";

sk, pk := GenKeyPair();
rk := GenRelinKey(sk);

ctxt_one := Encrypt(1, p, pk);    // Decrease initial noise budget
ctxt_x := Mul(Encrypt(EmbedInSlots([Random(-1, 0) : i in [1..l]]: henselExponent := 1), p, pk), ctxt_one, rk);
ctxt_y := Mul(Encrypt(EmbedInSlots([Random(-1, 1) : i in [1..l]]: henselExponent := 1), p, pk), ctxt_one, rk);
ctxt_z := Mul(Encrypt(EmbedInSlots([Random(-1, 1) : i in [1..l]]: henselExponent := 1), p, pk), ctxt_one, rk);

ctxt_x := SetPlaintextModulus(MulConstant(ctxt_x, DivideOverField(p, gbfvModulus)), gbfvModulus);
ctxt_y := SetPlaintextModulus(MulConstant(ctxt_y, DivideOverField(p, gbfvModulus)), gbfvModulus);
ctxt_z := SetPlaintextModulus(MulConstant(ctxt_z, DivideOverField(p, gbfvModulus)), gbfvModulus);

PrintNoiseBudget(SetPlaintextModulus(ctxt_x, p): message := "initial");
PrintNoiseBudget(SetPlaintextModulus(ctxt_y, p): message := "initial");
PrintNoiseBudget(SetPlaintextModulus(ctxt_z, p): message := "initial");
timer := StartTiming();

ctxt_y := Mul(AddConstant(MulConstant(ctxt_y, -1), 1), ctxt_y, rk);
ctxt_z := Mul(AddConstant(MulConstant(ctxt_z, -1), 1), ctxt_z, rk);

ctxt_eval := Add(ctxt_x, Mul(MulConstant(AddConstant(ctxt_x, 1), Modinv(4, p)),
                             Add(Add(MulConstant(ctxt_y, 2), MulConstant(ctxt_z, 2)), Mul(ctxt_y, ctxt_z, rk)), rk));

StopTiming(timer: message := "minimum");
PrintNoiseBudget(SetPlaintextModulus(ctxt_eval, p): message := "minimum");



alphabet_size := 64;
Zpy<y> := PolynomialRing(Integers(p));
poly := &*[y - i : i in {-alphabet_size + 1..alphabet_size - 1} diff {0}];
poly *:= (Evaluate(poly, 0) ^ (-1));

ctxt_1 := Mul(Encrypt(EmbedInSlots([Random(0, alphabet_size - 1) : i in [1..l]]: henselExponent := 1), p, pk), ctxt_one, rk);
ctxt_2 := Mul(Encrypt(EmbedInSlots([Random(0, alphabet_size - 1) : i in [1..l]]: henselExponent := 1), p, pk), ctxt_one, rk);

ctxt_1 := SetPlaintextModulus(MulConstant(ctxt_1, DivideOverField(p, gbfvModulus)), gbfvModulus);
ctxt_2 := SetPlaintextModulus(MulConstant(ctxt_2, DivideOverField(p, gbfvModulus)), gbfvModulus);

PrintNoiseBudget(SetPlaintextModulus(ctxt_1, p): message := "initial");
PrintNoiseBudget(SetPlaintextModulus(ctxt_2, p): message := "initial");
timer := StartTiming();

ctxt_comp := PolyEval(Zx!poly, Add(ctxt_1, MulConstant(ctxt_2, -1)), addFunc, func<x, y | mulFunc(x, y, rk)>: optimal_depth := true);

StopTiming(timer: message := "comparison");
PrintNoiseBudget(SetPlaintextModulus(ctxt_comp, p): message := "comparison");



string_length := 8;
PrintNoiseBudget(SetPlaintextModulus(ctxt_1, p): message := "initial");
timer := StartTiming();

ctxt_repeat := GetZeroCiphertext(ctxt_1);
for iteration := 1 to 2 * string_length - 1 do
    index := (m div gbfvExponent) * Random(1, gbfvExponent - 1) + 1;
    switchKey := GenSwitchKey(sk, index);
    ctxt_repeat := Add(ctxt_repeat, MulConstant(ApplyAutomorphismCiphertext(ctxt_1, index, switchKey), RandPol(p)));
end for;

StopTiming(timer: message := "repeat");
PrintNoiseBudget(SetPlaintextModulus(ctxt_repeat, p): message := "repeat");



PrintNoiseBudget(SetPlaintextModulus(ctxt_1, p): message := "initial");
timer := StartTiming();

ctxt_reverse := GetZeroCiphertext(ctxt_1);
for iteration := 1 to string_length do
    index := (m div gbfvExponent) * Random(1, gbfvExponent - 1) + 1;
    switchKey := GenSwitchKey(sk, index);
    ctxt_reverse := Add(ctxt_reverse, MulConstant(ApplyAutomorphismCiphertext(ctxt_1, index, switchKey), RandPol(p)));
end for;

StopTiming(timer: message := "reverse");
PrintNoiseBudget(SetPlaintextModulus(ctxt_reverse, p): message := "reverse");



PrintNoiseBudget(SetPlaintextModulus(ctxt_1, p): message := "initial");
timer := StartTiming();

index := (m div gbfvExponent) * Random(1, gbfvExponent - 1) + 1;
switchKey := GenSwitchKey(sk, index);
ctxt_extract := MulConstant(ApplyAutomorphismCiphertext(ctxt_1, index, switchKey), RandPol(p));

StopTiming(timer: message := "extract");
PrintNoiseBudget(SetPlaintextModulus(ctxt_extract, p): message := "extract");



nb_iterations := 25;
PrintNoiseBudget(SetPlaintextModulus(ctxt_1, p): message := "initial");
timer := StartTiming();

ctxt_add := GetZeroCiphertext(ctxt_1);
for iteration := 1 to nb_iterations do
    ctxt_add := Add(ctxt_add, ctxt_1);
end for;

StopTiming(timer: message := IntegerToString(nb_iterations) cat " adds");



PrintNoiseBudget(SetPlaintextModulus(ctxt_1, p): message := "initial");
timer := StartTiming();

for iteration := 1 to nb_iterations do
    ctxt_mul_cst := MulConstant(ctxt_1, RandPol(p));
end for;

StopTiming(timer: message := IntegerToString(nb_iterations) cat " cst muls");



PrintNoiseBudget(SetPlaintextModulus(ctxt_1, p): message := "initial");
timer := StartTiming();

for iteration := 1 to nb_iterations do
    index := (m div gbfvExponent) * Random(1, gbfvExponent - 1) + 1;
    switchKey := GenSwitchKey(sk, index);
    ctxt_auto := ApplyAutomorphismCiphertext(ctxt_1, index, switchKey);
end for;

StopTiming(timer: message := IntegerToString(nb_iterations) cat " autos");

load "Traces/Post_processing.m";