load "Crypto/BFV/BFV.m";
load "Bootstrapping/Thin_recrypt.m";

sk, pk := GenKeyPair();
rk := GenRelinKey(sk);
bootKey := GenBootKeyRecrypt(sk, pk, e);

c1 := Encrypt(x, p ^ r, pk);
c2 := Encrypt(x ^ 2, p ^ r, pk);
c3 := Encrypt(x ^ 3, p ^ r, pk);

timer := StartTiming();
res1 := Add(c1, Mul(c2, c3, rk));
PolynomialToString(Decrypt(res1, sk));
res2 := MulConstant(AddConstant(res1, Random(2, 8)), x ^ 8 + 4 * x ^ 3);
PolynomialToString(Decrypt(ApplyAutomorphismCiphertext(res2, 5, GenSwitchKey(sk, 5)), sk));

ctxt := AddConstant(MulConstant(MulConstant(HomomorphicInnerProduct(res2, bootKey, 0), p), p), 2);
PolynomialToString(Decrypt(ApplyAutomorphismCiphertext(AddConstant(Mul(Mul(ctxt, ctxt, rk), Mul(ctxt, ctxt, rk), rk), x),
                                                       3, GenSwitchKey(sk, 3)), sk));

evl_result := PolyEval(Zx![Z | Random(p ^ r) : i in [1..100]],
              Encrypt(Random(1, 100), p ^ r, pk), addFunc, func<x, y | mulFunc(x, y, rk)>);
PolynomialToString(Decrypt(evl_result, sk: print_result := false, check_correctness := true,
                           expected_result := Decrypt(evl_result, sk)));
StopTiming(timer);

PrintNoiseBudget(c1);
PrintNoiseBudget(res2);

load "Traces/Post_processing.m";