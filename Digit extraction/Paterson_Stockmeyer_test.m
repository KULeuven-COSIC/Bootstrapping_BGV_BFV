load "Crypto/BFV/BFV.m";
load "Digit extraction/Digit_extraction.m";

Zx<x> := PolynomialRing(Integers());
res := true;
for i := 1 to 10000 do
    d := Random(50) + 1;
    poly := (x ^ d) + Zx![Random(10) - 5 : i in [1..d]];
    element := Random(10) - 5;
    if PatersonStockmeyer(poly, element, func<x, y | x + y>, func<x, y | x * y>) ne Evaluate(poly, element) then
        res := false;
        break;
    end if;
end for;
"Test Paterson-Stockmeyer on integer polynomial", res;

sk, pk := GenKeyPair();
rk := GenRelinKey(sk);
m := RandPol(t);
c := Encrypt(m, t, pk);
degree := 50;
poly := (x ^ degree) + Zx![Random(t) : i in [1..degree]];
evl := PatersonStockmeyer(poly, c, addFunc, func<x, y | mulFunc(x, y, rk)>);
//evl := PatersonStockmeyer(poly, c, addFunc, func<x, y | mulLazyFunc(x, y, rk)>:
//                          lazy := true, sanitizeFunc := func<x | relinFunc(x, rk)>);

Zft := quo<Zt_poly | f>;
Zft_poly := PolynomialRing(Zft);
result := Zx!Evaluate(Zft_poly!Zt_poly!poly, Zft!Zt_poly!m);
"Test Paterson-Stockmeyer on ciphertext", result eq Decrypt(evl, sk);