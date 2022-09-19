load "Crypto/BFV/BFV.m";
load "Digit extraction/Digit_extraction.m";

// Back-up of the original p
prime := p;

// Test lifting polynomial
res := true;
for i := 1 to 1000 do
    p := Random({2, 3, 5, 7, 11});
    e := Random(9) + 1;
    e_prime := Random(e - 1) + 1;
    z0 := Random(p - 1);
    z1 := Random(p - 1);
    poly := GetLiftingPolynomial(p, e);
    if (Evaluate(poly, z0 + z1 * (p ^ e_prime)) mod (p ^ (e_prime + 1))) ne z0 then
        res := false;
        break;
    end if;
end for;
"Test lifting polynomial", res;

// Test lowest digit removal polynomial
res := true;
for i := 1 to 100 do
    p := Random({2, 3, 5, 7, 11});
    e := Random(9) + 1;
    x := Random(p ^ e - 1);
    poly := GetLowestDigitRemovalPolynomial(p, e);
    if (Evaluate(poly, x) mod (p ^ e)) ne x - (x mod p) then
        res := false;
        break;
    end if;
end for;
"Test lowest digit removal polynomial", res;

// Test lowest digit retain polynomial
res := true;
for i := 1 to 100 do
    p := Random({2, 3, 5, 7, 11});
    e := Random(9) + 1;
    x := Random(p ^ e - 1);
    poly := GetLowestDigitRetainPolynomial(p, e);
    if (Evaluate(poly, x) mod (p ^ e)) ne (x mod p) then
        res := false;
        break;
    end if;
end for;
"Test lowest digit retain polynomial", res;

// Test simple digit extraction algorithm
res := true;
for i := 1 to 100 do
    p := Random({2, 3, 5, 7, 11});
    e := Random(8) + 2;
    v := Random(e - 2) + 1;
    u := Random(p ^ e - 1);
    liftingPolynomial := GetLiftingPolynomial(p, e - 1);
    if HaleviShoupDigitExtraction(u, p, e, v, func<x, y | (x + y) mod (p ^ e)>, func<x, y | (x - y) mod (p ^ e)>,
                                              func<x, y | (x * y) mod (p ^ e)>,
                                              func<x: exp := 1 | x div (p ^ exp)>, liftingPolynomial) mod (p ^ (e - v)) ne
                                 (u - (u mod (p ^ v))) div (p ^ v) then
        res := false;
        break;
    end if;
end for;
"Test simple digit extraction", res;

// Test advanced digit extraction algorithm
res := true;
for i := 1 to 100 do
    p := Random({2, 3, 5, 7, 11});
    e := Random(8) + 2;
    v := Random(e - 2) + 1;
    u := Random(p ^ e - 1);
    liftingPolynomial := GetLiftingPolynomial(p, e - 1);
    lowestDigitRetainPolynomials := [GetLowestDigitRetainPolynomial(p, iteration) : iteration in [1..e]];
    if ChenHanDigitExtraction(u, p, e, v, func<x, y | (x + y) mod (p ^ e)>, func<x, y | (x - y) mod (p ^ e)>,
                                          func<x, y | (x * y) mod (p ^ e)>,
                                          func<x: exp := 1 | x div (p ^ exp)>, liftingPolynomial, lowestDigitRetainPolynomials)
                                          mod (p ^ (e - v)) ne (u - (u mod (p ^ v))) div (p ^ v) then
        res := false;
        break;
    end if;
end for;
"Test advanced digit extraction", res;

// Test digit extraction algorithms on ciphertext
sk, pk := GenKeyPair();
rk := GenRelinKey(sk);
p := prime;
e := 6;
v := Random(e - 2) + 1;
m := Random(p ^ e - 1);
c := Encrypt(m, p ^ e, pk);

liftingPolynomial := GetLiftingPolynomial(p, e - 1);
lowestDigitRetainPolynomials := [GetLowestDigitRetainPolynomial(p, iteration) : iteration in [1..e]];
result1 := HaleviShoupDigitExtraction(c, p, e, v,
                                      addFunc, subFunc, func<x, y | mulFunc(x, y, rk)>,
                                      div_pFunc, liftingPolynomial);
result2 := ChenHanDigitExtraction(c, p, e, v,
                                  addFunc, subFunc, func<x, y | mulFunc(x, y, rk)>,
                                  div_pFunc, liftingPolynomial,
                                  lowestDigitRetainPolynomials);
res := HaleviShoupDigitExtraction(m, p, e, v, func<x, y | (x + y) mod (p ^ e)>, func<x, y | (x - y) mod (p ^ e)>,
                                              func<x, y | (x * y) mod (p ^ e)>,
                                              func<x: exp := 1 | x div (p ^ exp)>, liftingPolynomial) mod (p ^ (e - v));
"Test digit extraction on ciphertext", (Decrypt(result1, sk) eq res) and (Decrypt(result2, sk) eq res);