load "Crypto/BFV/BFV.m";
load "Digit extraction/Digit_extraction.m";

Zx<x> := PolynomialRing(Integers());
res := true;
for i := 1 to 10000 do
    d := Random(50) + 1;
    poly := (x ^ d) + Zx![Random(10) - 5 : i in [1..d]];
    element := Random(10) - 5;
    if PolyEval(poly, element, func<x, y | x + y>, func<x, y | x * y>) ne Evaluate(poly, element) then
        res := false;
        break;
    end if;
end for;
"Test baby-step/giant-step on integer polynomial", res;

sk, pk := GenKeyPair();
rk := GenRelinKey(sk);
m := RandPol(t);
c := Encrypt(m, t, pk);
degree := 50;
poly := (x ^ degree) + Zx![Random(t) : i in [1..degree]];
evl := PolyEval(poly, c, addFunc, func<x, y | mulFunc(x, y, rk)>);
//evl := PolyEval(poly, c, addFunc, func<x, y | mulLazyFunc(x, y, rk)>:
//                lazy := true, sanitizeFunc := func<x | relinFunc(x, rk)>);

Zft := quo<Zt_poly | f>;
Zft_poly := PolynomialRing(Zft);
result := Zx!Evaluate(Zft_poly!Zt_poly!poly, Zft!Zt_poly!m);
"Test baby-step/giant-step on ciphertext", result eq Decrypt(evl, sk);



// Test depth of the procedure
degree := 127;
poly := x ^ degree + x ^ (degree - 1);
res := PolyEval(poly, [0], func<x, y | (Category(x) eq Category(0) and Category(y) eq Category(0)) select Maximum(x, y)
                                  else (Category(x) eq Category(0) and Category(y) ne Category(0)) select y else
                                       (Category(x) ne Category(0) and Category(y) eq Category(0)) select x else
                                       [Maximum(x[1], y[1])]>,
                           func<x, y | (Category(x) eq Category(0) and Category(y) eq Category(0)) select Maximum(x, y)
                                  else (Category(x) eq Category(0) and Category(y) ne Category(0)) select y else
                                       (Category(x) ne Category(0) and Category(y) eq Category(0)) select x else
                                       [Maximum(x[1], y[1]) + 1]>);
"Test non-scalar depth of baby-step/giant-step", res[1] eq Ceiling(Log(2, degree));



// Test even polynomials
res := true;
for i := 1 to 1000 do
    d := Random(25) + 1;
    poly := Evaluate((x ^ d) + Zx![Random(10) - 5 : i in [1..d]], x^2);
    element := Random(10) - 5;
    if PolyEval(poly, element, func<x, y | x + y>, func<x, y | x * y>) ne Evaluate(poly, element) then
        res := false;
        break;
    end if;
end for;
"Test baby-step/giant-step on even polynomial", res;

// Test odd polynomials
res := true;
for i := 1 to 1000 do
    d := Random(25) + 1;
    poly := Evaluate((x ^ d) + Zx![Random(10) - 5 : i in [1..d]], x^2) * x;
    element := Random(10) - 5;
    if PolyEval(poly, element, func<x, y | x + y>, func<x, y | x * y>) ne Evaluate(poly, element) then
        res := false;
        break;
    end if;
end for;
"Test baby-step/giant-step on odd polynomial", res;



// Test number of operations
// Overwrite basic arithmetic functions to count number of operations
// This is done by passing a set that keeps an ID for each non-scalar multiplication
collision_param := 2^256;

// Check whether the given variable is an augmented ciphertext
function IsAugmentedCiphertext(c)
    if Category(c) eq Category(<<[Zx | ], 0, 0, R!0>, {0}>) then
        return true;
    else
        return false;
    end if;
end function;

// Add the given ciphertexts and/or constants together
function addFunc(x, y)
    if IsAugmentedCiphertext(x) and IsAugmentedCiphertext(y) then
        return <Add(x[1], y[1]), x[2] join y[2]>;
    elif IsAugmentedCiphertext(x) then
        return <AddConstant(x[1], y), x[2]>;
    elif IsAugmentedCiphertext(y) then
        return <AddConstant(y[1], x), y[2]>;
    end if;
end function;

// Multiply the given ciphertexts and/or integer constants together
// This function cannot be used for lazy relinearization
function mulFunc(x, y, rk)
    if IsAugmentedCiphertext(x) and IsAugmentedCiphertext(y) then
        return <Mul(x[1], y[1], rk), x[2] join y[2] join {Random(collision_param)}>;
    elif IsAugmentedCiphertext(x) then
        return <MulConstant(x[1], y), x[2]>;
    elif IsAugmentedCiphertext(y) then
        return <MulConstant(y[1], x), y[2]>;
    end if;
end function;

// Multiply the given ciphertexts and/or integer constants together
// This function can be used for lazy relinearization
function mulLazyFunc(x, y, rk)
    if IsAugmentedCiphertext(x) and IsAugmentedCiphertext(y) then
        set := x[2] join y[2];
        // First relinearize both ciphertexts if necessary
        if GetNbParts(x[1]) eq 3 then
            AutomaticModSwitchRelin(~x[1]);
            x[1] := Relin(x[1], rk);
            set join:= {Random(collision_param)};
        end if;
        if GetNbParts(y[1]) eq 3 then
            AutomaticModSwitchRelin(~y[1]);
            y[1] := Relin(y[1], rk);
            set join:= {Random(collision_param)};
        end if;

        // Modulus switching is necessary to keep noise low
        AutomaticModSwitchMul(~x[1]);
        AutomaticModSwitchMul(~y[1]);
        return <MulNR(x[1], y[1]), set>;
    elif IsAugmentedCiphertext(x) then
        return <MulConstant(x[1], y), x[2]>;
    elif IsAugmentedCiphertext(y) then
        return <MulConstant(y[1], x), y[2]>;
    end if;
end function;

// Relinearize the given ciphertext if necessary
function relinFunc(x, rk)
    if GetNbParts(x[1]) eq 3 then
        AutomaticModSwitchRelin(~x[1]);
        x[1] := Relin(x[1], rk);
        DynamicModSwitch(~x[1]);
        x[2] join:= {Random(collision_param)};
    end if;
    return x;
end function;

// Perform real tests
// Note that operation counts are only correct if there are no zero coefficients
res1 := true; res2 := true; res3 := true;
for degree := 1 to 50 do
    // Usual polynomial evaluation
    poly := Zx![Random(1, t) : i in [0..degree]];
    evl := PolyEval(poly, <c, {Z | }>, addFunc, func<x, y | mulFunc(x, y, rk)>);
    result := Zx!Evaluate(Zft_poly!Zt_poly!poly, Zft!Zt_poly!m);
    _, _, nb_operations := GetBestParameters(poly);
    res1 and:= (result eq Decrypt(evl[1], sk)) and #evl[2] eq nb_operations;

    // Do the same for odd polynomials
    half_degree := degree div 2;
    poly := Evaluate(Zx![Random(1, t) : i in [0..half_degree]], x^2) * x;
    evl := PolyEval(poly, <c, {Z | }>, addFunc, func<x, y | mulFunc(x, y, rk)>);
    result := Zx!Evaluate(Zft_poly!Zt_poly!poly, Zft!Zt_poly!m);
    _, _, nb_operations := GetBestParameters(poly);
    res2 and:= (result eq Decrypt(evl[1], sk)) and #evl[2] eq nb_operations;

    // Do the same for lazy relinearization
    poly := Zx![Random(1, t) : i in [0..degree]];
    evl := PolyEval(poly, <c, {Z | }>, addFunc, func<x, y | mulLazyFunc(x, y, rk)>:
                    lazy := true, sanitizeFunc := func<x | relinFunc(x, rk)>);
    result := Zx!Evaluate(Zft_poly!Zt_poly!poly, Zft!Zt_poly!m);
    _, _, nb_operations := GetBestParameters(poly: lazy := true);
    res3 and:= (result eq Decrypt(evl[1], sk)) and #evl[2] eq nb_operations;
end for;

"Test baby-step/giant-step number of operations", res1;
"Test baby-step/giant-step number of operations odd polynomial", res2;
"Test baby-step/giant-step number of operations lazy relinearization", res3;

// Perform tests for simultaneous evaluation of multiple polynomials
res1 := true; res2 := true; res3 := true;
degree1 := 50;
for degree2 := 1 to 50 do
    // Usual polynomial evaluation
    poly1 := Zx![Random(1, t) : i in [0..degree1]];
    poly2 := Zx![Random(1, t) : i in [0..degree2]];
    evl := PolyEval([poly1, poly2], <c, {Z | }>, addFunc, func<x, y | mulFunc(x, y, rk)>);
    result1 := Zx!Evaluate(Zft_poly!Zt_poly!poly1, Zft!Zt_poly!m);
    result2 := Zx!Evaluate(Zft_poly!Zt_poly!poly2, Zft!Zt_poly!m);
    _, _, nb_operations := GetBestParameters([poly1, poly2]);
    res1 and:= (result1 eq Decrypt(evl[1][1], sk)) and (result2 eq Decrypt(evl[2][1], sk)) and
              #(evl[1][2] join evl[2][2]) eq nb_operations;

    // Do the same for odd polynomials
    half_degree1 := degree1 div 2;
    half_degree2 := degree2 div 2;
    poly1 := Evaluate(Zx![Random(1, t) : i in [0..half_degree1]], x^2) * x;
    poly2 := Evaluate(Zx![Random(1, t) : i in [0..half_degree2]], x^2) * x;
    evl := PolyEval([poly1, poly2], <c, {Z | }>, addFunc, func<x, y | mulFunc(x, y, rk)>);
    result1 := Zx!Evaluate(Zft_poly!Zt_poly!poly1, Zft!Zt_poly!m);
    result2 := Zx!Evaluate(Zft_poly!Zt_poly!poly2, Zft!Zt_poly!m);
    _, _, nb_operations := GetBestParameters([poly1, poly2]);
    res2 and:= (result1 eq Decrypt(evl[1][1], sk)) and (result2 eq Decrypt(evl[2][1], sk)) and
              #(evl[1][2] join evl[2][2]) eq nb_operations;

    // Do the same for lazy relinearization
    poly1 := Zx![Random(1, t) : i in [0..degree1]];
    poly2 := Zx![Random(1, t) : i in [0..degree2]];
    evl := PolyEval([poly1, poly2], <c, {Z | }>, addFunc, func<x, y | mulLazyFunc(x, y, rk)>:
                              lazy := true, sanitizeFunc := func<x | relinFunc(x, rk)>);
    result1 := Zx!Evaluate(Zft_poly!Zt_poly!poly1, Zft!Zt_poly!m);
    result2 := Zx!Evaluate(Zft_poly!Zt_poly!poly2, Zft!Zt_poly!m);
    _, _, nb_operations := GetBestParameters([poly1, poly2]: lazy := true);
    res3 and:= (result1 eq Decrypt(evl[1][1], sk)) and (result2 eq Decrypt(evl[2][1], sk)) and
              #(evl[1][2] join evl[2][2]) eq nb_operations;
end for;

"Test baby-step/giant-step multiple polynomials", res1;
"Test baby-step/giant-step multiple polynomials odd polynomial", res2;
"Test baby-step/giant-step multiple polynomials lazy relinearization", res3;