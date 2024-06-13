load "Crypto/BFV/BFV.m";

sk, pk := GenKeyPair();

m1 := RandPol(t);
c1 := Encrypt(m1, t, pk);
mm1 := Decrypt(c1, sk);
mmm1 := DecryptPowerful(c1, sk);
"Test decrypt m1", (mm1 eq m1 and mmm1 eq m1);

m2 := RandPol(t);
c2 := Encrypt(m2, t, pk);
mm2 := Decrypt(c2, sk);
"Test decrypt m2", mm2 eq m2;

cs1 := Encrypt(m1, t, pk);
cs1 := ModSwitch(cs1, 2^200);
ms1 := Decrypt(cs1, sk);
"Test mod switch ms1", ms1 eq m1;

cs2 := Encrypt(m2, t, pk);
cs2 := ModSwitch(cs2, 3^50);
ms2 := Decrypt(cs2, sk);
"Test mod switch ms2", ms2 eq m2;

cs3 := ModSwitch(cs1, 2^300);
ms3 := Decrypt(cs3, sk);
"Test mod switch up ms3", ms3 eq m1;

cs4 := ModSwitch(cs2, 2^300);
ms4 := Decrypt(cs4, sk);
"Test mod switch up ms4", ms4 eq m2;

ca := Add(c1, c2);
ma := Decrypt(ca, sk);
"Test hom add", ma eq ((m1 + m2) mod t);

cs := Sub(c1, c2);
ms := Decrypt(cs, sk);
"Test hom sub", ms eq ((m1 - m2) mod t);

cm := MulNR(c1, c2);
mm := Decrypt(cm, sk);
"Test hom mul no relin", mm eq (((m1*m2) mod f) mod t);

cms := Add(cm, c1);
mms := Decrypt(cms, sk);
"Test hom mul add no relin", mms eq (((m1*m2+m1) mod f) mod t);

rk := GenRelinKey(sk);
cmr := Relin(cm, rk);
mmr := Decrypt(cmr, sk);
"Test hom mul with relin", mmr eq (((m1*m2) mod f) mod t);

csm1 := Encrypt(m1, t, pk);
csm2 := Encrypt(m2, t, pk);
csm2 := ModSwitch(csm2, Round(Sqrt(q)));
csm := MulNR(csm1, csm2);
msm := Decrypt(csm, sk);
"Test hom mul no relin different mod", msm eq (((m1*m2) mod f) mod t);

csmr := Relin(csm, rk);
msmr := Decrypt(csmr, sk);
"Test hom mul with relin different mod", msmr eq (((m1*m2) mod f) mod t);

cc := AddConstant(GetZeroCiphertext(t), m1);
ccm := MulNR(cc, c2);
cmm := Decrypt(ccm, sk);
"Test hom mul with const", cmm eq (((m1*m2) mod f) mod t);

"Error in fresh encryption", ErrorC(c1, sk);
"Error after addition", ErrorC(ca, sk);
"Error after subtraction", ErrorC(cs, sk);
"Error after mul no relin", ErrorC(cm, sk);
"Error after mul with relin", ErrorC(cmr, sk);

// Computing max level of multiplications
"Computing tree of consecutive levels .....";

halfMax := 13;
csq := c1;
tim := 0;
for i := 1 to 2 * halfMax do
    u := Cputime();
    csq := Mul(csq, csq, rk);
    tim +:= Cputime(u);
    "Error after mul level " cat IntegerToString(i), ErrorC(csq, sk);
end for;
mpow := Decrypt(csq, sk);
error1 := ErrorC(csq, sk);
"Total time for " cat IntegerToString(2 * halfMax) cat " multiplications", tim;

// Test dynamic scaling
"";
csq := c1;
t1 := 0;
for i := 1 to halfMax do
    u := Cputime();
    csq := MulNR(csq, csq);
    csq := Relin(csq, rk);
    t1 +:= Cputime(u);
end for;
u := Cputime();
csq := ModSwitch(csq, 2^200);
tScale := Cputime(u);
t2 := 0;
for i := halfMax + 1 to 2 * halfMax do
    u := Cputime();
    csq := MulNR(csq, csq);
    csq := Relin(csq, rk);
    t2 +:= Cputime(u);
end for;
error2 := ErrorC(csq, sk);
"Error without dynamic rescaling is", error1;
"Error with dynamic rescaling is", error2;
"Time for " cat IntegerToString(halfMax) cat " multiplications with mod 2^300 is", t1;
"Time for " cat IntegerToString(halfMax) cat " multiplications with mod 2^200 is", t2;
"Time for dynamic rescaling is", tScale;

// Test plaintext slots
parts := [Zx | [Random(t-1) : i in [1..d]] : j in [1..l]];
plaintext := EmbedInSlots(parts);
"";
"Test plaintext embedding 1", GetPlaintextParts(plaintext) eq parts;

parts := [i eq 2 select 1 else 0 : i in [1..l]]; 
plaintext := EmbedInSlots(parts);
"Test plaintext embedding 2", ((plaintext mod factors[1]) eq 0) and ((plaintext mod factors[2]) eq 1);

parts1 := [Zx | [Random(t-1) : i in [1..d]] : j in [1..l]];
parts2 := [Zx | [Random(t-1) : i in [1..d]] : j in [1..l]];
plaintext1 := EmbedInSlots(parts1);
plaintext2 := EmbedInSlots(parts2);

sum := [Zx | ((parts1[i] + parts2[i]) mod (factors[1])) : i in [1..l]];
mul := [Zx | ((parts1[i] * parts2[i]) mod (factors[1])) : i in [1..l]];

"Test plaintext embedding sum", GetPlaintextParts((plaintext1 + plaintext2) mod t) eq sum;
"Test plaintext embedding mul", GetPlaintextParts(((plaintext1 * plaintext2) mod f) mod t) eq mul;

// Test automorphisms and key switching
index := [IsGoodDimension(i) select 1 else 0 : i in [1..GetNbDimensions()]];
switchKey := GenSwitchKey(sk, index);
cNew := ApplyAutomorphismCiphertext(c1, index, switchKey);
plaintext := Decrypt(cNew, sk);

parts1 := GetPlaintextParts(m1);
parts2 := GetPlaintextParts(plaintext);
res := true;
for element in parts1 do
    if Index(parts2, element) eq 0 then
        res := false;
    end if;
end for;
"Test automorphisms and key switching", res;

// Test rotations in good and bad dimensions
for iteration := 1 to GetNbDimensions() do
    if IsGoodDimension(iteration) then
        // Good dimension
        index := Get1DHyperIndex(iteration, 1);
        switchKey := GenSwitchKey(sk, index);

        cNew := RotateSlotsGoodDimension(c1, iteration, 1, switchKey);
        plaintext := Decrypt(cNew, sk);

        parts1 := GetPlaintextParts(m1);
        parts2 := GetPlaintextParts(plaintext);
        res := true;
        for index := 1 to l do
            hyperIndex := IndexToHypercube(index);
            hyperIndex[iteration] := (hyperIndex[iteration] + 1) mod GetDimensionSize(iteration);
            increasedIndex := HypercubeToIndex(hyperIndex);

            if parts1[index] ne parts2[increasedIndex] then
                res := false;
            end if;
        end for;
        "Test rotations good dimension", res;
    else
        // Bad dimension
        indexAhead := Get1DHyperIndex(iteration, 1);
        indexBack := Get1DHyperIndex(iteration, 1 - GetDimensionSize(iteration));

        switchKeyAhead := GenSwitchKey(sk, indexAhead);
        switchKeyBack := GenSwitchKey(sk, indexBack);

        cNew := RotateSlotsBadDimension(c1, iteration, 1, switchKeyAhead, switchKeyBack);
        plaintext := Decrypt(cNew, sk);

        parts1 := GetPlaintextParts(m1);
        parts2 := GetPlaintextParts(plaintext);
        res := true;
        for index := 1 to l do
            hyperIndex := IndexToHypercube(index);
            hyperIndex[iteration] := (hyperIndex[iteration] + 1) mod GetDimensionSize(iteration);
            increasedIndex := HypercubeToIndex(hyperIndex);

            if parts1[index] ne parts2[increasedIndex] then
                res := false;
            end if;
        end for;
        "Test rotations bad dimension", res;
    end if;
end for;

// Test Frobenius maps
for exp := 1 to Minimum(3, d - 1) do
    parts := GetPlaintextParts(m1);
    parts_updated := [(ApplyFrobeniusPowerPlaintext(part, exp) mod GetFirstSlotFactor()) mod t : part in parts];

    switchKey := GenSwitchKey(sk, Modexp(p, exp, m));
    "Test Frobenius maps", exp, GetPlaintextParts(Decrypt(ApplyFrobeniusPowerCiphertext(c1, exp, switchKey), sk)) eq
                                parts_updated;
end for;