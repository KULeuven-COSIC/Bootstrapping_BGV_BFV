load "Crypto/BFV/BFV.m";
load "Linear maps/GeneralCyclotomic/Linear_maps.m";

// Simulate functionality on plaintext
function SimulateMatMulSlots(m, constants)
    res := [0 : i in [1..l]];

    for constant in constants do
        m_parts := GetPlaintextParts(m);
        constant_parts := GetPlaintextParts(constant);
        res := [((res[i] + constant_parts[i] * m_parts[i]) mod GetFirstSlotFactor()) mod t : i in [1..l]];

        m := ApplyFrobeniusPowerPlaintext(m, 1);
    end for;
    return res;
end function;



// Test functionality on ciphertext
sk, pk := GenKeyPair();

// Generate switch keys
frobeniusSwitchKeys := [];
for exp := 1 to d - 1 do
    Append(~frobeniusSwitchKeys, GenSwitchKey(sk, Modexp(p, exp, m)));
end for;

m := RandPol(t);
c := Encrypt(m, t, pk);

// Test linear transformation
constants := [RandPol(t) : i in [1..d]];
adapted_constants := MatMulSlotsAdaptedConstants(constants, e);

// Apply linear transformation
res := GetPlaintextParts(Decrypt(MatMulSlotsBabyGiant(c, adapted_constants, frobeniusSwitchKeys), sk));
// res := GetPlaintextParts(Decrypt(MatMulSlots(c, constants, frobeniusSwitchKeys), sk));
// --> Naive algorithm: don't use

"Test linear transformation", res eq SimulateMatMulSlots(m, constants);



// Test unpacking of slots
unpack := UnpackSlots(c, constants, frobeniusSwitchKeys);
"Test unpack slots", GetPlaintextParts(Decrypt(unpack[1], sk)) eq res;



// Test slot-wise trace map
m := RandPol(t);
c := Encrypt(m, t, pk);
res := true;
for element in GetPlaintextParts(Decrypt(SlotwiseTrace(c, frobeniusSwitchKeys), sk)) do
    if Degree(element) gt 0 then
        res := false;
        break;
    end if;
end for;
"Test slot-wise trace map", res;