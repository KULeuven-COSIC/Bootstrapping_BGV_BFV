load "Crypto/BFV/BFV.m";
load "Linear maps/GeneralCyclotomic/Linear_maps.m";

// Compute ring structure present on the slots
Zt_F1<y> := GetSlotAlgebra(e);

sk, pk := GenKeyPair();

// Generate switch keys
frobeniusSwitchKeys := [];
for exp := 1 to d - 1 do
    Append(~frobeniusSwitchKeys, GenSwitchKey(sk, Modexp(p, exp, m)));
end for;

m := RandPol(t);
index := IndexToHypercube(Random(l - 1) + 1);
"Test slots contain right values", GetFromSlot(m, index) eq Zx!Evaluate(m, y ^ GetHypercubeRepresentative(index));

m := EmbedInSlots([Zx | i eq 1 select GetNormalElement() else 0 : i in [1..l]]);
c := Encrypt(m, t, pk);

dim := 1;
constants := EvalStage_1Constants(1, e);
adapted_constants := BlockMatMul1DGoodDimensionAdaptedConstants(constants, dim, e);
adapted_constantsAhead, adapted_constantsBack := BlockMatMul1DBadDimensionAdaptedConstants(constants, dim, e);

// Generate switch keys
rotationSwitchKeysAhead := [];
for pos := 1 to GetDimensionSize(dim) - 1 do
    Append(~rotationSwitchKeysAhead, GenSwitchKey(sk, Get1DHyperIndex(dim, pos)));
end for;
rotationSwitchKeysBack := [];
for pos := 1 to GetDimensionSize(dim) - 1 do
    Append(~rotationSwitchKeysBack, GenSwitchKey(sk, Get1DHyperIndex(dim, pos - GetDimensionSize(dim))));
end for;
switchKeyMinusD := GenSwitchKey(sk, Get1DHyperIndex(dim, -GetDimensionSize(dim)));

// Test linear transformation in first dimension
if IsGoodDimension(dim) then
    c := BlockMatMul1DGoodDimensionBabyGiant(c, adapted_constants, dim, rotationSwitchKeysAhead, frobeniusSwitchKeys);
else
    c := BlockMatMul1DBadDimensionBabyGiant(c, adapted_constantsAhead, adapted_constantsBack, dim,
                                            rotationSwitchKeysAhead, switchKeyMinusD, frobeniusSwitchKeys);
end if;
res := GetPlaintextParts(Decrypt(c, sk));
"Test stage 1 of linear maps", res eq [index le GetDimensionSize(1) select 1 else 0 : index in [1..l]];



// Embed single coefficient into slots
ind := Random(l - 1) + 1;
m := EmbedInSlots([Zx | i eq ind select Evaluate(GetNormalElement(), y ^ (p ^ Random(d - 1))) else 0 : i in [1..l]]);
c := Encrypt(m, t, pk);

// Compute linear transformation in first dimension
if IsGoodDimension(dim) then
    c := BlockMatMul1DGoodDimensionBabyGiant(c, adapted_constants, dim, rotationSwitchKeysAhead, frobeniusSwitchKeys);
else
    c := BlockMatMul1DBadDimensionBabyGiant(c, adapted_constantsAhead, adapted_constantsBack, dim,
                                            rotationSwitchKeysAhead, switchKeyMinusD, frobeniusSwitchKeys);
end if;

if GetNbDimensions() eq #factors_m then
    // Compute linear transformation in each dimension except for the first one
    for dim := 2 to GetNbDimensions() do
        dim_size := GetDimensionSize(dim);
        constants := EvalStage_dimConstants(dim, e);
        adapted_constants := MatMul1DGoodDimensionAdaptedConstants(constants, dim, e);
        adapted_constantsAhead, adapted_constantsBack := MatMul1DBadDimensionAdaptedConstants(constants, dim, e);

        // Generate switch keys
        switchKeysAhead := [];
        for pos := 1 to GetDimensionSize(dim) - 1 do
            Append(~switchKeysAhead, GenSwitchKey(sk, Get1DHyperIndex(dim, pos)));
        end for;
        switchKeysBack := [];
        for pos := 1 to GetDimensionSize(dim) - 1 do
            Append(~switchKeysBack, GenSwitchKey(sk, Get1DHyperIndex(dim, pos - GetDimensionSize(dim))));
        end for;
        switchKeyMinusD := GenSwitchKey(sk, Get1DHyperIndex(dim, -GetDimensionSize(dim)));

        // Good vs bad dimension
        if IsGoodDimension(dim) then
            c := MatMul1DGoodDimensionBabyGiant(c, adapted_constants, dim, switchKeysAhead);
        else
            c := MatMul1DBadDimensionBabyGiant(c, adapted_constantsAhead, adapted_constantsBack, dim,
                                            switchKeysAhead, switchKeyMinusD);
        end if;
    end for;
    Zxi := PolynomialRing(Z, #factors_m);
    res := Zxi!PolynomialToPowerfulBasis(Decrypt(c, sk), factors_m);
    mod_reduction := quo<Zxi | t>;
    res := Coefficients(Zxi!mod_reduction!res);
    "Test all stages of linear maps", (#res eq 1) and ((res[1] mod t) eq 1);



    // Test inverse linear transformation
    m := RandPol(t);
    c := Encrypt(m, t, pk);
    for dim := 1 to GetNbDimensions() do
        // Eval transformation
        constants := EvalStage_dimConstants(dim, e);
        adapted_constants := MatMul1DGoodDimensionAdaptedConstants(constants, dim, e);
        adapted_constantsAhead, adapted_constantsBack := MatMul1DBadDimensionAdaptedConstants(constants, dim, e);

        // Generate switch keys
        switchKeysAhead := [];
        for pos := 1 to GetDimensionSize(dim) - 1 do
            Append(~switchKeysAhead, GenSwitchKey(sk, Get1DHyperIndex(dim, pos)));
        end for;
        switchKeysBack := [];
        for pos := 1 to GetDimensionSize(dim) - 1 do
            Append(~switchKeysBack, GenSwitchKey(sk, Get1DHyperIndex(dim, pos - GetDimensionSize(dim))));
        end for;
        switchKeyMinusD := GenSwitchKey(sk, Get1DHyperIndex(dim, -GetDimensionSize(dim)));

        // Good vs bad dimension
        if IsGoodDimension(dim) then
            c := MatMul1DGoodDimensionBabyGiant(c, adapted_constants, dim, switchKeysAhead);
        else
            c := MatMul1DBadDimensionBabyGiant(c, adapted_constantsAhead, adapted_constantsBack, dim,
                                            switchKeysAhead, switchKeyMinusD);
        end if;



        // Inverse Eval transformation
        constants := EvalInvStage_dimConstants(dim, e);
        adapted_constants := MatMul1DGoodDimensionAdaptedConstants(constants, dim, e);
        adapted_constantsAhead, adapted_constantsBack := MatMul1DBadDimensionAdaptedConstants(constants, dim, e);

        // Good vs bad dimension
        if IsGoodDimension(dim) then
            c := MatMul1DGoodDimensionBabyGiant(c, adapted_constants, dim, switchKeysAhead);
        else
            c := MatMul1DBadDimensionBabyGiant(c, adapted_constantsAhead, adapted_constantsBack, dim,
                                            switchKeysAhead, switchKeyMinusD);
        end if;
        res := Decrypt(c, sk);

        "Test inverse linear map in dimension", dim, res eq m;
    end for;
end if;



// Test inverse BlockMatMul
dim := 1;
m := RandPol(t);
c := Encrypt(m, t, pk);

// Eval transformation
constants := EvalStage_1Constants(1, e);
adapted_constants := BlockMatMul1DGoodDimensionAdaptedConstants(constants, dim, e);
adapted_constantsAhead, adapted_constantsBack := BlockMatMul1DBadDimensionAdaptedConstants(constants, dim, e);

// Generate switch keys
rotationSwitchKeysAhead := [];
for pos := 1 to GetDimensionSize(dim) - 1 do
    Append(~rotationSwitchKeysAhead, GenSwitchKey(sk, Get1DHyperIndex(dim, pos)));
end for;
rotationSwitchKeysBack := [];
for pos := 1 to GetDimensionSize(dim) - 1 do
    Append(~rotationSwitchKeysBack, GenSwitchKey(sk, Get1DHyperIndex(dim, pos - GetDimensionSize(dim))));
end for;
switchKeyMinusD := GenSwitchKey(sk, Get1DHyperIndex(dim, -GetDimensionSize(dim)));

// Good vs bad dimension
if IsGoodDimension(dim) then
    c := BlockMatMul1DGoodDimensionBabyGiant(c, adapted_constants, dim, rotationSwitchKeysAhead, frobeniusSwitchKeys);
else
    c := BlockMatMul1DBadDimensionBabyGiant(c, adapted_constantsAhead, adapted_constantsBack, dim,
                                            rotationSwitchKeysAhead, switchKeyMinusD, frobeniusSwitchKeys);
end if;



// Inverse Eval transformation
constants := EvalInvStage_1Constants(1, e);
adapted_constants := BlockMatMul1DGoodDimensionAdaptedConstants(constants, dim, e);
adapted_constantsAhead, adapted_constantsBack := BlockMatMul1DBadDimensionAdaptedConstants(constants, dim, e);

// Good vs bad dimension
if IsGoodDimension(dim) then
    c := BlockMatMul1DGoodDimensionBabyGiant(c, adapted_constants, dim, rotationSwitchKeysAhead, frobeniusSwitchKeys);
else
    c := BlockMatMul1DBadDimensionBabyGiant(c, adapted_constantsAhead, adapted_constantsBack, dim,
                                            rotationSwitchKeysAhead, switchKeyMinusD, frobeniusSwitchKeys);
end if;
res := Decrypt(c, sk);

"Test inverse BlockMatMul linear map in dimension", dim, res eq m;



// Test unpacking the plaintext slots
constants := UnpackConstants(e);
adapted_constants := MatMulSlotsAdaptedConstants(constants, e);
repackConstants := RepackConstants(e);

// Create plaintext and ciphertext
m := EmbedInSlots([Zx | i eq 1 select GetNormalElement() else Evaluate(GetNormalElement(),
                                                                       y ^ (p ^ (Random(d - 2) + 1))) : i in [1..l]]);
c := Encrypt(m, t, pk);

"Test unpack slots", GetPlaintextParts(Decrypt(MatMulSlotsBabyGiant(c, adapted_constants, frobeniusSwitchKeys), sk)) eq
                     [i eq 1 select 1 else 0 : i in [1..l]];

res := UnpackSlots(c, constants, frobeniusSwitchKeys);
correct := true;
for numel := 1 to #res do
    plaintext_parts := GetPlaintextParts(Decrypt(res[numel], sk));
    if (numel eq 1) and (plaintext_parts ne [i eq 1 select 1 else 0 : i in [1..l]]) then
        correct := false;
    end if;
    if (numel ne 1) and (plaintext_parts[1] ne 0) then
        correct := false;
    end if;
    for slot := 2 to l do
        if (plaintext_parts[slot] ne 0) and (plaintext_parts[slot] ne 1) then
            correct := false;
        end if;
    end for;
end for;

"Test unpack slots", correct;



// Test repacking the plaintext slots
m := RandPol(t);
c := Encrypt(m, t, pk);

unpacked_slots := UnpackSlots(c, constants, frobeniusSwitchKeys);
repacked_slots := RepackSlots(unpacked_slots, repackConstants);
"Test repack slots", Decrypt(repacked_slots, sk) eq Decrypt(c, sk);