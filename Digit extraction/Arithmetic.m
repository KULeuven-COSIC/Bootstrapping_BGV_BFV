// Divide the given ciphertext by p
function div_pFunc(c)
    return ExactDivisionBy(c, p);
end function;

// Add the given ciphertexts and/or constants together
function addFunc(x, y)
    if IsCiphertext(x) and IsCiphertext(y) then
        return Add(x, y);
    elif IsCiphertext(x) then
        return AddConstant(x, y);
    elif IsCiphertext(y) then
        return AddConstant(y, x);
    end if;
end function;

// Subtract the given ciphertexts and/or constants
function subFunc(x, y)
    if IsCiphertext(x) and IsCiphertext(y) then
        return Sub(x, y);
    elif IsCiphertext(x) then
        return SubCiphertextConstant(x, y);
    elif IsCiphertext(y) then
        return SubConstantCiphertext(y, x);
    end if;
end function;

// Multiply the given ciphertexts and/or integer constants together
// This function cannot be used for lazy relinearization
function mulFunc(x, y, rk)
    if IsCiphertext(x) and IsCiphertext(y) then
        return Mul(x, y, rk);
    elif IsCiphertext(x) then
        return MulConstant(x, y);
    elif IsCiphertext(y) then
        return MulConstant(y, x);
    end if;
end function;

// Multiply the given ciphertexts and/or integer constants together
// This function can be used for lazy relinearization
function mulLazyFunc(x, y, rk)
    if IsCiphertext(x) and IsCiphertext(y) then
        // First relinearize both ciphertexts if necessary
        if GetNbParts(x) eq 3 then
            AutomaticModSwitchRelin(~x);
            x := Relin(x, rk);
        end if;
        if GetNbParts(y) eq 3 then
            AutomaticModSwitchRelin(~y);
            y := Relin(y, rk);
        end if;

        // Modulus switching is necessary to keep noise low
        AutomaticModSwitchMul(~x);
        AutomaticModSwitchMul(~y);
        return MulNR(x, y);
    elif IsCiphertext(x) then
        return MulConstant(x, y);
    elif IsCiphertext(y) then
        return MulConstant(y, x);
    end if;
end function;

// Relinearize the given ciphertext if necessary
function relinFunc(x, rk)
    if GetNbParts(x) eq 3 then
        AutomaticModSwitchRelin(~x);
        x := Relin(x, rk);
        DynamicModSwitch(~x);
    end if;
    return x;
end function;



/*** Overwrite basic arithmetic functions to count number of operations and total depth ***/
collision_param := 2^256;

function IsDummyCiphertext(c)
    // Keep set of IDs and whether ciphertext is relinearized
    return Category(c) eq Category(<{Z | }, true>);
end function;

function addDummyFunc(x, y)
    if IsDummyCiphertext(x) and IsDummyCiphertext(y) then
        return <x[1] join y[1], x[2] and y[2]>;
    elif IsDummyCiphertext(x) then
        return x;
    elif IsDummyCiphertext(y) then
        return y;
    end if;
end function;

function mulDummyFunc(x, y)
    if IsDummyCiphertext(x) and IsDummyCiphertext(y) then
        return <x[1] join y[1] join {Random(collision_param)}, true>;
    elif IsDummyCiphertext(x) then
        return x;
    elif IsDummyCiphertext(y) then
        return y;
    end if;
end function;

function mulLazyDummyFunc(x, y)
    if IsDummyCiphertext(x) and IsDummyCiphertext(y) then
        if x[2] and y[2] then
            return <x[1] join y[1], false>;
        elif x[2] or y[2] then
            return <x[1] join y[1] join {Random(collision_param)}, false>;
        else
            return <x[1] join y[1] join {Random(collision_param)} join {Random(collision_param)}, false>;
        end if;
    elif IsDummyCiphertext(x) then
        return x;
    elif IsDummyCiphertext(y) then
        return y;
    end if;
end function;

function relinDummyFunc(x)
    return x[2] select x else <x[1] join {Random(collision_param)}, true>;
end function;