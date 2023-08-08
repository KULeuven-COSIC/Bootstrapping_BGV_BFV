// Support for converting between polynomial, single CRT, double CRT and powerful basis
//--------------------------
load "CRT/FFT.m";

/*****
 * Remark:
 * The custom FFT algorithm that we implemented in Magma is not optimal, probably due
 * to random memory accesses. It is therefore recommended to use the functions in this
 * file only when absolutely necessary.
 * --> For example: use for implementing automorphisms
 *****/



// Return a list of prime moduli that can be used for converting to CRT representation
function GenerateModulusChain(m, nbModuli, minModulus, maxModulus)
    base := 2 * m;
    moduli := [];
    for multiplier := Ceiling((minModulus - 1) / base) to Floor((maxModulus - 1) / base) do
        modulus := base * multiplier + 1;
        if IsPrime(modulus) then
            Append(~moduli, modulus);
            if #moduli eq nbModuli then
                return moduli;
            end if;
        end if;
    end for;
    
    error "Not enough moduli in the given range.";
end function;

// Store modulus chain and precomputation for general FFT
modChain := GenerateModulusChain(m, Ceiling(Log(minModulus, q * expansion_automorphism)), minModulus, maxModulus);
partialModuli := [Z | &*modChain[1..index] : index in [1..#modChain]];
precompList := <PrecompBluestein(m, modulus) : modulus in modChain>;

// Info for recombination of RNS representation
recombLarge := [Z | &*modChain div modulus : modulus in modChain];
recombSmall := [Z | Modinv(recombLarge[index], modChain[index]) : index in [1..#modChain]];



// Convert the given coefficients to CRT representation
function CoefficientsToCRT(coeff, m, p, precomp)
    output := BluesteinFFT(CatZeros(coeff, m), m, p, precomp);
    for currentExponent := 0 to m - 1 do
        if GCD(currentExponent, m) ne 1 then
            Undefine(~output, currentExponent + 1);
        end if;
    end for;
    return output;
end function;

// Convert the given CRT representation to coefficients
function CRTToCoefficients(x, m, p, precomp)
    for currentIndex := 1 to m do
        if not IsDefined(x, currentIndex) then
            x[currentIndex] := 0;
        end if;
    end for;
    output := BluesteinFFTInv(x, m, p, precomp);
    return Eltseq(((Zx!output) mod precomp[5]) mod p);
end function;



// Convert the given polynomial to single CRT representation
function PolynomialToSingleCRT(poly: level := #modChain)
    assert level le #modChain;          // level should not exceed number of primes
    return [Zx | poly mod modulus : modulus in modChain[1..level]];
end function;

// Convert the given single CRT representation to a polynomial
function SingleCRTToPolynomial(singleCRT)
    return &+[Zx | ((singleCRT[ind] * recombSmall[ind]) mod modChain[ind]) * recombLarge[ind] : ind in [1..#singleCRT]] mod
           partialModuli[#singleCRT];
end function;

// Convert the given single CRT representation to double CRT
function SingleCRTToDoubleCRT(singleCRT)
    return [CoefficientsToCRT(Eltseq(singleCRT[index]), m, modChain[index], precompList[index]) : index in [1..#singleCRT]];
end function;

// Convert the given double CRT representation to single CRT
function DoubleCRTToSingleCRT(doubleCRT)
    return [Zx | CRTToCoefficients(doubleCRT[index], m, modChain[index], precompList[index]) : index in [1..#doubleCRT]];
end function;

// Convert the given polynomial to double CRT representation
function PolynomialToDoubleCRT(poly: level := #modChain)
    assert level le #modChain;          // level should not exceed number of primes
    return SingleCRTToDoubleCRT(PolynomialToSingleCRT(poly: level := level));
end function;

// Convert the given double CRT representation to a polynomial
function DoubleCRTToPolynomial(doubleCRT)
    return SingleCRTToPolynomial(DoubleCRTToSingleCRT(doubleCRT));
end function;



// Convert the given element of the power basis to the powerful basis
function PolynomialToPowerfulBasis(element, factors_m)
    // Set up necessary data structures
    cyclotomicPolynomials := [Zx | CyclotomicPolynomial(factor) : factor in factors_m];
    Zxi := PolynomialRing(Z, #factors_m);
    res := Zxi!0;

    // Parameters for conversion
    k := &+[m div factors_m[index] : index in [1..#factors_m]];
    l := Modinv(k, m);

    // Iterate over each monomial and compute the value in the powerful basis
    seq := Eltseq(element);
    for index := 1 to #seq do
        res +:= seq[index] * (&*[Evaluate((x ^ ((l * (index - 1)) mod factors_m[var]))
                                 mod cyclotomicPolynomials[var], Zxi.var) : var in [1..#factors_m]]);
    end for;
    return res;
end function;

// Convert the given element of the powerful basis to the power basis
function PowerfulBasisToPolynomial(element, factors_m)
    return Evaluate(element, [x ^ (m div factor) : factor in factors_m]) mod f;
end function;

// Return a polynomial that, when considered in the powerful basis, contains
// the given value at all coefficients
function EmbedInPowerfulBasis(value, factors_m)
    Zxi := PolynomialRing(Z, #factors_m);
    max_indices := [EulerPhi(factor) : factor in factors_m];

    // Loop over each possible monomial
    res := Zxi!0;
    for currentMonomial := 0 to m - 1 do
        currentValue := value;    // Value of the current coefficient

        // We add a monomial if the current index is in the valid range
        for var := 1 to #factors_m do
            if (currentMonomial mod factors_m[var]) ge max_indices[var] then
                currentValue := 0;
                break;
            end if;
        end for;
        res +:= currentValue * (&*[Zxi.var ^ (currentMonomial mod factors_m[var]) : var in [1..#factors_m]]);
    end for;
    return PowerfulBasisToPolynomial(res, factors_m);
end function;
