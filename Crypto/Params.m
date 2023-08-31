// This file stores the parameters for the BGV and BFV scheme
//--------------------------

// Parameter setup
q := 2^300;                           // Ciphertext modulus
m := 2^10 - 1;                        // m-th cyclotomic polynomial
n := EulerPhi(m);                     // Degree of f(x)
p := 2;                               // Plaintext prime modulus
r := 1;                               // Original Hensel lifting factor
e := 8;                               // Extended Hensel lifting factor during bootstrapping
t := p^e;                             // Plaintext modulus during bootstrapping
h := 120;                             // Hamming weight secret keys, ternary {0, -/+1}
errorB := 20;                         // Binomial sampling on [-errorB, errorB] with sigma = Sqrt(errorB/2)
L := 5;                               // Number of pieces when splitting
w := 2 ^ Ceiling(Log(2, Root(q, L))); // Base for relinearization, relin key goes from w^0 to w^(L-1)

// Polynomials over integers
Z := Integers();
Zx<x> := PolynomialRing(Z);
f := Zx!CyclotomicPolynomial(m);

// Plaintext ring
Zt := Integers(t);
Zt_poly := PolynomialRing(Zt);

// Structure of automorphism group and coprime factorization of m
Zm := Integers(m);
factors_m := [];
usePowerOfTwo := false;

// Real and complex numbers used for error estimation
R := RealField(10);
C := ComplexField(10);
xi := Exp(2 * Pi(C) * C.1 / m);

// Experimental constants
can_max := 900;                   // To be determined experimentally from "Scripts/Find_can_max.m" after setting other parameters
expansion_automorphism := 2^10;   // The maximum growth of the norm when an automorphism is applied to an element

// Constants for determining the modulus chain and modulus switching details
enableModSwitch := false;         // Only for the BFV scheme
modPrecision := 2^5;              // Determines the precision of the modulus (how close it is to its optimal value)
noiseLevelMul := 2^5;             // Magnitude of the noise before multiplication (cannot be too high to prevent decryption errors)
noiseLevelRelin := 2^5 * t * w * Sqrt((n / 12) * L * (errorB * n / 2)); // Magnitude of the noise before key switching

// Constants related to the prime-modulus chain
// Necessary for conversion to CRT representation and powerful basis
minModulus := 2 ^ 63;
maxModulus := 2 ^ 64 - 1;