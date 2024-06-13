// This file stores the parameters for the BGV and BFV scheme
//--------------------------

// Parameter setup
q := 2^300;                             // Ciphertext modulus
m := 2^10 - 1;                          // m-th cyclotomic polynomial
n := EulerPhi(m);                       // Degree of f(x)
p := 2;                                 // Plaintext prime modulus
r := 1;                                 // Original Hensel lifting factor
e := 8;                                 // Extended Hensel lifting factor during bootstrapping
t := p^e;                               // Plaintext modulus during bootstrapping
h := 120;                               // Hamming weight secret keys, ternary {0, -/+1}
errorB := 20;                           // Binomial sampling on [-errorB, errorB] with sigma = Sqrt(errorB/2)
L := 5;                                 // Number of pieces when splitting
w := 2 ^ Ceiling(Log(2, Root(q, L)));   // Base for relinearization, relin key goes from w^0 to w^(L-1)

// Structure of automorphism group and coprime factorization of m
factors_m := [];                  // Factorization of m for HElib linear transformations (prime-power factorization by default)
mat_dimensions := [];             // Matrix dimensions for our linear transformations (specified in reverse order: L_T, ..., L_1)
usePowerOfTwo := false;           // Use SEAL or our version of linear transformations if true and HElib version if false

// Parameters for determining the modulus chain and modulus switching details
// The second (resp. third) parameter should be small (resp. large) enough to prevent noise blow-up
enableModSwitch := true;          // Only for the BFV scheme
noiseLevelMul := 2^5;             // Noise is brought to this level before BGV multiplication
noiseLevelRelin := 2^5 * t * w * Sqrt((n / 12) * L * (errorB * n / 2));   // Noise is brought to this level before key switching

// Experimental parameters
can_max := 900;                   // To be determined experimentally from 'Scripts/Find_can_max.m' after setting other parameters
expansion_automorphism := 2^10;   // The maximum growth of the norm when an automorphism is applied to an element



/*** The following parameters should not be changed in normal circumstances ***/

// Integers and quotient rings
Z := Integers();
Zm := Integers(m);
Zt := Integers(t);

// Polynomial rings
Zx<x> := PolynomialRing(Z);
Zt_poly := PolynomialRing(Zt);
f := Zx!CyclotomicPolynomial(m);

// Real and complex numbers used for error estimation
R := RealField(10);
C := ComplexField(10);
xi := Exp(2 * Pi(C) * C.1 / m);

// Parameters related to the prime-modulus chain
// Necessary for conversion to CRT representation and powerful basis
minModulus := 2 ^ 63;
maxModulus := 2 ^ 64 - 1;