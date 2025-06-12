output_folder := "Bootstrapping_SEAL/";
IGNORE_DIGIT_EXTRACTION := false;
// This file stores the parameters for the BGV and BFV scheme
//--------------------------

// Parameter setup
q := 2^900;                       // Ciphertext modulus
m := 2^10;                        // m-th cyclotomic polynomial
p := 2^16 + 1;                    // Plaintext prime modulus
r := 1;                           // Original Hensel lifting factor
e := 2;                           // Extended Hensel lifting factor during bootstrapping
h := 32;                          // Hamming weight secret keys, ternary {0, -/+1}
errorB := 20;                     // Binomial sampling on [-errorB, errorB] with sigma = Sqrt(errorB/2)
B := 15;                          // Range of the noise for bootstrapping (only for e = 2 and p > 2)
L := 5;                           // Number of pieces when splitting the relin key

// Parameters for linear transformations
factors_m := [];                  // Factorization of m for HElib linear transformations (prime-power factorization by default)
mat_dimensions := [];             // Matrix dimensions for our linear transformations (in SlotToCoeff order: L_T, ..., L_1)
useHElibLT := false;              // Use HElib version of linear transformations
useSEALLT := false;               // Use SEAL version of linear transformations
useOurLT := false;                // Use our BFV version of linear transformations
useGBFVLT := true;                // Use our improved GBFV linear transformations

// Details for modulus switching and noise growth
// The second (resp. third) parameter should be small (resp. large) enough to prevent noise blow-up
enableModSwitch := false;         // Only for the BFV scheme
noiseLevelMul := 2^5;             // Noise is brought to this level before BGV multiplication
noiseBufferRelin := 2^5;          // Buffer for noise level before key switching
can_max := 1500;                  // To be determined experimentally from 'Scripts/Find_can_max.m' after setting other parameters

// Batch encoding in plaintext slots can be done with naive or FFT-based algorithm
useFFTBatchEncoder := true;       // Use batch encoder based on FFT algorithm (only possible if m is a power of two)

// GBFV parameters
Z := Integers();                  // Integers
Zx<x> := PolynomialRing(Z);       // Polynomial ring
gbfvExponent := 2^7;              // Exponent of plaintext modulus
gbfvCoefficient := 2^(2^2);       // Coefficient of plaintext modulus
gbfvModulus := x ^ gbfvExponent - gbfvCoefficient;

// GBFV parameters for improved bootstrapping
n_prime := 2^5;                   // GBFV ring dimension
n_double_prime := 2^3;            // BFV ring dimension
intModuli := [Zx | ];             // Intermediate GBFV plaintext moduli
gbfv_mat_dimensions := [Z | 2^5]; // Matrix dimensions for GBFV linear transformations (in SlotToCoeff order: 2^(l_1), ..., 2^(l_s))