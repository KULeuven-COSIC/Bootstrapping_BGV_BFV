output_folder := "Bootstrapping_SEAL/";
IGNORE_DIGIT_EXTRACTION := false;
// This file stores the parameters for the BGV and BFV scheme
//--------------------------

// Parameter setup
q := 2^2000;                      // Ciphertext modulus
m := 2^15;                        // m-th cyclotomic polynomial
p := 2^16 + 1;                    // Plaintext prime modulus
r := 1;                           // Original Hensel lifting factor
e := 2;                           // Extended Hensel lifting factor during bootstrapping
h := 32;                          // Hamming weight secret keys, ternary {0, -/+1}
errorB := 20;                     // Binomial sampling on [-errorB, errorB] with sigma = Sqrt(errorB/2)
B := 15;                          // Range of the noise for bootstrapping (only for e = 2 and p > 2)
L := 5;                           // Number of pieces when splitting the relin key

// Parameters for linear transformations
factors_m := [];                  // Factorization of m for HElib linear transformations (prime-power factorization by default)
mat_dimensions := [2^7, 2^7];     // Matrix dimensions for our linear transformations (specified in reverse order: L_T, ..., L_1)
usePowerOfTwo := true;            // Use SEAL or our version of linear transformations if true and HElib version if false

// Details for modulus switching and noise growth
// The second (resp. third) parameter should be small (resp. large) enough to prevent noise blow-up
enableModSwitch := false;         // Only for the BFV scheme
noiseLevelMul := 2^5;             // Noise is brought to this level before BGV multiplication
noiseBufferRelin := 2^5;          // Buffer for noise level before key switching
can_max := 1500;                  // To be determined experimentally from 'Scripts/Find_can_max.m' after setting other parameters

// Batch encoding in plaintext slots can be done with naive or FFT-based algorithm
useFFTBatchEncoder := true;       // Use batch encoder based on FFT algorithm (only possible if m is a power of two)

// GBFV parameters for binomial plaintext modulus
gbfvExponent := 2^13;             // Degree of the GBFV plaintext modulus
gbfvCoefficient := 2^8;           // Coefficient of the GBFV plaintext modulus