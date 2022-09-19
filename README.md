# Bootstrapping_BGV_BFV

Magma implementation of bootstrapping for BGV and BFV.

## Content

The code is divided over the following folders:
* [`CRT`](CRT) contains functions to convert between power basis, powerful basis, single and double CRT.
* [`Crypto`](Crypto) contains the implementation of BGV and BFV, including rotations and Frobenius maps.
* [`Linear maps`](Linear%20maps) provides functionality to map plaintext coefficients to slots and vice versa.
* [`Digit extraction`](Digit%20extraction) is necessary to extract the upper digits of a sparsely packed or "thin" ciphertext.
* [`Bootstrapping`](Bootstrapping) contains the actual bootstrapping algorithm for fully packed as well as for "thin" ciphertexts.
