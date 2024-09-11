# Bootstrapping_BGV_BFV

Magma implementation of bootstrapping for BGV and BFV.

Any bugs can be reported to robin.geelen@esat.kuleuven.be.

## Content

The code is divided over the following folders:
* [`Arithmetic`](Arithmetic) contains functions to convert between power basis, powerful basis and FFT domain.
* [`Crypto`](Crypto) contains the implementation of BGV and BFV, including rotations and Frobenius maps.
* [`Linear maps`](Linear%20maps) provides functionality to map plaintext coefficients to slots and vice versa.
* [`Digit extraction`](Digit%20extraction) is necessary to extract the upper digits of a sparsely packed or "thin" ciphertext.
* [`Bootstrapping`](Bootstrapping) contains the actual bootstrapping algorithm for fully packed as well as for "thin" ciphertexts.

## Installation

* Obtain a Magma license from http://magma.maths.usyd.edu.au/magma.
* Start Magma and change to the root directory of this repository via the “ChangeDirectory” command.
* Load the desired file via the “load” command.
