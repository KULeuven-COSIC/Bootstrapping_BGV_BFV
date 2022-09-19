load "CRT/FFT.m";

// Test Bluestein FFT
function TestBluesteinFFT1()
    // Note that p - 1 divisible by 2 ^ n for n = 40 so anything less is fine
    p := 64113622527246337;
    m := 31;

    // Precomputations
    precomp := PrecompBluestein(m, p);
    omega := precomp[1] ^ 2;

    // Random vector of elements to take FFT
    x := [Random(p) : i in [1..m]];
    simpleFFT := [Z | &+[x[i + 1] * omega ^ (k * i) : i in [0..m - 1]] : k in [0..m - 1]];

    // Test forward and backward FFT
    test_forward := simpleFFT eq BluesteinFFT(x, m, p, precomp);
    test_backward := BluesteinFFTInv(simpleFFT, m, p, precomp) eq x;

    return test_forward and test_backward;
end function;

// Test Bluestein FFT for power of 2
function TestBluesteinFFT2()
    // Note that p - 1 divisible by 2 ^ n for n = 40 so anything less is fine
    p := 64113622527246337;
    m := 2^7;

    // Precomputations
    precomp := PrecompBluestein(m, p);
    omega := precomp[1] ^ 2;

    // Random vector of elements to take FFT
    x := [Random(p) : i in [1..m]];
    simpleFFT := [Z | &+[x[i + 1] * omega ^ (k * i) : i in [0..m - 1]] : k in [0..m - 1]];

    // Test forward and backward FFT
    test_forward := simpleFFT eq BluesteinFFT(x, m, p, precomp);
    test_backward := BluesteinFFTInv(simpleFFT, m, p, precomp) eq x;

    return test_forward and test_backward;
end function;

// Test Bluestein FFT for even times odd number
function TestBluesteinFFT3()
    // Note that p - 1 divisible by 2 ^ n for n = 40 so anything less is fine
    p := 64113622527246337;
    m := 2^3 * 31;

    // Precomputations
    precomp := PrecompBluestein(m, p);
    omega := precomp[1] ^ 2;

    // Random vector of elements to take FFT
    x := [Random(p) : i in [1..m]];
    simpleFFT := [Z | &+[x[i + 1] * omega ^ (k * i) : i in [0..m - 1]] : k in [0..m - 1]];

    // Test forward and backward FFT
    test_forward := simpleFFT eq BluesteinFFT(x, m, p, precomp);
    test_backward := BluesteinFFTInv(simpleFFT, m, p, precomp) eq x;

    return test_forward and test_backward;
end function;

"Test Bluestein FFT", TestBluesteinFFT1();
"Test Bluestein FFT power of two", TestBluesteinFFT2();
"Test Bluestein FFT even times odd", TestBluesteinFFT3();