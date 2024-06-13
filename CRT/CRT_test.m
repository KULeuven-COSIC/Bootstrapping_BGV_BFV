load "CRT/CRT.m";

// Test conversion between polynomial and single CRT
poly := RandPol(&*modChain);
singleCRT := PolynomialToSingleCRT(poly);
res := SingleCRTToPolynomial(singleCRT);
"Test conversion to single CRT and back", poly eq res;

// Test conversion between single CRT and double CRT
doubleCRT := SingleCRTToDoubleCRT(singleCRT);
res := DoubleCRTToSingleCRT(doubleCRT);
"Test conversion to double CRT and back", singleCRT eq res;

// Test conversion between power and powerful basis
poly := RandPol(partialModuli[#partialModuli - 1]);
"Test conversion between power and powerful basis", PowerfulBasisToPolynomial(
                                                    PolynomialToPowerfulBasis(poly, PrimePowerFactorization(m)),
                                                                                    PrimePowerFactorization(m)) eq poly;