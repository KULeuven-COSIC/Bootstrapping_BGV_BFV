load "Crypto/General.m";
load "Arithmetic/Powerful.m";

// Test conversion between power and powerful basis
poly := RandPol(q);
"Test conversion between power and powerful basis", PowerfulBasisToPolynomial(
                                                    PolynomialToPowerfulBasis(poly, PrimePowerFactorization(m)),
                                                                                    PrimePowerFactorization(m)) eq poly;