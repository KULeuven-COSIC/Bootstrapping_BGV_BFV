// Count the number of basic homomorphic operations for the decomposed slot-to-coefficient
// transformation for power-of-two cyclotomics
// The count corresponds to the behaviour implemented in 'Linear maps/PowerOfTwo'
load "Crypto/BFV/BFV.m";
load "Linear maps/PowerOfTwo/Linear_maps.m";

m := 2^16;                      // m-th cyclotomic polynomial
n := EulerPhi(m);               // Degree of f(x)
p := 2^16 + 1;                  // Plaintext prime modulus
d := Order(Integers(m)!p);      // Degree of irreducible factors
l := n div d;                   // Number of slots

mat_dimensions := [2^7, 2^8];   // Matrix dimensions for our linear transformations (specified in reverse order: L_T, ..., L_1)

assert IsPowerOfTwo(m);
assert IsPrime(p);
assert GCD(m, p) eq 1;
assert #mat_dimensions ge 1;
assert &*mat_dimensions eq l;
assert (p mod 4 eq 3) or mat_dimensions[1] ge 2;

// Fully packed slots (only possible for at least 2 matrix dimensions)
if #mat_dimensions ge 2 then
    nb_auto := 0; nb_mul := 0;

    // First stage
    if p mod 4 eq 1 then
        nb_mul +:= 2 * d * mat_dimensions[1];
        g_seq, h_seq := GetGeneralBabyGiantParams([d, 2, mat_dimensions[1] div 2]);
    else
        nb_mul +:= 2 * (d div 2) * mat_dimensions[1];
        g_seq, h_seq := GetGeneralBabyGiantParams([d div 2, mat_dimensions[1]]);
    end if;
    g := &*g_seq; h := &*h_seq;
    nb_auto +:= 2 * g + h - 2;

    // Other stages
    for index := 2 to #mat_dimensions - 1 do
        g, h := GetBabyGiantParams(mat_dimensions[index]);
        nb_auto +:= 2 * g + h - 2;
        nb_mul +:= 2 * mat_dimensions[index];
    end for;

    // Last stage
    if p mod 4 eq 1 then
        nb_mul +:= d * mat_dimensions[#mat_dimensions];
        g, h := GetBabyGiantParams(d * mat_dimensions[#mat_dimensions]);
    else
        nb_mul +:= (d div 2) * mat_dimensions[#mat_dimensions];
        g, h := GetBabyGiantParams((d div 2) * mat_dimensions[#mat_dimensions]);
    end if;
    nb_auto +:= g + h - 2;

    // Prior methods
    g_seq, h_seq := GetGeneralBabyGiantParams([2, n div 2]);
    g := &*g_seq; h := &*h_seq;
    nb_auto_prior := g + h - 2;
    nb_mul_prior := n;

    "\nWe need", nb_auto, "automorphisms and", nb_mul,
    "multiplications for the packed slot-to-coefficient transformation. There are", #mat_dimensions, "multiplicative levels.";
    "Prior methods need", nb_auto_prior, "automorphisms and", nb_mul_prior,
    "multiplications for the packed slot-to-coefficient transformation. There is 1 multiplicative level.";
end if;

// Sparsely packed slots (trace operation is not counted)
nb_auto := 0; nb_mul := 0;
if p mod 4 eq 1 then    // First stage
    g_seq, h_seq := GetGeneralBabyGiantParams([2, mat_dimensions[1] div 2]);
    g := &*g_seq; h := &*h_seq;
    nb_auto +:= 2 * g + h - 2;
    nb_mul +:= 2 * mat_dimensions[1];
end if;
for index := (p mod 4 eq 1 select 2 else 1) to #mat_dimensions do
    g, h := GetBabyGiantParams(mat_dimensions[index]);
    if index eq #mat_dimensions then    // Last stage
        nb_auto +:= g + h - 2;
        nb_mul +:= mat_dimensions[index];
    else
        nb_auto +:= 2 * g + h - 2;
        nb_mul +:= 2 * mat_dimensions[index];
    end if;
end for;

// Prior methods
g_seq, h_seq := GetGeneralBabyGiantParams([2, l div 2]);
g := &*g_seq; h := &*h_seq;
nb_auto_prior := g + h - 2;
nb_mul_prior := l;

"\nWe need", nb_auto, "automorphisms and", nb_mul,
"multiplications for the sparse slot-to-coefficient transformation. There are", #mat_dimensions, "multiplicative levels.";
"Prior methods need", nb_auto_prior, "automorphisms and", nb_mul_prior,
"multiplications for the sparse slot-to-coefficient transformation. There is 1 multiplicative level.";

if d eq 1 then
    "\nSlot unpacking and repacking are free, because there is complete splitting.";
else
    // Slot unpacking
    "\nWe need", d - 1, "automorphisms and", d - 1, "multiplications for slot unpacking.";
    "Prior methods need", d - 1, "automorphisms and", d ^ 2, "multiplications for slot unpacking. There is 1 multiplicative level.";

    // Slot repacking
    "\nWe need", d - 1, "multiplications for slot repacking.";
    "Prior methods need", d, "multiplications for slot repacking. There is 1 multiplicative level.";
end if;