hash_prime := 634564036503856717;
hash_length := 16;

hash_ct1 := RandPol(hash_prime);
hash_ct2 := RandPol(hash_prime);
hash_ct3 := RandPol(hash_prime);
hash_ct4 := RandPol(hash_prime);
hash_ct5 := RandPol(hash_prime);
hash_ct6 := RandPol(hash_prime);
hash_ct7 := RandPol(hash_prime);
hash_ct8 := RandPol(hash_prime);

// Check whether the given ciphertext is transparent
function IsTransparent(input)
    for element in input[1][2..#input[1]] do
        if (element mod input[3]) ne 0 then
            return false;
        end if;
    end for;
    return true;
end function;

// Check if plaintext or ciphertext is equal to zero
function IsZero(input)
    if IsCiphertext(input) then
        return IsTransparent(input) and Decrypt(input, 0: print_result := false) eq 0;
    else
        return input eq 0;
    end if;
end function;

// Check if plaintext or ciphertext is equal to one
function IsOne(input)
    if IsCiphertext(input) then
        return IsTransparent(input) and Decrypt(input, 0: print_result := false) eq 1;
    else
        return input eq 1;
    end if;
end function;

// Check if plaintext or ciphertext has degree zero
function HasDegreeZero(input)
    if IsCiphertext(input) then
        return IsTransparent(input) and Degree(Zx!input[1][1]) lt 1;
    else
        return Degree(Zx!input) lt 1;
    end if;
end function;

// Convert polynomial to string
function PolynomialToString(poly)
    poly := Eltseq(Zx!poly);
    if #poly gt 0 then
        res := "";
        exp := #poly;

        // Print coefficient per coefficient
        print_plus := false;
        for coeff in Reverse(poly) do
            exp -:= 1;
            if coeff eq 0 then
                continue;
            end if;

            // Concatenate current term
            res cat:= (print_plus select " + " else "") cat IntegerToString(coeff, 16) cat
                      (exp eq 0 select "" else ("x^" cat IntegerToString(exp)));
            print_plus := true;
        end for;
        return res;
    else
        return "0";
    end if;
end function;

// A very simple hash function for ciphertexts
function MyHash(input)
    if IsZero(input) then
        return "ZERO_CIPHERTEXT_" cat (IsHighLevel(input) select "HIGH" else "LOW");
    end if;

    // A few simple operations on the ciphertext
    result := ((hash_ct1 * (input[1][1] mod hash_prime) + hash_ct2) mod f);
    if #input[1] gt 1 then
        result +:= ((hash_ct3 * (input[1][2] mod hash_prime) + hash_ct4) mod f);
        if #input[1] gt 2 then
            result +:= ((hash_ct5 * (input[1][3] mod hash_prime) + hash_ct6) mod f);
        end if;
    end if;
    result := CatZeros(Eltseq(result mod hash_prime), hash_length);

    // Compute hash value
    hash := "";
    for index := 1 to hash_length do
        hash cat:= IntegerToString((result[index] mod 26) + 10, 36);
    end for;
    return hash;
end function;

// Return a random number in the hash range
function RandomHash()
    hash := "";
    for index := 1 to hash_length do
        hash cat:= IntegerToString(Random(10, 35), 36);
    end for;
    return hash;
end function;