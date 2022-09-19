load "Crypto/BGV/BGV.m";

sk, pk := GenKeyPair();
rk := GenRelinKey(sk);

m1 := RandPol(t);
c1 := Encrypt(m1, t, pk);
"Error on ciphertext c1", ErrorCanC(c1, sk);
"Estimated error on ciphertext c1", EstimatedErrorCanC(c1);

m2 := RandPol(t);
c2 := Encrypt(m2, t, pk);
"Error on ciphertext c2", ErrorCanC(c2, sk);
"Estimated error on ciphertext c2", EstimatedErrorCanC(c2);

cm := MulNR(c1, c2);
"Error on multiplied ciphertext", ErrorCanC(cm, sk);
"Estimated error on multiplied ciphertext", EstimatedErrorCanC(cm);

cmr := Relin(cm, rk);
"Error on relinearized ciphertext", ErrorCanC(cmr, sk);
"Estimated error on relinearized ciphertext", EstimatedErrorCanC(cmr);

cs := ModSwitch(cmr, baseModulus ^ (nbModuli div 2));
"Error on mod switched ciphertext", ErrorCanC(cs, sk);
"Estimated error on mod switched ciphertext", EstimatedErrorCanC(cs);

// Many consecutive multiplications
"";
csq := c1;
for i := 1 to 25 do
    csq := MulNR(csq, Encrypt(RandPol(t), t, pk));
    csq := Relin(csq, rk);

    if i mod 5 eq 0 then
        "Error after mul level " cat IntegerToString(i), ErrorCanC(csq, sk);
        "Estimated error after mul level " cat IntegerToString(i), EstimatedErrorCanC(csq);
        "";
    end if;
end for;