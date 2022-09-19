// Generate a bootstrapping key for sk
function GenBootKeyRecrypt(sk, pk, henselExponentCiphertext)
    return Encrypt(sk, p ^ henselExponentCiphertext, pk);
end function;