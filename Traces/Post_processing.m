// Deduplicate Galois elements and sort
galois_elts := Sort([el2 : el2 in {StringToInteger(el1) : el1 in Split(Read(CONSTANTS))}]);

PrintFile(CONSTANTS, "#include \"constants.h\"": Overwrite := true);
PrintFile(CONSTANTS, "");
PrintFile(CONSTANTS, "const uint64_t global_log2N = " cat IntegerToString(Round(Log(2, m))) cat ";");
PrintFile(CONSTANTS, "const uint64_t global_prime_plaintext_modulus = " cat IntegerToString(p) cat ";");
PrintFile(CONSTANTS, "const std::vector<uint32_t> global_galois_elements{ " cat &cat[Strings() | IntegerToString(galois_elts[index])
                     cat (index eq #galois_elts select "" else ", ") : index in [1..#galois_elts]] cat " };");

// Write deletes to trace file
nb_ops := StringToInteger(Read(output_folder cat "ops")); trace := Split(Read(TRACE), "\t");
assert #trace eq (nb_ops + 1); assert #Split(Read(output_folder cat "ctxt")) eq nb_ops;
for hash in Split(Read(output_folder cat "ctxt")) do
    last_used := StringToInteger(Read(output_folder cat "Files/" cat hash));
    if last_used eq 0 then
        DeleteCiphertext(hash);
    else
        trace[last_used + 1] cat:= ("delete " cat hash cat "; " cat hash cat " = NULL;\n");
    end if;
end for;

// Concatenate files to get final trace
PrintFile(output_folder cat "trace.cpp", "#include \"trace.h\"\n": Overwrite := true);
PrintFile(output_folder cat "trace.cpp", "void run_trace(Bootstrapper& bootstrapper, const BootstrappingKey& bk, " cat
                                          "Encryptor& encryptor, Decryptor& decryptor,\n\t\t\t   " cat
                                          "Encryptor& target_encryptor, Decryptor& target_decryptor)");
PrintFile(output_folder cat "trace.cpp", "{\n\t// INIT");
PrintFile(output_folder cat "trace.cpp", &cat["\n\t" cat el : el in Split(Read(INIT))]);
PrintFile(output_folder cat "trace.cpp", "\n\t// TRACE");
PrintFile(output_folder cat "trace.cpp", &cat["\n\t" cat el : el in Split(&cat(trace))]);
PrintFile(output_folder cat "trace.cpp", "\n\t// TERMINATE");
PrintFile(output_folder cat "trace.cpp", &cat["\n\t" cat el : el in Split(Read(TERMINATE) cat Read(TERMINATE_DELETE))]);
PrintFile(output_folder cat "trace.cpp", "}");
exit;