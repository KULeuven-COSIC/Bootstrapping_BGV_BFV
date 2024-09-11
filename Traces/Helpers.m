INIT := output_folder cat "tmp_trace_1.cpp";
TRACE := output_folder cat "tmp_trace_2.cpp";
TERMINATE := output_folder cat "tmp_trace_3.cpp";
TERMINATE_DELETE := output_folder cat "tmp_trace_4.cpp";
CONSTANTS := output_folder cat "constants.cpp";
PrintFile(INIT, "": Overwrite := true);
PrintFile(TRACE, "": Overwrite := true);
PrintFile(TERMINATE, "": Overwrite := true);
PrintFile(TERMINATE_DELETE, "": Overwrite := true);
PrintFile(CONSTANTS, "": Overwrite := true);
PrintFile(output_folder cat "ctxt", "": Overwrite := true);
PrintFile(output_folder cat "ops", 0: Overwrite := true);
PrintFile(output_folder cat "is_ntt_optimal_domain", 1: Overwrite := true);

function GetOperationCount()
    return StringToInteger(Read(output_folder cat "ops"));
end function;

procedure IncreaseOperationCount()
    PrintFile(output_folder cat "ops", GetOperationCount() + 1: Overwrite := true);
end procedure;



procedure UseCiphertext(hash: terminate := false)
    if terminate then
        PrintFile(output_folder cat "Files/" cat hash, 0: Overwrite := true);
    elif not ((hash in Split(Read(output_folder cat "ctxt"))) and (Read(output_folder cat "Files/" cat hash) eq "0\n")) then
        PrintFile(output_folder cat "Files/" cat hash, GetOperationCount(): Overwrite := true);
    end if;
end procedure;

procedure CreateCiphertext(hash)
    IncreaseOperationCount();
    UseCiphertext(hash);
    PrintFile(output_folder cat "ctxt", hash);
    PrintFile(TRACE, "\tCiphertext* " cat hash cat " = new Ciphertext;");
end procedure;

procedure DeleteCiphertext(hash)
    PrintFile(TERMINATE_DELETE, "delete " cat hash cat "; " cat hash cat " = NULL;");
end procedure;

procedure SetOptimalCoefficientDomain()
    PrintFile(TRACE, "bootstrapper.set_optimal_coefficient_domain();");
    PrintFile(output_folder cat "is_ntt_optimal_domain", 0: Overwrite := true);
end procedure;

procedure SetOptimalNTTDomain(: file := TRACE)
    PrintFile(file, "bootstrapper.set_optimal_ntt_domain();");
    PrintFile(output_folder cat "is_ntt_optimal_domain", 1: Overwrite := true);
end procedure;

function IsOptimalNTTDomain()
    return Read(output_folder cat "is_ntt_optimal_domain") eq "1\n";
end function;



procedure UsePlaintext(hash, plaintext)
    PrintFile(output_folder cat "Files/" cat hash, PolynomialToString(plaintext): Overwrite := true);
    PrintFile(INIT, "Plaintext " cat hash cat ";");
    PrintFile(INIT, "bootstrapper.read_plaintext_from_file(" cat hash cat ", \"" cat hash cat "\");");
end procedure;

procedure UsePlaintextNTT(hash, plaintext, high_level)
    UsePlaintext(hash, plaintext);
    PrintFile(INIT, "bootstrapper.transform_to_ntt_inplace(" cat hash cat ", " cat
                    (high_level select "ZERO_CIPHERTEXT_HIGH" else "ZERO_CIPHERTEXT_LOW") cat
                    "->parms_id(), " cat (high_level select "1" else "0") cat ");");
end procedure;

procedure UsePlaintextOptimalDomain(hash, plaintext, high_level)
    if IsOptimalNTTDomain() then
        UsePlaintextNTT(hash, plaintext, high_level);
    else
        UsePlaintext(hash, plaintext);
    end if;
end procedure;

procedure EncryptPlaintextToCiphertext(hash1, hash2, high_level)
    PrintFile(INIT, "Ciphertext* " cat hash2 cat " = new Ciphertext;");
    PrintFile(INIT, (high_level select "target_encryptor" else "encryptor") cat ".encrypt(" cat
                     hash1 cat ", *" cat hash2 cat ");");
    DeleteCiphertext(hash2);
end procedure;



function StartTiming()
    timer := RandomHash();
    PrintFile(TRACE, "auto " cat timer cat "_start = std::chrono::steady_clock::now();");
    return timer;
end function;

procedure StopTiming(timer: message := "")
    message := (message eq "") select "" else (" " cat message);
    PrintFile(TRACE, "auto " cat timer cat "_end = std::chrono::steady_clock::now();");
    PrintFile(TRACE, "std::cout << \"timing" cat message cat ": \" << std::chrono::duration_cast<std::chrono::milliseconds>" cat
                     "(" cat timer cat "_end - " cat timer cat "_start).count() << \" ms\" << std::endl;");
end procedure;



SetOptimalNTTDomain(: file := INIT);
PrintFile(TERMINATE, "std::cout << std::endl;");

EncryptPlaintextToCiphertext("Plaintext{ \"0\" }", "ZERO_CIPHERTEXT_LOW", false);
EncryptPlaintextToCiphertext("Plaintext{ \"0\" }", "ZERO_CIPHERTEXT_HIGH", true);
PrintFile(INIT, "bootstrapper.multiply_plain_inplace(*ZERO_CIPHERTEXT_LOW, Plaintext{ \"0\" }, 0);");
PrintFile(INIT, "bootstrapper.multiply_plain_inplace(*ZERO_CIPHERTEXT_HIGH, Plaintext{ \"0\" }, 1);");

DeleteCiphertext("ZERO_CIPHERTEXT_HIGH");