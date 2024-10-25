HEADERS = bootstrapping.h constants.h contextchain.h trace.h extended_evaluator.h sparse_key_generator.h
SOURCES = bootstrapping.cpp constants.cpp contextchain.cpp trace.cpp seal.cpp extended_evaluator.cpp sparse_key_generator.cpp
SEAL_DIR = /home/rgeelen/libs/seal

bootstrapping_seal:
	g++ -std=c++17 -O3 -w -I$(SEAL_DIR)/include/SEAL-4.1 -L$(SEAL_DIR)/lib $(SOURCES) -lseal-4.1 -o bootstrapping_seal

clean:
	rm -f bootstrapping_seal
	rm -f constants.cpp
	rm -f tmp_trace_1.cpp
	rm -f tmp_trace_2.cpp
	rm -f tmp_trace_3.cpp
	rm -f tmp_trace_4.cpp
	rm -f trace.cpp
	rm -f ops
	rm -f ctxt
	rm -f is_ntt_optimal_domain
	rm -r -f Files
	mkdir Files
	touch Files/.gitignore
