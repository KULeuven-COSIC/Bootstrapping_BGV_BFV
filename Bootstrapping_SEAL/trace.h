#pragma once
#include <iostream>
#include <vector>
#include <assert.h>
#include <fstream>
#include <chrono>
#include "seal/seal.h"
#include "bootstrapping.h"
#include "constants.h"

using namespace seal;
using namespace std;

void run_trace(Bootstrapper& bootstrapper, const BootstrappingKey& bk, Encryptor& encryptor, Decryptor& decryptor,
			   Encryptor& target_encryptor, Decryptor& target_decryptor);
