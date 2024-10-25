#include "trace.h"

int main()
{
	// set up context
	EncryptionParameters parms(scheme_type::bfv);
	size_t ring_dimension = (size_t)1 << (global_log2N - 1);
	parms.set_poly_modulus_degree(ring_dimension);
	parms.set_coeff_modulus(CoeffModulus::Create(ring_dimension, { 60, 60, 60, 60, 60, 60, 60 }));
	parms.set_plain_modulus(global_prime_plaintext_modulus);
	SEALContext context(parms, false, seal::sec_level_type::none);
	std::cout << "Q bit count is " << context.key_context_data()->total_coeff_modulus_bit_count() << std::endl;

	// set up keys
	SparseKeyGenerator keygen_sparse(context, 256);			// Hamming weight zero means ternary uniform distribution
	SecretKey sk = keygen_sparse.sparse_key();
	KeyGenerator keygen(context, sk);
	PublicKey pk;
	keygen.create_public_key(pk);

	Encryptor encryptor(context, pk);
	Decryptor decryptor(context, sk);

	/***
	// create example plaintexts
	Plaintext x_plain{ "1x^1" }, ptxt_mul_high{ "5x^7 + 2x^6" }, ptxt_mul_low{ "1x^7" };

	Ciphertext x_enc, result;
	encryptor.encrypt(x_plain, x_enc);
	std::cout << "encrypted message" << std::endl;
	std::cout << "noise budget is " << decryptor.invariant_noise_budget(x_enc) << " bits" << std::endl;
	***/

	std::cout << "setup context" << std::endl;

	// plaintext space during bootstrapping is fixed to p^2
	Bootstrapper bootstrapper(context, 2);

	std::cout << "initialized bootstrapper" << std::endl;

	BootstrappingKey bk;
	bootstrapper.create_bootstrapping_key(sk, bk, 32);		// Hamming weight zero means no sparse secret encapsulation

	std::cout << "created bootstrapping key" << std::endl << std::endl;

	/***
	// some operations before inner product
	bootstrapper.apply_galois_inplace(x_enc, bk, 3, 0);
	bootstrapper.square_inplace(x_enc, bk, 0);

	bootstrapper.homomorphic_noisy_decrypt(x_enc, bk, result);

	// some operations between inner product and division by p
	bootstrapper.apply_galois_inplace(result, bk, 3, 1);
	bootstrapper.transform_to_ntt_inplace(ptxt_mul_high, result.parms_id(), 1);
	bootstrapper.multiply_plain_inplace(result, ptxt_mul_high, 1);
	bootstrapper.add_plain_inplace(result, Plaintext{ "10001" }, 1);	// stored in hex
	//bootstrapper.multiply_plain_inplace(result, Plaintext{ "10001" }, 1);
	//bootstrapper.square_inplace(result, bk, 1);

	bootstrapper.high_to_low_level_inplace(result);

	// some operations after division by p
	bootstrapper.apply_galois_inplace(result, bk, 3, 0);
	bootstrapper.transform_to_ntt_inplace(ptxt_mul_low, result.parms_id(), 0);
	bootstrapper.multiply_plain_inplace(result, ptxt_mul_low, 0);
	bootstrapper.transform_from_ntt_inplace(result, 0);
	
	Plaintext result_dec;
	decryptor.decrypt(result, result_dec);
	std::cout << "output: " << result_dec.to_string() << std::endl << "noise budget: " <<
							   decryptor.invariant_noise_budget(result) << std::endl;
	***/

	SecretKey target_sk;
	bootstrapper.context_chain.convert_sk(sk, target_sk);

	KeyGenerator target_keygen(bootstrapper.context_chain.target_context(), target_sk);
	PublicKey target_pk;
	target_keygen.create_public_key(target_pk);

	Encryptor target_encryptor(bootstrapper.context_chain.target_context(), target_pk);
	Decryptor target_decryptor(bootstrapper.context_chain.target_context(), target_sk);

	run_trace(bootstrapper, bk, encryptor, decryptor, target_encryptor, target_decryptor);
	
	return 0;
}
