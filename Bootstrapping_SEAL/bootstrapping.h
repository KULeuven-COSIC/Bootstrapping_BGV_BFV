#pragma once
#include <string>
#include "seal/seal.h"
#include "contextchain.h"
#include "extended_evaluator.h"
#include "sparse_key_generator.h"

class Bootstrapper;

#define DEBUG_PARAMS
#define DEBUG_PASS(x)
#define DEBUG_DEC_PRINT(x, y)
#define DEBUG_DEC_PRINT_RAW(x, y)
#define DEBUG_LOG_NOISE_BUDGET(x, y)

class BootstrappingKey {
private:
	seal::Ciphertext encrypted_sk;
	seal::GaloisKeys gk;
	seal::RelinKeys rk;
	seal::KSwitchKeys ek1;
	seal::KSwitchKeys ek2;

	seal::GaloisKeys base_gk;
	seal::RelinKeys base_rk;

	uint64_t hamming_weight;

	bool is_valid_for(const seal::SEALContext& context) const;

public:
	BootstrappingKey() = default;
	BootstrappingKey(const BootstrappingKey&) = default;
	BootstrappingKey(BootstrappingKey&&) = default;
	~BootstrappingKey() = default;

	const seal::GaloisKeys& galois_keys() const;
	const seal::RelinKeys& relin_keys() const;

	const seal::GaloisKeys& base_galois_keys() const;
	const seal::RelinKeys& base_relin_keys() const;

	friend Bootstrapper;
};

class Bootstrapper {
private:
	bool is_ntt_optimal_domain = 1;

public:
	ContextChain context_chain;
	seal::MemoryPoolHandle pool;

	const ExtendedEvaluator& bootstrapping_evaluator() const;

private:
	/**
	 * Computes the "noisy decryption" `c0 + c1 * s`
	*/
	void homomorphic_noisy_decrypt(const seal::Ciphertext& ciphertext, const BootstrappingKey& bk, seal::Ciphertext& destination, seal::MemoryPoolHandle pool DEBUG_PARAMS) const;

	const ExtendedEvaluator& get_evaluator(bool high_level) const;

	static const seal::GaloisKeys& get_galois_keys(const BootstrappingKey& bk, bool high_level);

	static const seal::RelinKeys& get_relin_keys(const BootstrappingKey& bk, bool high_level);

public:
	void apply_galois(seal::Ciphertext& ciphertext, const BootstrappingKey& bk, seal::Ciphertext& destination, uint32_t galois_elt, bool high_level) const;

	void apply_galois_inplace(seal::Ciphertext& ciphertext, const BootstrappingKey& bk, uint32_t galois_elt, bool high_level) const;

	void add(seal::Ciphertext& ciphertext1, seal::Ciphertext& ciphertext2, seal::Ciphertext& destination, bool high_level) const;

	void add_inplace(seal::Ciphertext& ciphertext1, seal::Ciphertext& ciphertext2, bool high_level) const;

	void add_plain(seal::Ciphertext& ciphertext, const seal::Plaintext& plaintext, seal::Ciphertext& destination, bool high_level) const;

	void add_plain_inplace(seal::Ciphertext& ciphertext, const seal::Plaintext& plaintext, bool high_level) const;

	void sub(seal::Ciphertext& ciphertext1, seal::Ciphertext& ciphertext2, seal::Ciphertext& destination, bool high_level) const;

	void sub_inplace(seal::Ciphertext& ciphertext1, seal::Ciphertext& ciphertext2, bool high_level) const;

	void sub_plain(seal::Ciphertext& ciphertext, const seal::Plaintext& plaintext, seal::Ciphertext& destination, bool high_level) const;

	void sub_plain_inplace(seal::Ciphertext& ciphertext, const seal::Plaintext& plaintext, bool high_level) const;

	void multiply(seal::Ciphertext& ciphertext1, seal::Ciphertext& ciphertext2, const BootstrappingKey& bk, seal::Ciphertext& destination, bool high_level) const;
	void gbfv_multiply(seal::Ciphertext& ciphertext1, seal::Ciphertext& ciphertext2, const BootstrappingKey& bk, seal::Ciphertext& destination, size_t exponent, uint64_t coefficient, bool high_level) const;

	void multiply_inplace(seal::Ciphertext& ciphertext1, seal::Ciphertext& ciphertext2, const BootstrappingKey& bk, bool high_level) const;
	void gbfv_multiply_inplace(seal::Ciphertext& ciphertext1, seal::Ciphertext& ciphertext2, const BootstrappingKey& bk, size_t exponent, uint64_t coefficient, bool high_level) const;

	void multiplyNR(seal::Ciphertext& ciphertext1, seal::Ciphertext& ciphertext2, seal::Ciphertext& destination, bool high_level) const;
	void gbfv_multiplyNR(seal::Ciphertext& ciphertext1, seal::Ciphertext& ciphertext2, seal::Ciphertext& destination, size_t exponent, uint64_t coefficient, bool high_level) const;

	void multiplyNR_inplace(seal::Ciphertext& ciphertext1, seal::Ciphertext& ciphertext2, bool high_level) const;
	void gbfv_multiplyNR_inplace(seal::Ciphertext& ciphertext1, seal::Ciphertext& ciphertext2, size_t exponent, uint64_t coefficient, bool high_level) const;

	void relinearize(seal::Ciphertext& ciphertext, const BootstrappingKey& bk, seal::Ciphertext& destination, bool high_level) const;

	void relinearize_inplace(seal::Ciphertext& ciphertext, const BootstrappingKey& bk, bool high_level) const;

	void multiply_plain(seal::Ciphertext& ciphertext, const seal::Plaintext& plaintext, seal::Ciphertext& destination, bool high_level) const;
	
	void multiply_plain_inplace(seal::Ciphertext& ciphertext, const seal::Plaintext& plaintext, bool high_level) const;

	void square(seal::Ciphertext& ciphertext, const BootstrappingKey& bk, seal::Ciphertext& destination, bool high_level) const;
	void gbfv_square(seal::Ciphertext& ciphertext, const BootstrappingKey& bk, seal::Ciphertext& destination, size_t exponent, uint64_t coefficient, bool high_level) const;

	void square_inplace(seal::Ciphertext& ciphertext, const BootstrappingKey& bk, bool high_level) const;
	void gbfv_square_inplace(seal::Ciphertext& ciphertext, const BootstrappingKey& bk, size_t exponent, uint64_t coefficient, bool high_level) const;

	void squareNR(seal::Ciphertext& ciphertext, seal::Ciphertext& destination, bool high_level) const;
	void gbfv_squareNR(seal::Ciphertext& ciphertext, seal::Ciphertext& destination, size_t exponent, uint64_t coefficient, bool high_level) const;

	void squareNR_inplace(seal::Ciphertext& ciphertext, bool high_level) const;
	void gbfv_squareNR_inplace(seal::Ciphertext& ciphertext, size_t exponent, uint64_t coefficient, bool high_level) const;

	void negate_inplace(seal::Ciphertext& ciphertext, bool high_level) const;

	void transform_to_ntt(const seal::Ciphertext& ciphertext, seal::Ciphertext& destination, bool high_level) const;
	void transform_to_ntt(const seal::Plaintext& plaintext, const seal::parms_id_type& parms_id, seal::Plaintext& destination, bool high_level) const;

	void transform_to_ntt_inplace(seal::Ciphertext& ciphertext, bool high_level) const;
	void transform_to_ntt_inplace(seal::Plaintext& plaintext, const seal::parms_id_type& parms_id, bool high_level) const;
	
	void transform_from_ntt(const seal::Ciphertext& ciphertext, seal::Ciphertext& destination, bool high_level) const;

	void transform_from_ntt_inplace(seal::Ciphertext& ciphertext, bool high_level) const;

	void homomorphic_noisy_decrypt(Ciphertext& ciphertext, const BootstrappingKey& bk, Ciphertext& destination) const;

	void high_to_low_level_inplace(seal::Ciphertext& ciphertext) const;

	void set_optimal_coefficient_domain();
	void set_optimal_ntt_domain();
	void ciphertexts_to_optimal_domain_inplace(seal::Ciphertext& ciphertext1, seal::Ciphertext& ciphertext2, bool high_level) const;

	static void read_plaintext_from_file(seal::Plaintext& plaintext, const std::string& hash);

public:
	Bootstrapper(const seal::SEALContext& bootstrapped_context, size_t exponent, MemoryPoolHandle pool = MemoryManager::GetPool());
	Bootstrapper(const Bootstrapper&) = default;
	Bootstrapper(Bootstrapper&&) = default;
	~Bootstrapper() = default;

	void create_bootstrapping_key(const seal::SecretKey& sk, BootstrappingKey& bk, uint64_t hamming_weight = 0) const;
};

inline const ExtendedEvaluator& Bootstrapper::bootstrapping_evaluator() const
{
	return context_chain.target_evaluator();
}

inline const seal::GaloisKeys& BootstrappingKey::galois_keys() const
{
	return gk;
}

inline const seal::RelinKeys& BootstrappingKey::relin_keys() const
{
	return rk;
}

inline const seal::GaloisKeys& BootstrappingKey::base_galois_keys() const
{
	return base_gk;
}

inline const seal::RelinKeys& BootstrappingKey::base_relin_keys() const
{
	return base_rk;
}
