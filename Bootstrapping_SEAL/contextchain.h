#pragma once
#include "seal/seal.h"
#include "extended_evaluator.h"

using namespace seal;

/**
 * Since SEAL only supports a fixed plaintext modulus per SEALContext,
 * this object manages a list of SEALContexts with plaintext moduli
 * p, p^2, ..., p^e (all of them are necessary during digit extraction)
*/
class ContextChain {
private:
	std::vector<SEALContext> contexts;
	std::vector<std::unique_ptr<ExtendedEvaluator>> evaluators;
	util::Pointer<util::RNSTool> context_switch_rns_tool;

	static void convert_neg_ones(uint64_t* data, size_t len, const Modulus& from, const Modulus& to);

public:
	ContextChain(const SEALContext& base_context, size_t e, MemoryPoolHandle pool);
	ContextChain(const ContextChain&) = delete;
	ContextChain(ContextChain&&) = default;
	~ContextChain() = default;

	size_t poly_modulus_degree() const;
	const SEALContext& get_context(parms_id_type parm_id) const;
	const SEALContext& get_context(size_t i) const;
	const ExtendedEvaluator& get_evaluator(parms_id_type parm_id) const;
	const ExtendedEvaluator& get_evaluator(size_t i) const;
	size_t size() const;
	size_t get_context_index(parms_id_type parm_id) const;

	/**
	 * The base context is the first context in the chain, i.e. the one with plaintext
	 * modulus p
	*/
	const SEALContext& base_context() const;

	/**
	 * The "target context" is the final context in the chain, i.e. the one with plaintext
	 * modulus p^e
	*/
	const SEALContext& target_context() const;
	const ExtendedEvaluator& target_evaluator() const;

	/**
	 * Converts a secret key for one of the contexts to a secret key for the target context
	*/
	void convert_sk(const SecretKey& source, SecretKey& destination) const;

	/**
	 * Converts a secret key for one of the contexts to the plaintext space of the target context
	*/
	void convert_sk_plain(const SecretKey& source, Plaintext& destination) const;

	/**
	 * Converts a ciphertext for the first/base context to the plaintext space of the target context
	*/
	void convert_ciphertext_plain(const Ciphertext& source, util::PtrIter<Plaintext*> destination, MemoryPoolHandle pool) const;

	/**
	 * Converts a key-switch key from one context to another (the source context is derived from source.parms_id())
	*/
	void convert_kswitchkey(const GaloisKeys& source, GaloisKeys& destination, size_t target_index) const;
	
	/**
	 * Converts a key-switch key from one context to another (the source context is derived from source.parms_id())
	*/
	void convert_kswitchkey(const RelinKeys& source, RelinKeys& destination, size_t target_index) const;

	/**
	 * Transforms a ciphertext enrypting a message m to a ciphertext of the one step lower context that encrypts m / p;
	 * Requires that p | m
	 */
	void divide_exact_switch_inplace(Ciphertext& value, size_t power = 1) const;
}; 
