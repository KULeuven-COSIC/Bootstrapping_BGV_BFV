#include "contextchain.h"
#include <assert.h>

using namespace seal;
using namespace util;

void ContextChain::convert_neg_ones(uint64_t* data, size_t len, const Modulus& from, const Modulus& to)
{
	uint64_t from_neg_one = negate_uint_mod(1, from);
	uint64_t to_neg_one = negate_uint_mod(1, to);
	SEAL_ITERATE(data, len, [&from_neg_one, &to_neg_one](auto& I) {
		if (I == from_neg_one) {
			I = to_neg_one;
		}
	});
}

ContextChain::ContextChain(const SEALContext& base_context, size_t e, MemoryPoolHandle pool)
{
	EncryptionParameters parms = base_context.key_context_data()->parms();
	if (!parms.plain_modulus().is_prime()) {
		throw std::invalid_argument("ContextChain only supports base schemes with prime plaintext moduli");
	}

	uint64_t p = parms.plain_modulus().value();
	contexts.push_back(base_context);
	evaluators.emplace_back(std::make_unique<ExtendedEvaluator, const SEALContext&>(contexts.back()));

	for (size_t i = 1; i < e; ++i) {
		EncryptionParameters new_parms = parms;
		new_parms.set_plain_modulus(exponentiate_uint(p, i + 1));
		contexts.emplace_back(new_parms, false, seal::sec_level_type::none);
		evaluators.emplace_back(std::make_unique<ExtendedEvaluator, const SEALContext&>(contexts.back()));
	}
	assert(evaluators.size() == contexts.size());

	Pointer<RNSBase> rns_base = allocate<RNSBase>(pool, base_context.first_context_data()->parms().coeff_modulus(), pool);
	context_switch_rns_tool = allocate<RNSTool>(pool, poly_modulus_degree(), *rns_base, contexts.back().first_context_data()->parms().plain_modulus(), pool);
}

size_t ContextChain::poly_modulus_degree() const
{
	return contexts.begin()->key_context_data()->parms().poly_modulus_degree();
}

const SEALContext& ContextChain::get_context(parms_id_type parm_id) const
{
	size_t index = get_context_index(parm_id);
	return get_context(index);
}

const SEALContext& ContextChain::get_context(size_t i) const
{
	return contexts[i];
}

const ExtendedEvaluator& ContextChain::get_evaluator(parms_id_type parm_id) const
{
	size_t index = get_context_index(parm_id);
	return get_evaluator(index);
}

const ExtendedEvaluator& ContextChain::get_evaluator(size_t i) const
{
	return *evaluators[i];
}

size_t ContextChain::size() const
{
	return contexts.size();
}

size_t ContextChain::get_context_index(parms_id_type parm_id) const
{
	for (size_t i = 0; i < contexts.size(); ++i) {
		if (contexts[i].get_context_data(parm_id) != nullptr) {
			return i;
		}
	}
	throw std::invalid_argument("No matching context found");
}

const SEALContext& ContextChain::base_context() const
{
	return *contexts.begin();
}

const SEALContext& ContextChain::target_context() const
{
	return contexts.back();
}

const ExtendedEvaluator& ContextChain::target_evaluator() const
{
	return get_evaluator(size() - 1);
}

void ContextChain::convert_sk(const SecretKey& source, SecretKey& destination) const
{
	const SEALContext& source_context = get_context(source.parms_id());
	if (!is_metadata_valid_for(source, source_context)) {
		throw std::invalid_argument("Invalid secret key");
	}
	if (!source.data().is_ntt_form()) {
		throw std::invalid_argument("Secret key data must be in NTT form");
	}

	const size_t poly_modulus_degree = this->poly_modulus_degree();
	const SEALContext::ContextData& target_context_data = *target_context().key_context_data();
	const SEALContext::ContextData& base_context_data = *source_context.get_context_data(source.parms_id());

	destination.data().resize(poly_modulus_degree * target_context_data.parms().coeff_modulus().size());
	destination.parms_id() = target_context_data.parms_id();

	const RNSIter destination_iter(destination.data().data(), poly_modulus_degree);
	const ConstRNSIter source_iter(source.data().data(), poly_modulus_degree);

	// since the secret key has coefficients in { -1, 0, 1 }, we only have to consider one
	// rns factor

	set_poly(*source_iter, poly_modulus_degree, 1, *destination_iter);
	const CoeffIter first_rns_factor = *destination_iter;
	const Modulus& first_rns_modulus = *target_context_data.parms().coeff_modulus().begin();

	inverse_ntt_negacyclic_harvey(first_rns_factor, base_context_data.small_ntt_tables()[0]);

	// fix the -1, which are different values modulo different moduli
	convert_neg_ones(first_rns_factor, poly_modulus_degree, *base_context_data.parms().coeff_modulus().begin(), first_rns_modulus);
	SEAL_ITERATE(iter(destination_iter, target_context_data.parms().coeff_modulus()) + 1, target_context_data.parms().coeff_modulus().size() - 1, [&](auto I) {
		set_poly(first_rns_factor, poly_modulus_degree, 1, std::get<0>(I));
		convert_neg_ones(std::get<0>(I), poly_modulus_degree, first_rns_modulus, std::get<1>(I));
	});

	ntt_negacyclic_harvey(destination_iter, target_context_data.parms().coeff_modulus().size(), target_context_data.small_ntt_tables());
}

void ContextChain::convert_sk_plain(const SecretKey& source, Plaintext& destination) const
{
	const SEALContext& source_context = get_context(source.parms_id());
	if (!is_metadata_valid_for(source, source_context)) {
		throw std::invalid_argument("Invalid secret key");
	}
	if (!source.data().is_ntt_form()) {
		throw std::invalid_argument("Secret key data must be in NTT form");
	}

	const size_t poly_modulus_degree = this->poly_modulus_degree();

	// we must undo both NTT and RNS transformations

	const EncryptionParameters& parms = source_context.key_context_data()->parms();
	const size_t coeff_modulus_size = parms.coeff_modulus().size();
	util::ConstNTTTablesIter ntt_tables = iter(source_context.key_context_data()->small_ntt_tables());
	const util::RNSTool& rns_tool = *source_context.key_context_data()->rns_tool();

	destination.parms_id() = parms_id_zero;
	destination.resize(poly_modulus_degree);

	// since the secret key has coefficients in { -1, 0, 1 }, we only have to consider one
	// rns factor

	ConstCoeffIter first_rns_factor = *ConstRNSIter(source.data().data(), poly_modulus_degree);
	set_poly(first_rns_factor, poly_modulus_degree, 1, destination.data());

	CoeffIter result(destination.data());
	inverse_ntt_negacyclic_harvey(result, source_context.key_context_data()->small_ntt_tables()[0]);

	convert_neg_ones(result, poly_modulus_degree, parms.coeff_modulus()[0], target_context().key_context_data()->parms().plain_modulus());
}

void ContextChain::convert_ciphertext_plain(const Ciphertext& source, PtrIter<Plaintext*> destination, MemoryPoolHandle pool) const
{
	const SEALContext& base_context = *contexts.begin();
	if (!is_metadata_valid_for(source, base_context)) {
		throw std::invalid_argument("Invalid ciphertext");
	}
	if (source.size() != 2) {
		throw std::invalid_argument("Can only convert size 2 ciphertexts to plaintexts");
	}
	if (source.is_ntt_form()) {
		throw std::invalid_argument("BFV ciphertexts cannot be in NTT form");
	}

	const size_t poly_modulus_degree = this->poly_modulus_degree();

	SEAL_ITERATE(util::iter(source, destination), 2, [&context_switch_rns_tool = this->context_switch_rns_tool, pool, poly_modulus_degree](auto I) {
		std::get<1>(I).parms_id() = parms_id_zero;
		std::get<1>(I).resize(poly_modulus_degree);

		// Semantic misuse of decrypt_scale_and_round, as we are not decrypting but just want to compute
		// round(q'/q * ciphertext)
		context_switch_rns_tool->decrypt_scale_and_round(std::get<0>(I), std::get<1>(I).data(), pool);
	});
}

void ContextChain::convert_kswitchkey(const GaloisKeys& source, GaloisKeys& destination, size_t target_index) const
{
	size_t source_index = get_context_index(source.parms_id());
	if (!is_metadata_valid_for(source, get_context(source_index))) {
		throw std::invalid_argument("Invalid galois key");
	}
	// since kswitch keys only operate on ciphertext level (do not interact with the message), we do not
	// have to perform any transformations
	destination = source;
	destination.parms_id() = get_context(target_index).key_context_data()->parms_id();
	for (auto& keys : destination.data()) {
		for (PublicKey& pk : keys) {
			pk.parms_id() = get_context(target_index).key_context_data()->parms_id();
		}
	}
}

void ContextChain::convert_kswitchkey(const RelinKeys& source, RelinKeys& destination, size_t target_index) const
{
	size_t source_index = get_context_index(source.parms_id());
	if (!is_metadata_valid_for(source, get_context(source_index))) {
		throw std::invalid_argument("Invalid galois key");
	}
	// since kswitch keys only operate on ciphertext level (do not interact with the message), we do not
	// have to perform any transformations
	destination = source;
	destination.parms_id() = get_context(target_index).key_context_data()->parms_id();
	for (auto& keys : destination.data()) {
		for (PublicKey& pk : keys) {
			pk.parms_id() = get_context(target_index).key_context_data()->parms_id();
		}
	}
}

void ContextChain::divide_exact_switch_inplace(Ciphertext& value, size_t power) const
{
	const size_t context_index = get_context_index(value.parms_id());
	const SEALContext& source_context = contexts[context_index];

	if (!is_metadata_valid_for(value, source_context)) {
		throw std::invalid_argument("Invalid ciphertext");
	}
	if (context_index < power) {
		throw std::logic_error("Cannot divide_exact_switch_inplace() by more contexts than available.");
	}

	const SEALContext& target_context = contexts[context_index - power];

	if (source_context.first_context_data()->parms_id() != value.parms_id()) {
		throw std::logic_error("It is currently not supported to use modulus switching chains within ContextChain");
	}
	if (source_context.first_context_data()->parms().coeff_modulus().size() != target_context.first_context_data()->parms().coeff_modulus().size()) {
		throw std::logic_error("It is currently not implemented to support different q in the context chain");
	}

	// Since we assume that the moduli are the same, we can just use the data as-is
	value.parms_id() = target_context.first_context_data()->parms_id();
}
