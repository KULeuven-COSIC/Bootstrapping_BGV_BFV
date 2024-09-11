#include <fstream>
#include "bootstrapping.h"
#include "constants.h"
#include "seal/util/scalingvariant.h"
#include "seal/util/polyarithsmallmod.h"

using namespace seal;

void Bootstrapper::homomorphic_noisy_decrypt(const Ciphertext& ciphertext, const BootstrappingKey& bk, Ciphertext& destination, MemoryPoolHandle pool DEBUG_PARAMS) const
{
	// ciphertext is validated in convert_ciphertext_plain()
	if (!bk.is_valid_for(context_chain.target_context())) {
		throw std::invalid_argument("Invalid bootstrapping key");
	}
	seal::Plaintext ciphertext_as_plaintext[2];
	context_chain.convert_ciphertext_plain(ciphertext, ciphertext_as_plaintext, pool);
	bootstrapping_evaluator().multiply_plain(bk.encrypted_sk, ciphertext_as_plaintext[1], destination, pool);
	bootstrapping_evaluator().add_plain_inplace(destination, ciphertext_as_plaintext[0]);
}

Bootstrapper::Bootstrapper(const seal::SEALContext& bootstrapped_context, size_t exponent, MemoryPoolHandle pool)
	: context_chain(bootstrapped_context, exponent, pool), pool(pool)
{
}

void Bootstrapper::create_bootstrapping_key(const seal::SecretKey& sk, BootstrappingKey& bk) const
{
	Plaintext sk_plain(MemoryManager::GetPool(mm_prof_opt::mm_force_new, true));
	context_chain.convert_sk_plain(sk, sk_plain);

	SecretKey bootstrapping_sk;
	context_chain.convert_sk(sk, bootstrapping_sk);

	KeyGenerator keygen(context_chain.target_context(), bootstrapping_sk);
	PublicKey pk;
	keygen.create_public_key(pk);

	Encryptor enc(context_chain.target_context(), pk);
	seal::Ciphertext enc_sk;
	enc.encrypt(sk_plain, enc_sk, pool);

	std::cout << "creating " << global_galois_elements.size() << " galois keys" << std::endl;

	GaloisKeys gk;
	keygen.create_galois_keys(global_galois_elements, gk);

	RelinKeys rk;
	keygen.create_relin_keys(rk);

	bk.encrypted_sk = std::move(enc_sk);
	bk.gk = std::move(gk);
	bk.rk = std::move(rk);

	context_chain.convert_kswitchkey(bk.gk, bk.base_gk, 0);
	context_chain.convert_kswitchkey(bk.rk, bk.base_rk, 0);
}

bool BootstrappingKey::is_valid_for(const seal::SEALContext& context) const
{
	return is_metadata_valid_for(gk, context) && is_metadata_valid_for(rk, context) && is_metadata_valid_for(encrypted_sk, context) && is_buffer_valid(gk) && is_buffer_valid(rk) && is_buffer_valid(encrypted_sk);
}

const seal::Evaluator& Bootstrapper::get_evaluator(bool high_level) const
{
	if (high_level)
		return bootstrapping_evaluator();
	else
		return context_chain.get_evaluator(0);
}

const seal::GaloisKeys& Bootstrapper::get_galois_keys(const BootstrappingKey& bk, bool high_level)
{
	if (high_level)
		return bk.galois_keys();
	else
		return bk.base_galois_keys();
}

const seal::RelinKeys& Bootstrapper::get_relin_keys(const BootstrappingKey& bk, bool high_level)
{
	if (high_level)
		return bk.relin_keys();
	else
		return bk.base_relin_keys();
}

void Bootstrapper::apply_galois(seal::Ciphertext& ciphertext, const BootstrappingKey& bk, seal::Ciphertext& destination, uint32_t galois_elt, bool high_level) const
{
	try
	{
		transform_from_ntt_inplace(ciphertext, high_level);
		get_evaluator(high_level).apply_galois(ciphertext, galois_elt, get_galois_keys(bk, high_level), destination);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::apply_galois_inplace(seal::Ciphertext& ciphertext, const BootstrappingKey& bk, uint32_t galois_elt, bool high_level) const
{
	try
	{
		transform_from_ntt_inplace(ciphertext, high_level);
		get_evaluator(high_level).apply_galois_inplace(ciphertext, galois_elt, get_galois_keys(bk, high_level));
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::add(seal::Ciphertext& ciphertext1, seal::Ciphertext& ciphertext2, seal::Ciphertext& destination, bool high_level) const
{
	try
	{
		ciphertexts_to_optimal_domain_inplace(ciphertext1, ciphertext2, high_level);
		get_evaluator(high_level).add(ciphertext1, ciphertext2, destination);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::add_inplace(seal::Ciphertext& ciphertext1, seal::Ciphertext& ciphertext2, bool high_level) const
{
	try
	{
		ciphertexts_to_optimal_domain_inplace(ciphertext1, ciphertext2, high_level);
		get_evaluator(high_level).add_inplace(ciphertext1, ciphertext2);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::add_plain(seal::Ciphertext& ciphertext, const seal::Plaintext& plaintext, seal::Ciphertext& destination, bool high_level) const
{
	try
	{
		transform_from_ntt_inplace(ciphertext, high_level);
		get_evaluator(high_level).add_plain(ciphertext, plaintext, destination);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::add_plain_inplace(seal::Ciphertext& ciphertext, const seal::Plaintext& plaintext, bool high_level) const
{
	try
	{
		transform_from_ntt_inplace(ciphertext, high_level);
		get_evaluator(high_level).add_plain_inplace(ciphertext, plaintext);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::sub(seal::Ciphertext& ciphertext1, seal::Ciphertext& ciphertext2, seal::Ciphertext& destination, bool high_level) const
{
	try
	{
		ciphertexts_to_optimal_domain_inplace(ciphertext1, ciphertext2, high_level);
		get_evaluator(high_level).sub(ciphertext1, ciphertext2, destination);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::sub_inplace(seal::Ciphertext& ciphertext1, seal::Ciphertext& ciphertext2, bool high_level) const
{
	try
	{
		ciphertexts_to_optimal_domain_inplace(ciphertext1, ciphertext2, high_level);
		get_evaluator(high_level).sub_inplace(ciphertext1, ciphertext2);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::sub_plain(seal::Ciphertext& ciphertext, const seal::Plaintext& plaintext, seal::Ciphertext& destination, bool high_level) const
{
	try
	{
		transform_from_ntt_inplace(ciphertext, high_level);
		get_evaluator(high_level).sub_plain(ciphertext, plaintext, destination);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::sub_plain_inplace(seal::Ciphertext& ciphertext, const seal::Plaintext& plaintext, bool high_level) const
{
	try
	{
		transform_from_ntt_inplace(ciphertext, high_level);
		get_evaluator(high_level).sub_plain_inplace(ciphertext, plaintext);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::multiply(seal::Ciphertext& ciphertext1, seal::Ciphertext& ciphertext2, const BootstrappingKey& bk, seal::Ciphertext& destination, bool high_level) const
{
	try
	{
		transform_from_ntt_inplace(ciphertext1, high_level);
		transform_from_ntt_inplace(ciphertext2, high_level);
		get_evaluator(high_level).multiply(ciphertext1, ciphertext2, destination);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
	try
	{
		get_evaluator(high_level).relinearize_inplace(destination, get_relin_keys(bk, high_level));
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::multiply_inplace(seal::Ciphertext& ciphertext1, seal::Ciphertext& ciphertext2, const BootstrappingKey& bk, bool high_level) const
{
	try
	{
		transform_from_ntt_inplace(ciphertext1, high_level);
		transform_from_ntt_inplace(ciphertext2, high_level);
		get_evaluator(high_level).multiply_inplace(ciphertext1, ciphertext2);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
	try
	{
		get_evaluator(high_level).relinearize_inplace(ciphertext1, get_relin_keys(bk, high_level));
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::multiplyNR(seal::Ciphertext& ciphertext1, seal::Ciphertext& ciphertext2, seal::Ciphertext& destination, bool high_level) const
{
	try
	{
		transform_from_ntt_inplace(ciphertext1, high_level);
		transform_from_ntt_inplace(ciphertext2, high_level);
		get_evaluator(high_level).multiply(ciphertext1, ciphertext2, destination);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::multiplyNR_inplace(seal::Ciphertext& ciphertext1, seal::Ciphertext& ciphertext2, bool high_level) const
{
	try
	{
		transform_from_ntt_inplace(ciphertext1, high_level);
		transform_from_ntt_inplace(ciphertext2, high_level);
		get_evaluator(high_level).multiply_inplace(ciphertext1, ciphertext2);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::relinearize(seal::Ciphertext& ciphertext, const BootstrappingKey& bk, seal::Ciphertext& destination, bool high_level) const
{
	try
	{
		transform_from_ntt_inplace(ciphertext, high_level);
		get_evaluator(high_level).relinearize(ciphertext, get_relin_keys(bk, high_level), destination);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::relinearize_inplace(seal::Ciphertext& ciphertext, const BootstrappingKey& bk, bool high_level) const
{
	try
	{
		transform_from_ntt_inplace(ciphertext, high_level);
		get_evaluator(high_level).relinearize_inplace(ciphertext, get_relin_keys(bk, high_level));
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::multiply_plain(seal::Ciphertext& ciphertext, const seal::Plaintext& plaintext, seal::Ciphertext& destination, bool high_level) const
{
	try
	{
		if (plaintext.is_ntt_form())
			transform_to_ntt_inplace(ciphertext, high_level);
		else
			transform_from_ntt_inplace(ciphertext, high_level);
		get_evaluator(high_level).multiply_plain(ciphertext, plaintext, destination);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::multiply_plain_inplace(seal::Ciphertext& ciphertext, const seal::Plaintext& plaintext, bool high_level) const
{
	try
	{
		if (plaintext.is_ntt_form())
			transform_to_ntt_inplace(ciphertext, high_level);
		else
			transform_from_ntt_inplace(ciphertext, high_level);
		get_evaluator(high_level).multiply_plain_inplace(ciphertext, plaintext);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::square(seal::Ciphertext& ciphertext, const BootstrappingKey& bk, seal::Ciphertext& destination, bool high_level) const
{
	try
	{
		transform_from_ntt_inplace(ciphertext, high_level);
		get_evaluator(high_level).square(ciphertext, destination);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
	try
	{
		get_evaluator(high_level).relinearize_inplace(destination, get_relin_keys(bk, high_level));
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::square_inplace(seal::Ciphertext& ciphertext, const BootstrappingKey& bk, bool high_level) const
{
	try
	{
		transform_from_ntt_inplace(ciphertext, high_level);
		get_evaluator(high_level).square_inplace(ciphertext);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
	try
	{
		get_evaluator(high_level).relinearize_inplace(ciphertext, get_relin_keys(bk, high_level));
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::squareNR(seal::Ciphertext& ciphertext, seal::Ciphertext& destination, bool high_level) const
{
	try
	{
		transform_from_ntt_inplace(ciphertext, high_level);
		get_evaluator(high_level).square(ciphertext, destination);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::squareNR_inplace(seal::Ciphertext& ciphertext, bool high_level) const
{
	try
	{
		transform_from_ntt_inplace(ciphertext, high_level);
		get_evaluator(high_level).square_inplace(ciphertext);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::negate_inplace(seal::Ciphertext& ciphertext, bool high_level) const
{
	try
	{
		get_evaluator(high_level).negate_inplace(ciphertext);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::transform_to_ntt(const seal::Ciphertext& ciphertext, seal::Ciphertext& destination, bool high_level) const
{
	try
	{
		if (ciphertext.is_ntt_form())
			destination = ciphertext;
		else
			get_evaluator(high_level).transform_to_ntt(ciphertext, destination);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::transform_to_ntt(const seal::Plaintext& plaintext, const seal::parms_id_type& parms_id, seal::Plaintext& destination, bool high_level) const
{
	try
	{
		if (plaintext.is_ntt_form())
			destination = plaintext;
		else
			get_evaluator(high_level).transform_to_ntt(plaintext, parms_id, destination);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::transform_to_ntt_inplace(seal::Ciphertext& ciphertext, bool high_level) const
{
	try
	{
		if (!ciphertext.is_ntt_form())
			get_evaluator(high_level).transform_to_ntt_inplace(ciphertext);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::transform_to_ntt_inplace(seal::Plaintext& plaintext, const seal::parms_id_type& parms_id, bool high_level) const
{
	try
	{
		if (!plaintext.is_ntt_form())
			get_evaluator(high_level).transform_to_ntt_inplace(plaintext, parms_id);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::transform_from_ntt(const seal::Ciphertext& ciphertext, seal::Ciphertext& destination, bool high_level) const
{
	try
	{
		if (ciphertext.is_ntt_form())
			get_evaluator(high_level).transform_from_ntt(ciphertext, destination);
		else
			destination = ciphertext;
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::transform_from_ntt_inplace(seal::Ciphertext& ciphertext, bool high_level) const
{
	try
	{
		if (ciphertext.is_ntt_form())
			get_evaluator(high_level).transform_from_ntt_inplace(ciphertext);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::homomorphic_noisy_decrypt(Ciphertext& ciphertext, const BootstrappingKey& bk, Ciphertext& destination) const
{
	try
	{
		transform_from_ntt_inplace(ciphertext, 0);
		homomorphic_noisy_decrypt(ciphertext, bk, destination, MemoryManager::GetPool() DEBUG_PASS(sk));
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::high_to_low_level_inplace(seal::Ciphertext& ciphertext) const
{
	try
	{
		transform_from_ntt_inplace(ciphertext, 1);
		context_chain.divide_exact_switch_inplace(ciphertext);
	}
	catch (std::logic_error excp)
	{
		std::cout << excp.what() << std::endl;
	}
}

void Bootstrapper::set_optimal_coefficient_domain()
{
	is_ntt_optimal_domain = 0;
}

void Bootstrapper::set_optimal_ntt_domain()
{
	is_ntt_optimal_domain = 1;
}

void Bootstrapper::ciphertexts_to_optimal_domain_inplace(seal::Ciphertext& ciphertext1, seal::Ciphertext& ciphertext2, bool high_level) const
{
	if (is_ntt_optimal_domain)
	{
		transform_to_ntt_inplace(ciphertext1, high_level);
		transform_to_ntt_inplace(ciphertext2, high_level);
	}
	else
	{
		transform_from_ntt_inplace(ciphertext1, high_level);
		transform_from_ntt_inplace(ciphertext2, high_level);
	}
}

void Bootstrapper::read_plaintext_from_file(seal::Plaintext& plaintext, const std::string& hash)
{
	std::ifstream file("Files/" + hash);
	std::string line;
	std::getline(file, line);
	file.close();
	plaintext = line;
}
