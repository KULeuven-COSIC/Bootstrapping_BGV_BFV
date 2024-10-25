#include "sparse_key_generator.h"
#include "seal/randomtostd.h"
#include "seal/util/common.h"
#include "seal/util/galois.h"
#include "seal/util/ntt.h"
#include "seal/util/polyarithsmallmod.h"
#include "seal/util/polycore.h"
#include "seal/util/rlwe.h"
#include "seal/util/uintarithsmallmod.h"
#include "seal/util/uintcore.h"
#include <algorithm>

using namespace std;
using namespace seal;
using namespace util;

SparseKeyGenerator::SparseKeyGenerator(const seal::SEALContext& context, std::uint64_t hamming_weight)
    : context_(context)
{
    // Verify parameters
    if (!context_.parameters_set())
    {
        throw invalid_argument("encryption parameters are not set correctly");
    }

    // Generate the sparse secret key
    generate_sparse_sk(hamming_weight);
}

SparseKeyGenerator::SparseKeyGenerator(const SEALContext& context, const SecretKey& secret_key, uint64_t hamming_weight)
    : context_(context)
{
    // Verify parameters
    if (!context_.parameters_set())
    {
        throw invalid_argument("encryption parameters are not set correctly");
    }
    if (!is_valid_for(secret_key, context_))
    {
        throw invalid_argument("secret key is not valid for encryption parameters");
    }

    // Set the secret key
    secret_key_ = secret_key;
    sk_generated_ = true;

    // Generate the sparse secret key
    generate_sparse_sk(hamming_weight);
}

SparseKeyGenerator::SparseKeyGenerator(const SEALContext& context, const SecretKey& secret_key, const SecretKey& other_key)
    : SparseKeyGenerator(context, secret_key, 0)
{
    // Overwrite sparse secret key with the given one
    sparse_secret_key_ = other_key;
}

void SparseKeyGenerator::generate_sparse_sk(uint64_t hamming_weight)
{
    // Extract encryption parameters.
    auto& context_data = *context_.key_context_data();
    auto& parms = context_data.parms();
    auto& coeff_modulus = parms.coeff_modulus();
    size_t coeff_count = parms.poly_modulus_degree();
    size_t coeff_modulus_size = coeff_modulus.size();

    // Initialize sparse secret key.
    sparse_secret_key_ = SecretKey();
    sparse_secret_key_.data().resize(mul_safe(coeff_count, coeff_modulus_size));

    // Generate sparse secret key
    RNSIter sparse_secret_key(sparse_secret_key_.data().data(), coeff_count);
    if (hamming_weight)
        sample_poly_hamming(parms.random_generator()->create(), parms, sparse_secret_key, hamming_weight);
    else
        sample_poly_ternary(parms.random_generator()->create(), parms, sparse_secret_key);

    // Transform the sparse secret s into NTT representation.
    auto ntt_tables = context_data.small_ntt_tables();
    ntt_negacyclic_harvey(sparse_secret_key, coeff_modulus_size, ntt_tables);

    // Set the parms_id for sparse secret key
    sparse_secret_key_.parms_id() = context_data.parms_id();
}

KSwitchKeys SparseKeyGenerator::create_encapsulation_keys(bool save_seed)
{
    // Check to see if secret key has been generated
    if (!sk_generated_)
    {
        throw logic_error("cannot generate encapsulation keys for unspecified secret key");
    }

    // Extract encryption parameters.
    auto& context_data = *context_.key_context_data();
    auto& parms = context_data.parms();
    size_t coeff_count = parms.poly_modulus_degree();
    size_t coeff_modulus_size = parms.coeff_modulus().size();

    // Size check
    if (!product_fits_in(coeff_count, coeff_modulus_size))
    {
        throw logic_error("invalid parameters");
    }

    // Create the KSwitchKeys object to return (only one key is required)
    KSwitchKeys kswitch_keys;
    kswitch_keys.data().resize(1);

    // Create switching key.
    RNSIter secret_key(secret_key_.data().data(), coeff_count);
    generate_one_kswitch_key(secret_key, kswitch_keys.data()[0], save_seed);

    // Set the parms_id
    kswitch_keys.parms_id() = context_data.parms_id();

    return kswitch_keys;
}

const SecretKey& SparseKeyGenerator::sparse_key() const
{
    return sparse_secret_key_;
}

// Note: insecure implementation but suffices for simulation purposes
// Secure implementation should either increase the noise or decrease the modulus to decompensate for lower Hamming weight
void SparseKeyGenerator::generate_one_kswitch_key(ConstRNSIter new_key, vector<PublicKey>& destination, bool save_seed)
{
    if (!context_.using_keyswitching())
    {
        throw logic_error("keyswitching is not supported by the context");
    }

    size_t coeff_count = context_.key_context_data()->parms().poly_modulus_degree();
    size_t decomp_mod_count = context_.first_context_data()->parms().coeff_modulus().size();
    auto& key_context_data = *context_.key_context_data();
    auto& key_parms = key_context_data.parms();
    auto& key_modulus = key_parms.coeff_modulus();

    // Size check
    if (!product_fits_in(coeff_count, decomp_mod_count))
    {
        throw logic_error("invalid parameters");
    }

    // KSwitchKeys data allocated from pool given by MemoryManager::GetPool.
    destination.resize(decomp_mod_count);

    SEAL_ITERATE(iter(new_key, key_modulus, destination, size_t(0)), decomp_mod_count, [&](auto I) {
        SEAL_ALLOCATE_GET_COEFF_ITER(temp, coeff_count, pool_);
        encrypt_zero_symmetric(     // Encryption of new key under sparse key
            sparse_secret_key_, context_, key_context_data.parms_id(), true, save_seed, get<2>(I).data());
        uint64_t factor = barrett_reduce_64(key_modulus.back().value(), get<1>(I));
        multiply_poly_scalar_coeffmod(get<0>(I), coeff_count, factor, get<1>(I), temp);

        // We use the SeqIter at get<3>(I) to find the i-th RNS factor of the first destination polynomial.
        CoeffIter destination_iter = (*iter(get<2>(I).data()))[get<3>(I)];
        add_poly_coeffmod(destination_iter, temp, coeff_count, get<1>(I), destination_iter);
        });
}

void SparseKeyGenerator::sample_poly_hamming(
    shared_ptr<UniformRandomGenerator> prng, const EncryptionParameters& parms, uint64_t* destination, uint64_t hamming_weight)
{
    auto& coeff_modulus = parms.coeff_modulus();
    size_t coeff_count = parms.poly_modulus_degree();
    size_t coeff_modulus_size = coeff_modulus.size();

    if (hamming_weight > coeff_count)
    {
        throw invalid_argument("hamming weight is too large");
    }

    RandomToStandardAdapter engine(prng);
    uniform_int_distribution<uint64_t> dist(0, 1);
    uniform_int_distribution<uint64_t> dist_pos(0, coeff_count - 1);
    bool* pos = new bool[coeff_count];
    for (uint64_t iii = 0; iii < coeff_count; iii++)
        pos[iii] = false;
    while (hamming_weight != 0)
    {
        uint64_t rand_pos = dist_pos(engine);
        if (!pos[rand_pos])
        {
            pos[rand_pos] = true;
            hamming_weight--;
        }
    }

    uint64_t iteration = 0;
    SEAL_ITERATE(iter(destination), coeff_count, [&](auto& I) {
        uint64_t rand = pos[iteration++] ? (2 * dist(engine)) : 1;
        uint64_t flag = static_cast<uint64_t>(-static_cast<int64_t>(rand == 0));
        SEAL_ITERATE(
            iter(StrideIter<uint64_t*>(&I, coeff_count), coeff_modulus), coeff_modulus_size,
            [&](auto J) { *get<0>(J) = rand + (flag & get<1>(J).value()) - 1; });
        });

    delete[] pos;
}
