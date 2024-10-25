#pragma once
#include "seal/keygenerator.h"

class SparseKeyGenerator
{
public:
    // Constructor for individual sparse key
    SparseKeyGenerator(const seal::SEALContext& context, std::uint64_t hamming_weight = 0);

    // Constructor for first encapsulation key
    SparseKeyGenerator(const seal::SEALContext& context, const seal::SecretKey& secret_key, std::uint64_t hamming_weight);

    // Constructor for second encapsulation key
    SparseKeyGenerator(const seal::SEALContext& context, const seal::SecretKey& secret_key, const seal::SecretKey& other_key);

    /**
    Returns a const reference to the sparse secret key.
    */
    SEAL_NODISCARD const seal::SecretKey& sparse_key() const;

    inline void create_encapsulation_keys(seal::KSwitchKeys& destination)
    {
        destination = create_encapsulation_keys(false);
    }

private:
    static void sample_poly_hamming(
        std::shared_ptr<seal::UniformRandomGenerator> prng, const seal::EncryptionParameters& parms,
        std::uint64_t* destination, std::uint64_t hamming_weight);

    SparseKeyGenerator(const SparseKeyGenerator& copy) = delete;

    SparseKeyGenerator& operator=(const SparseKeyGenerator& assign) = delete;

    SparseKeyGenerator(SparseKeyGenerator&& source) = delete;

    SparseKeyGenerator& operator=(SparseKeyGenerator&& assign) = delete;

    void generate_sparse_sk(std::uint64_t hamming_weight);

    /**
    Generates one key switching key for a new key.
    */
    void generate_one_kswitch_key(
        seal::util::ConstRNSIter new_key, std::vector<seal::PublicKey>& destination, bool save_seed = false);

    seal::KSwitchKeys create_encapsulation_keys(bool save_seed);

    // We use a fresh memory pool with `clear_on_destruction' enabled.
    seal::MemoryPoolHandle pool_ = seal::MemoryManager::GetPool(seal::mm_prof_opt::mm_force_new, true);

    seal::SEALContext context_;

    seal::SecretKey secret_key_;
    seal::SecretKey sparse_secret_key_;

    bool sk_generated_ = false;
};
