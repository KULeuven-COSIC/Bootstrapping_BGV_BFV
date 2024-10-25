#pragma once
#include "seal/evaluator.h"

class ExtendedEvaluator :
    public seal::Evaluator
{
private:
    seal::SEALContext extended_context_;    // Copied field because it is private in base class

    void gbfv_orig_multiply(seal::Ciphertext& encrypted1, const seal::Ciphertext& encrypted2, std::size_t exponent,
        std::uint64_t coefficient, bool twice, seal::MemoryPoolHandle pool) const;

    void gbfv_orig_square(seal::Ciphertext& encrypted, std::size_t exponent, std::uint64_t coefficient, bool twice,
        seal::MemoryPoolHandle pool) const;

    void switch_key_inplace_copy(           // Copied method because it is private in base class
        seal::Ciphertext& encrypted, seal::util::ConstRNSIter target_iter, const seal::KSwitchKeys& kswitch_keys,
        std::size_t kswitch_keys_index, seal::MemoryPoolHandle pool) const;

public:
    ExtendedEvaluator(const seal::SEALContext& context);

    void gbfv_multiply_inplace(
        seal::Ciphertext& encrypted1, const seal::Ciphertext& encrypted2, std::size_t exponent, std::uint64_t coefficient,
        bool twice, seal::MemoryPoolHandle pool = seal::MemoryManager::GetPool()) const;
    
    inline void gbfv_multiply(
        const seal::Ciphertext& encrypted1, const seal::Ciphertext& encrypted2, std::size_t exponent, std::uint64_t coefficient,
        bool twice, seal::Ciphertext& destination, seal::MemoryPoolHandle pool = seal::MemoryManager::GetPool()) const
    {
        if (&encrypted2 == &destination)
        {
            gbfv_multiply_inplace(destination, encrypted1, exponent, coefficient, twice, std::move(pool));
        }
        else
        {
            destination = encrypted1;
            gbfv_multiply_inplace(destination, encrypted2, exponent, coefficient, twice, std::move(pool));
        }
    }

    void gbfv_square_inplace(seal::Ciphertext& encrypted, std::size_t exponent, std::uint64_t coefficient, bool twice,
                             seal::MemoryPoolHandle pool = seal::MemoryManager::GetPool()) const;

    inline void gbfv_square(
        const seal::Ciphertext& encrypted, std::size_t exponent, std::uint64_t coefficient, bool twice,
        seal::Ciphertext& destination, seal::MemoryPoolHandle pool = seal::MemoryManager::GetPool()) const
    {
        destination = encrypted;
        gbfv_square_inplace(destination, exponent, coefficient, twice, std::move(pool));
    }

    void switch_sparse_key_inplace(
        seal::Ciphertext& encrypted, const seal::KSwitchKeys& switch_keys,
        seal::MemoryPoolHandle pool = seal::MemoryManager::GetPool()) const;
    
    void add_plain_to_second_poly_inplace(seal::Ciphertext& encrypted, const seal::Plaintext& plain,
                                          seal::MemoryPoolHandle pool) const;
};
