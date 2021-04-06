#ifndef _REGEVENC_HPP_
#define _REGEVENC_HPP_
/* regevEnc.hpp - a variant of Regev encryption with PVW packing
 * 
 * Copyright (C) 2021, LWE-PVSS
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject
 * to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included
 * in all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
 * OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR
 * OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
 * ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 **/
#include <vector>
#include <array>

#include "algebra.hpp"

namespace REGEVENC {

// Some parameters are hard-wired, others are set at runtime
constexpr int ell=2;     // how many secret keys per party
constexpr int sigma=2;   // keygen noise in [+-(2^{sigma}-1)]
constexpr int skSize=60; // secret key entries in [+-(2^{skSize}-1)]
    // We use skSize=60 for no reason at all, it might as well be drawn
    // from thenoise distribution. It needs to be somewhat small, say
    // less than sqrt(P), to provide elbow-room for the proofs.

// The global key for our Regev encrypiton includes the variour params,
// the CRS k-by-m matrix A over and the ell*enn-by-emm matrix B with enn
// public keys (both over Z_P).
class GlobalKey {
    static ALGEBRA::BigInt Pmod;
    static ALGEBRA::Scalar deltaScalar;  // approx P^{1/ell}
    static ALGEBRA::Scalar initPdelta(); // a function to initialize P and delta
public:
    static const ALGEBRA::BigInt& P() { return Pmod; }
    static const ALGEBRA::Scalar& delta() { return deltaScalar; }

    std::string tag; // a string to tag this public key
    int kay; // dimension of LWE-secret
    int emm; // #-of-columns in the CRS 
    int enn; // # of parties
    int rho; // encryption randomness in [+-(2^{rho}-1)]

    size_t nPks; // number of ell-row public keys that are stored in B
    ALGEBRA::SMatrix A, B; // The matrix M = (A / B)
    unsigned char Ahash[32]; // fingerprint of the CRS A
    unsigned char Bhash[32]; // fingerprint of the key B

    GlobalKey() = delete;
    GlobalKey(const std::string t, int k, int m, int n, int r,
              const ALGEBRA::SMatrix* crs=nullptr); // optional - a pre-selected CRS

    const unsigned char* const crsHash() const {return Ahash;}
    const unsigned char* const keyHash() const {return Bhash;}
    void setKeyHash(); // hash the matrix B

    bool operator==(const GlobalKey& other) const {return tag==other.tag;}
    bool operator!=(const GlobalKey& other) const {return !(*this==other);}

    // The actual implementation of key-generation
    void internalKeyGen(ALGEBRA::SMatrix& sk, ALGEBRA::SMatrix& pk, ALGEBRA::SMatrix& noise) const;

    // generate a new key-pair, returns (sk,pk) and optionally also noise,
    // each an ell-by-something matrix
    std::pair< ALGEBRA::SMatrix, ALGEBRA::SMatrix > genKeys(ALGEBRA::SMatrix* n=nullptr) const {
        std::pair< ALGEBRA::SMatrix, ALGEBRA::SMatrix > ret;
        if (n != nullptr)
            internalKeyGen(ret.first, ret.second, *n);
        else {
            ALGEBRA::SMatrix noise;
            internalKeyGen(ret.first, ret.second, noise);
        }
        return ret;
    }

    // Add the generated pk to the global key and return its index
    size_t addPK(const ALGEBRA::SMatrix& pk);

    // The actual implementation of encryption, ctx1=CRS x r, ctxt2=PK x r
    void internalEncrypt(ALGEBRA::SVector& ctxt1, ALGEBRA::SVector& ctxt2, const ALGEBRA::SVector& ptxt, ALGEBRA::SVector &r) const;

    // Encrypt a vector of plaintext scalars, return ct0,ct1 and optionally
    // also the randomness that was used in encryption
    std::pair<ALGEBRA::SVector,ALGEBRA::SVector> encrypt(const ALGEBRA::SVector& ptxt, ALGEBRA::SVector* r=nullptr) const {
        std::pair<ALGEBRA::SVector,ALGEBRA::SVector> ct;
        if (r != nullptr)
            internalEncrypt(ct.first, ct.second, ptxt, *r);
        else {
            ALGEBRA::SVector randomness;
            internalEncrypt(ct.first, ct.second, ptxt, randomness);
        }
        return ct;
    }

    // The actual implementation of decryption
    void internalDecrypt(ALGEBRA::Scalar& ptxt, ALGEBRA::SVector& noise,
        const ALGEBRA::SMatrix& sk, int idx, const ALGEBRA::SVector& ct1, const ALGEBRA::SVector& ct2) const;

    // Decrypts a ciphertext, returning ptxt and optioanlly the noise.
    // This function gets the idx of this specific secret key in the
    // global key, and it decrypts the relevant part of the ciphertext.
    ALGEBRA::Scalar decrypt(const ALGEBRA::SMatrix& sk, int idx,
                const std::pair<ALGEBRA::SVector,ALGEBRA::SVector>& ctxt, ALGEBRA::SVector* n=nullptr) {
        ALGEBRA::Scalar pt;
        if (n != nullptr)
            internalDecrypt(pt, *n, sk, idx, ctxt.first, ctxt.second);
        else {
            ALGEBRA::SVector noise;
            internalDecrypt(pt, noise, sk, idx, ctxt.first, ctxt.second);
        }
        return pt;
    }
};

// Select a -1/0/1 scalar with Pr[0]=1/2 and Pr[+-1]=1/4
class ZeroOneScalar {
public:
    ALGEBRA::Scalar& randomize(ALGEBRA::Scalar& s) const {
        long x = ALGEBRA::randBitsize(2); // two random bits
        conv(s, (x&1)-(x>>1));   // return their difference
        return s;
    }
    ALGEBRA::Scalar randomize() const { 
        ALGEBRA::Scalar s;
        return randomize(s);
    }
};

// Select a scalar in the range [+-(2^n -1)], n<=251, almost uniformly
// except the probability of zero is twice as large (namely 2^{-n}).
// This implementation is constant time (maybe).
class BoundedSizeScalar {
public:
    int bitSize;
    BoundedSizeScalar() = delete;
    explicit BoundedSizeScalar(int n): bitSize(n) {}

    ALGEBRA::Scalar& randomize(ALGEBRA::Scalar& s) const {
        ALGEBRA::BigInt zzs[2];
        ALGEBRA::randBitsize(zzs[0], bitSize);
        zzs[1] = -zzs[0];
        conv(s, zzs[ALGEBRA::randomBit()]); // convert to a Scalar mod p
        return s;
    }
    ALGEBRA::Scalar randomize() const { 
        ALGEBRA::Scalar s;
        return randomize(s);
    }
};
} // end of namespace REGEVENC
#endif // ifndef _REGEVENC_HPP_