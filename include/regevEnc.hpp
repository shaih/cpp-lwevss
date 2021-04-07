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
#include <iostream>
#include <vector>
#include <array>

#include "algebra.hpp"

namespace REGEVENC {

// Some parameters are hard-wired, others are set at runtime
constexpr int ell=4;        // redundancy parameter, # dimensions per party
constexpr int sigmaKG=10;  // keygen noise in [+-(2^{sigmaKG}-1)]
constexpr int sigmaEnc1=10; // encryption small noise in [+-(2^{sigmaEnc1}-1)]
constexpr int sigmaEnc2=20; // encryption large noise in [+-(2^{sigmaEnc2}-1)]
constexpr int skSize=2;     // secret key entries in [+-(2^{skSize}-1)]
constexpr int rho=2;        // encryption randomness in [+-(2^{rho}-1)]

// The global key for our Regev encrypiton includes the variour params,
// the CRS k-by-m matrix A over and the ell*enn-by-emm matrix B with enn
// public keys (both over Z_P).
class GlobalKey {
    static ALGEBRA::BigInt Pmod;
    static ALGEBRA::Scalar deltaScalar; // approx P^{1/ell}
    static ALGEBRA::BigInt delta2ellm1; // Delta^{ell-1}
    static ALGEBRA::Element gElement;   // (1,Delta,...,Delta^{ell-1})
    static ALGEBRA::Element initPdeltaG(); // a function to initialize P,delta,g
public:
    static const ALGEBRA::BigInt& P() { return Pmod; }
    static const ALGEBRA::Scalar& delta() { return deltaScalar; }
    static const ALGEBRA::BigInt& delta2ellMinus1() { return delta2ellm1; }
    static const ALGEBRA::Element& g() { return gElement; }

    std::string tag; // a string to tag this public key
    int kay; // dimension of LWE-secret
    int emm; // #-of-columns in the CRS 
    int enn; // # of parties

    size_t nPks; // number of ell-row public keys that are stored in B
    ALGEBRA::EMatrix A, B; // The matrix M = (A / B)
    unsigned char Ahash[32]; // fingerprint of the CRS A
    unsigned char Bhash[32]; // fingerprint of the key B

    GlobalKey() = delete;
    GlobalKey(const std::string t, int k, int m, int n,
              const ALGEBRA::EMatrix* crs=nullptr); // optional - a pre-selected CRS

    const unsigned char* const crsHash() const {return Ahash;}
    const unsigned char* const keyHash() const {return Bhash;}
    void setKeyHash(); // hash the matrix B

    bool operator==(const GlobalKey& other) const {return tag==other.tag;}
    bool operator!=(const GlobalKey& other) const {return !(*this==other);}

    // The actual implementation of key-generation
    void internalKeyGen(ALGEBRA::EVector& sk, ALGEBRA::EVector& pk, ALGEBRA::EVector& noise) const;

    // generate a new key-pair, returns (sk,pk) and optionally also noise,
    // each an ell-by-something matrix
    std::pair< ALGEBRA::EVector, ALGEBRA::EVector > genKeys(ALGEBRA::EVector* n=nullptr) const {
        std::pair< ALGEBRA::EVector, ALGEBRA::EVector > ret;
        if (n != nullptr)
            internalKeyGen(ret.first, ret.second, *n);
        else {
            ALGEBRA::EVector noise;
            internalKeyGen(ret.first, ret.second, noise);
        }
        return ret;
    }

    // Add the generated pk to the global key and return its index
    size_t addPK(const ALGEBRA::EVector& pk);

    // Implementation of encryption, ctx1=CRS x r +e1, ctxt2=PK x r +e2 +g*x
    void internalEncrypt(ALGEBRA::EVector& ctxt1, ALGEBRA::EVector& ctxt2,
        const ALGEBRA::SVector& ptxt, ALGEBRA::EVector& r, ALGEBRA::EVector& e) const;

    // Encrypt a vector of plaintext scalars, return ct0,ct1 and optionally
    // also the randomness and noise that were used in encryption
    std::pair<ALGEBRA::EVector,ALGEBRA::EVector>
    encrypt(const ALGEBRA::SVector& ptxt, ALGEBRA::EVector& r, ALGEBRA::EVector& e) const {
        std::pair<ALGEBRA::EVector,ALGEBRA::EVector> ct;
        internalEncrypt(ct.first, ct.second, ptxt, r, e);
        return ct;
    }
    std::pair<ALGEBRA::EVector,ALGEBRA::EVector>
    encrypt(const ALGEBRA::SVector& ptxt) const {
        ALGEBRA::EVector r, e;
        return encrypt(ptxt, r, e);
    }

    // The actual implementation of decryption
    void internalDecrypt(ALGEBRA::Scalar& ptxt, ALGEBRA::Element& noise,
                const ALGEBRA::EVector& sk, int idx,
                const ALGEBRA::EVector& ct1,const ALGEBRA::EVector& ct2)const;

    // Decrypts a ciphertext, returning ptxt and optioanlly the noise.
    // This function gets the idx of this specific secret key in the
    // global key, and it decrypts the relevant part of the ciphertext.
    ALGEBRA::Scalar decrypt(const ALGEBRA::EVector& sk, int idx,
                const std::pair<ALGEBRA::EVector,ALGEBRA::EVector>& ctxt, ALGEBRA::Element* n=nullptr) {
        ALGEBRA::Scalar pt;
        if (n != nullptr)
            internalDecrypt(pt, *n, sk, idx, ctxt.first, ctxt.second);
        else {
            ALGEBRA::Element noise;
            internalDecrypt(pt, noise, sk, idx, ctxt.first, ctxt.second);
        }
        return pt;
    }
};

// Select a -1/0/1 scalar with Pr[0]=1/2 and Pr[+-1]=1/4
class ZeroOneScalar {
public:
    ALGEBRA::Scalar& randomize(ALGEBRA::Scalar& s) const {
        size_t x = ALGEBRA::randBitsize(2); // two random bits
        conv(s, (x&1)-(x>>1));   // return their difference
        return s;
    }
    ALGEBRA::Scalar randomize() const { 
        ALGEBRA::Scalar s;
        return randomize(s);
    }
};

// Select a -1/0/1 scalar with Pr[0]=1/2 and Pr[+-1]=1/4
class ZeroOneElement {
public:
    ALGEBRA::Element& randomize(ALGEBRA::Element& e) const {
        size_t x = ALGEBRA::randBitsize(ell*2); // 2*ell random bits
        ALGEBRA::SVector v;
        ALGEBRA::resize(v,ell);
        for (size_t i=0; i<ell; i++) {
            conv(v[i], (x&1)-((x>>1)&1)); // -1/0/1 scalar
            x >>= 2;
        }
        ALGEBRA::conv(e,v);
        return e;
    }
    ALGEBRA::Element randomize() const { 
        ALGEBRA::Element e;
        return randomize(e);
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
class BoundedSizeElement {
public:
    int bitSize;
    BoundedSizeElement() = delete;
    explicit BoundedSizeElement(int n): bitSize(n) {}

    ALGEBRA::Element& randomize(ALGEBRA::Element& e) const {
        BoundedSizeScalar bss(bitSize);
        ALGEBRA::SVector v;
        ALGEBRA::resize(v,ell);
        for (size_t i=0; i<ell; i++)
            bss.randomize(v[i]);
        ALGEBRA::conv(e, v); // convert to an element in GF(P^ell)
        return e;
    }
    ALGEBRA::Element randomize() const { 
        ALGEBRA::Element e;
        return randomize(e);
    }
};

} // end of namespace REGEVENC
#endif // ifndef _REGEVENC_HPP_