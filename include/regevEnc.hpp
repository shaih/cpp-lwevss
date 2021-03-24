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
#include <stdexcept>

#include <NTL/ZZ.h>
#include <NTL/ZZ_p.h>
#include <NTL/vector.h>
#include <NTL/mat_ZZ_p.h>

namespace REGEVENC {

/*******************************************************************/
// NTL compatibility code to decouple the module form the underlying engine.
// The module code relies on Matrix to have NumRows() and NumCols() methods
// and on Vector to have a length() method, and on conv(toType,fromType) to
// convert between types. But otherwise it shouldn't rely on much of NTL
// beyond the compatibility functions below. (Of course it needs all the
// uaual operator +, *, %, etc.)

// in liue of "using X as Y", bring the relevant NTL types to this namespace
typedef NTL::ZZ BigInt;
typedef NTL::ZZ_p Scalar;
typedef NTL::vec_ZZ_p Vector;
typedef NTL::mat_ZZ_p Matrix;
inline void initRandomness(const std::string& st) {
    NTL::SetSeed((unsigned char*)st.data(), st.length());
}
inline Scalar& randomizeScalar(Scalar& s) { NTL::random(s); return s; }
inline Vector& resize(Vector& vec, size_t n) {vec.SetLength(n); return vec;}
inline Matrix& resize(Matrix& mat, size_t n, size_t m) {
    mat.SetDims(n,m); return mat;
}
inline long randBitsize(size_t n) {return NTL::RandomBits_long(n);}
inline BigInt& randBitsize(BigInt& bi, size_t n) {
    NTL::RandomBits(bi, n);
    return bi;
}
inline size_t randomBit() {return randBitsize(1);}
inline BigInt scalar2bigInt(const Scalar& s) {return NTL::conv<NTL::ZZ>(s);}
typedef NTL::RandomStreamPush PRGbackupClass; // backup/restore of PRG state
/*******************************************************************/

// Some parameters are hard-wired, others are set at runtime
constexpr int ell=2;     // how many secret keys per party
constexpr int sigma=2;   // keygen noise in [+-(2^{sigma}-1)]
constexpr int skSize=60; // secret key entries in [+-(2^{skSize}-1)]
    // We use skSize=60 for no reason at all, it might as well be drawn
    // from thenoise distribution. It needs to be somewhat small, say
    // less than sqrt(P), to provide elbow-room for the proofs.

// A class that holds witnesses to be used in proofs
struct RegevWitnesses {
    Vector sk, kgNoise, encRand;
};


// The global key for our Regev encrypiton includes the variour params,
// the CRS k-by-m matrix A over and the ell*enn-by-emm matrix B with enn
// public keys (both over Z_P).
class GlobalKey {
    static BigInt Pmod;
    static Scalar deltaScalar; // approx P^{1/ell}
    static Scalar initPdelta(); // a function to initialize P and delta
    int nPks;     // number of ell-row public keys that are stored in B
public:
    int kay; // dimension of LWE-secret
    int emm; // #-of-columns in the CRS 
    int enn; // # of parties
    int rho; // encryption randomness in [+-(2^{rho}-1)]

    static const BigInt& P() { return Pmod; }
    static const Scalar& delta() { return deltaScalar; }

    std::string tag; // a string to tag this public key
    Matrix A, B;     // The matrix M = (A / B)

    GlobalKey() = delete;
    GlobalKey(const std::string t, int k, int m, int n, int r):
        tag(t),kay(k),emm(m),enn(n),rho(r),nPks(0)
    {
        if (kay<=0 || emm<=0 || enn<=0 || rho<=0) {
            throw std::runtime_error("GlobalKey with invalid parameters");
        }
        resize(A,k,m);
        resize(B,ell*n,m);

        // Fill the CRS with pseudorandom entries, derived from the tag
        PRGbackupClass prgBak; // backup of current randomstate
        initRandomness(t+"CRS");
        for (int i=0; i<A.NumRows(); i++) for (int j=0; j<A.NumCols(); j++) {
            randomizeScalar(A[i][j]);
        }
    }   // prgBak restores the PRG state upon exit

    bool operator==(const GlobalKey& other) const {return tag==other.tag;}
    bool operator!=(const GlobalKey& other) const {return !(*this==other);}

    // The actual implementation of key-generation
    void internalKeyGen(Matrix& sk, Matrix& pk, Matrix& noise) const;

    // generate a new key-pair, returns (sk,pk) and optionally also noise,
    // each an ell-by-something matrix
    std::pair< Matrix, Matrix > genKeys(Matrix* n=nullptr) const {
        std::pair< Matrix, Matrix > ret;
        if (n != nullptr)
            internalKeyGen(ret.first, ret.second, *n);
        else {
            Matrix noise;
            internalKeyGen(ret.first, ret.second, noise);
        }
        return ret;
    }

    // Add the generated pk to the global key and return its index
    int addPK(const Matrix& pk) { // This function is NOT thread-safe
        if (pk.NumRows() != ell || pk.NumCols() != emm) {
            throw std::runtime_error("Public keys must be "+std::to_string(ell)
                +"-by-"+std::to_string(emm)+" matrices");
        }
        int idx = nPks++;
        if (idx >= enn) {
            --nPks;
            throw std::runtime_error("Cannot add more than "
                +std::to_string(enn)+" keys to global public key");
        }

        // copy the ell rows from pk to the global key
        for (int i=0; i<ell; i++) {
            B[idx*ell +i] = pk[i];
        }
        return idx;
    }

    // The actual implementation of encryption, ctx1=CRS x r, ctxt2=PK x r
    void internalEncrypt(Vector& ctxt1, Vector& ctxt2, const Vector& ptxt, Vector &r) const;

    // Encrypt a vector of plaintext scalars, return ct0,ct1 and optionally
    // also the randomness that was used in encryption
    std::pair<Vector,Vector> encrypt(const Vector& ptxt, Vector* r=nullptr) const {
        std::pair<Vector,Vector> ct;
        if (r != nullptr)
            internalEncrypt(ct.first, ct.second, ptxt, *r);
        else {
            Vector randomness;
            internalEncrypt(ct.first, ct.second, ptxt, randomness);
        }
        return ct;
    }

    // The actual implementation of decryption
    void internalDecrypt(Scalar& ptxt, Vector& noise, const Matrix& sk,
                         int idx, const Vector& ct1, const Vector& ct2) const;

    // Decrypts a ciphertext, returning ptxt and optioanlly the noise.
    // This function gets the idx of this specific secret key in the
    // global key, and it decrypts the relevant part of the ciphertext.
    Scalar decrypt(const Matrix& sk, int idx,
                const std::pair<Vector,Vector>& ctxt, Vector* n=nullptr) {
        Scalar pt;
        if (n != nullptr)
            internalDecrypt(pt, *n, sk, idx, ctxt.first, ctxt.second);
        else {
            Vector noise;
            internalDecrypt(pt, noise, sk, idx, ctxt.first, ctxt.second);
        }
        return pt;
    }
};

// Select a -1/0/1 scalar with Pr[0]=1/2 and Pr[+-1]=1/4
class ZeroOneScalar {
public:
    Scalar& randomize(Scalar& s) const {
        long x = randBitsize(2); // two random bits
        conv(s, (x&1)-(x>>1));   // return their difference
        return s;
    }
    Scalar randomize() const { 
        Scalar s;
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

    Scalar& randomize(Scalar& s) const {
#if 1
        BigInt zzs[2];
        randBitsize(zzs[0], bitSize);
        zzs[1] = -zzs[0];
        conv(s, zzs[randomBit()]); // convert to a Scalar mod p
#else
        conv(s,1);
#endif
        return s;
    }
    Scalar randomize() const { 
        Scalar s;
        return randomize(s);
    }
};
} // end of namespace REGEVENC
#endif // ifndef _REGEVENC_HPP_