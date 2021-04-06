/* regevEnc.cpp - a variant of Regev encryption with PVW packing
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
#include <cassert>
#include "regevEnc.hpp"
extern "C" {
    #include <sodium.h>
}
using namespace ALGEBRA;

namespace REGEVENC {

BigInt GlobalKey::Pmod;
Scalar GlobalKey::deltaScalar;
Element GlobalKey::gElement = GlobalKey::initPdeltaG(); // force to run initPdeltaG

Element GlobalKey::initPdeltaG() { // Implementation is NTL-specific
    // Initizlie the NTL global modulus to 2^{252} + 27742...493
    GlobalKey::Pmod = (NTL::conv<NTL::ZZ>(1L)<<252)
                    + NTL::conv<NTL::ZZ>("27742317777372353535851937790883648493");
    NTL::ZZ_p::init(GlobalKey::Pmod);
    NTL::ZZ_pX Phi_ell_X;
    NTL::SetCoeff(Phi_ell_X, ell); // x^ell +1
    NTL::SetCoeff(Phi_ell_X, 0);
    NTL::ZZ_pE::init(Phi_ell_X);

    // Initialize delta = 2^{126} as a ZZ_p
    GlobalKey::deltaScalar = NTL::to_ZZ_p(NTL::conv<NTL::ZZ>(1L)<<126);

    NTL::ZZ_pX gx;
    Scalar delta2i = NTL::to_ZZ_p(1);
    for (size_t i=0; i<ell; i++) {
        NTL::SetCoeff(gx, i, delta2i);
        delta2i *= GlobalKey::deltaScalar;
    }
    Element g;
    conv(g, gx);
    return g; // will be assigned to GlobalKey::gElement
}

GlobalKey::GlobalKey(const std::string t, int k, int m, int n, int r, const EMatrix* crs):
        tag(t),kay(k),emm(m),enn(n),rho(r),nPks(0) {
    if (kay<=0 || emm<=0 || enn<=0 || rho<=0) {
        throw std::runtime_error("GlobalKey with invalid parameters");
    }
    resize(A,k,m);
    resize(B,n,m);

    // Fill the CRS with pseudorandom entries, derived from the tag,
    // also hash them to get a fingerprint
    std::string t2 = tag+"CRS";
    crypto_generichash_state state;
    crypto_generichash_init(&state, (unsigned char*)t2.data(), t2.size(), sizeof(Ahash));

    PRGbackupClass prgBak; // backup of current randomstate
    initRandomness(t2);
    unsigned char buf[32*ell];
    for (int i=0; i<A.NumRows(); i++) for (int j=0; j<A.NumCols(); j++) {
        if (crs != nullptr) // use provided CRS
            A[i][j] = (*crs)[i][j];
        else
            ALGEBRA::randomizeElement(A[i][j]); // select a new random scalar
        elementBytes(buf, A[i][j], sizeof(buf));
        crypto_generichash_update(&state, buf, sizeof(buf));
    }
    crypto_generichash_final(&state, Ahash, sizeof(Ahash));
}   // prgBak restores the PRG state upon exit

// hash the key matrix B
void GlobalKey::setKeyHash() {
    crypto_generichash_state state;
    crypto_generichash_init(&state, (unsigned char*)"RegevKey", 8, sizeof(Bhash));
    unsigned char buf[32*ell];
    for (int i=0; i<B.NumRows(); i++) for (int j=0; j<B.NumCols(); j++) {
        elementBytes(buf, B[i][j], sizeof(buf));
        crypto_generichash_update(&state, buf, sizeof(buf));
    }
    crypto_generichash_final(&state, Bhash, sizeof(Bhash));
}

// Add the generated pk to the global key and return its index
size_t GlobalKey::addPK(const EVector& pk) { // This function is NOT thread-safe
    if (pk.length() != emm) {
        throw std::runtime_error("Public keys must be "+std::to_string(emm)+"-vectors");
    }
    size_t idx = nPks++;
    if (idx >= enn) {
        --nPks;
        throw std::runtime_error("Cannot add more than "
            +std::to_string(enn)+" keys to global public key");
    }

    // copy the pk to the global key
    B[idx] = pk;
    return idx;
}

void GlobalKey::internalKeyGen(EVector& sk, EVector& pk, EVector& noise) const
{
    // allocate space for the different components
    resize(sk,kay);
    resize(noise,emm);

    // Choose a random secret key, each entry in [+-(2^{skSize} -1)]
    BoundedSizeElement rSK(skSize);
    for (int i=0; i<sk.length(); i++) {
        rSK.randomize(sk[i]);
    }

    // The error vector entries are chosen from [+-3]
    BoundedSizeElement rNoise(sigma);
    for (int i=0; i<noise.length(); i++) {
        rNoise.randomize(noise[i]);
    }
    pk = sk * A + noise;
}

// Encrypt a vector of plaintext scalars
void GlobalKey::internalEncrypt(EVector& ctxt1, EVector& ctxt2,
                                const SVector& ptxt, EVector& arr) const{
    if (A.NumRows() != kay || A.NumCols() != emm
        || B.NumRows() != enn || B.NumCols() != emm) { // sanity check
        throw std::runtime_error("mal-formed public key, expected "+std::to_string(kay)
            +"-by-"+std::to_string(emm)+" CRS and "+std::to_string(enn)
            +"-by-"+std::to_string(emm)+" global PK");
    }
    // # plaintext elements must equal # of rows in the global key
    if (ptxt.length() != B.NumRows()) {
        throw std::runtime_error("encrypt size mismatch, "
            + std::to_string(B.NumRows())+" public key rows but asked to encrypt "
            + std::to_string(ptxt.length())+" scalars");
    }

    resize(arr,emm);       // the dimension-m encryption-randomness vector
    BoundedSizeElement rEnc(rho);// entries are signed (rho+1)-bit integers
    for (auto& e: arr) {
        rEnc.randomize(e);
    }

    // Compute an encrypiton of zero as (CRS*arr, PK*arr)
    ctxt1 = A * arr;
    ctxt2 = B * arr;

    // add g * ptxt to the bottom n rows
    for (size_t i=0; i<enn; i++)
        ctxt2[i] += g() * ptxt[i];
}

// Decrypts a ciphertext, returning ptxt and noise. This function gets
// the idx of this specific secret key in the global one, and then it
// decrypts the relevant part of the ciphertext.
void
GlobalKey::internalDecrypt(Scalar& ptxt, Element& noise, const EVector& sk,
                          int idx, const EVector& ct1, const EVector& ct2) const
{
    static const BigInt deltaZZ = scalar2bigInt(delta());

    // sanity checks
    if (sk.length() != kay) {
        throw std::runtime_error("mal-formed secret key, expected a "+
            std::to_string(kay)+"-vector");
    }
    if (ct1.length() != kay || ct2.length() != enn) {
        throw std::runtime_error("mal-formed ciphertext, expected a "+
            std::to_string(kay + enn)+"-vector");
    }
    if (idx < 0 || idx >= enn) {
        throw std::runtime_error("invalid secret-key index "+std::to_string(idx));
    }

    // Set the noisy plaintext as <sk,ct1> - relevantEntryOf(ct2)
    // = sk A r -(<b,r> + x*g) = (sk A -(sk A + e))r -x*g = -<e,r> -x*g
    Element noisyPtxt = innerProduct(sk,ct1) - ct2.at(idx);
    SVector noisyPtVec;
    conv(noisyPtVec, noisyPtxt);

    // Decode the plaintext scalar from the noisy element, which has the
    // form (z0,z1) = -(x,x*Delta) -(e0,e1).  To decode, first compute
    // y = z0*Delta-z1 = e1-e0*Delta (mod P). If |e1 -e0*Delta|<P/2 then
    // y = e1 -e0*Delta over the integers, and if also |e1| <Delta/2 then
    // (y mod Delta)= e1. Then extract x = -((y mod Delta)+z1)/Delta.

    assert(noisyPtVec.length()==2); // only implemented for ell=2, for now

    BigInt tmp = scalar2bigInt(noisyPtVec[0]*delta() -noisyPtVec[1]);
    if (tmp >= Pmod/2)
        tmp -= Pmod;

    // reduce modulo Delta, and map to [+- Delta/2]
    tmp %= deltaZZ;
    if (tmp >= deltaZZ/2)
        tmp -= deltaZZ;
    else if (tmp < -deltaZZ/2)
        tmp +=deltaZZ;

    SVector noiseVec;
    resize(noiseVec, ell);  // allocate space

    conv(noiseVec[1], tmp); // e1
    ptxt = (noiseVec[1]+noisyPtVec[1])/ delta(); // -x=(e1+z1)/Delta

    noiseVec[0] = ptxt-noisyPtVec[0]; // -x -(-x-e0) = e0
    ptxt = -ptxt;                     // x
    conv(noise, noiseVec);
}

} // end of namespace REGEVENC