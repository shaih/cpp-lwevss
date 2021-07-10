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
#include <cmath>
#include <cassert>
#include "regevEnc.hpp"
#include "utils.hpp"
extern "C" {
    #include <sodium.h>
}
using namespace ALGEBRA;

//#define DEBUGGING

namespace REGEVENC {

BigInt GlobalKey::Pmod;
Scalar GlobalKey::deltaScalar; // Delta = P^{1/ell} as a scalar
BigInt GlobalKey::delta2ellm1; // Delta^{ell-1} as a bigInt
Element GlobalKey::gElement = GlobalKey::initPdeltaG(); // force to run initPdeltaG

Element GlobalKey::initPdeltaG() { // Implementation is NTL-specific
    // Initizlie the NTL global modulus to 2^{252} +27742...493
    GlobalKey::Pmod = (toBigInt(1)<<252)
                    + NTL::conv<NTL::ZZ>("27742317777372353535851937790883648493");
    NTL::ZZ_p::init(GlobalKey::Pmod);

    // Initizlie the NTL global polynomial modulus to F(X) = X^ell +1
    NTL::ZZ_pX Phi_ell_X;
    NTL::SetCoeff(Phi_ell_X, ell); // x^ell +1
    NTL::SetCoeff(Phi_ell_X, 0);
    NTL::ZZ_pE::init(Phi_ell_X);

    // Initialize delta
    BigInt delta = toBigInt(1) << (252/ell);     // approx P^{1/ell}
    conv(GlobalKey::deltaScalar, delta);         // convert to a scalar mod P
    power(GlobalKey::delta2ellm1, delta, ell-1); // Delta^{ell-1}

    // Initialize the element g = (Delta^{ell-1},...,Delta,1)
    NTL::ZZ_pX gx;
    Scalar delta2i;
    conv(delta2i, 1L);
    for (size_t i=0; i<ell; i++) {
        NTL::SetCoeff(gx, i, delta2i);
        delta2i *= GlobalKey::deltaScalar;
    }
    Element g;
    conv(g, gx);
    return g; // will be assigned to GlobalKey::gElement
}

// Find parameters that satisfy the constraints
void KeyParams::setParams() {
  int kk;
  int nn = n*GlobalKey::ell;
  int tt = (nn-1)/2;
  int lognSqrtT = ceil(log2(nn) + log(tt)/2); // log_2(nn*sqrt(tt))
  // Start from a large sigmaEnc, then count down until you find a value that works
  int start = (GlobalKey::pSize*(GlobalKey::ell-1)) / GlobalKey::ell;
  for (sigmaEnc1=start-lognSqrtT-11; sigmaEnc1>0; sigmaEnc1--) {
      kk = ceil(37.5*(GlobalKey::pSize+2-sigmaEnc1));
      k = (kk+GlobalKey::ell-1)/GlobalKey::ell; // ceil(kk/ell)
      kk = GlobalKey::ell * k; // round up to a multiple of ell

      // check if P^{(ell-1)/2} > 2^sigmaEnc1 * 600 n sqrt(n*t)
      int logSqrtK = ceil(log2(kk)/2);
      if (start >= sigmaEnc1+lognSqrtT+10+logSqrtK)
        break;
  }
  auto e2e1gap = 124080L*kk*tt; // 124080*kk*tt
  e2e1gap = ceil(log2(e2e1gap) / 2); // log_2(sqrt(124080*kk*tt))
  sigmaEnc2 = sigmaEnc1 + e2e1gap;
}

GlobalKey::GlobalKey(const std::string tg, const KeyParams &prms, const EMatrix* crs):
        nPks(0),tag(tg),kay(prms.k),enn(prms.n),
        sigmaEnc1(prms.sigmaEnc1),sigmaEnc2(prms.sigmaEnc2)
{
    if (kay<=0 || enn<=0 || sigmaEnc1<=1 || sigmaEnc2<=2) {
        throw std::runtime_error("GlobalKey with invalid parameters");
    }
    tee = ((enn-1)/(2*ell))*ell; // less than n/2, divisible by ell
    assert(tee>0);       // sanity check
    resize(A,kay,kay);
    resize(B,enn,kay);

    // Fill the CRS with pseudorandom entries, derived from the tag,
    // also hash them to get a fingerprint
    std::string t2 = tag+"CRS";
    PRGbackupClass prgBak; // backup of current randomstate
    initRandomness(t2);
    for (int i=0; i<A.NumRows(); i++) for (int j=0; j<A.NumCols(); j++) {
        if (crs != nullptr) // use provided CRS
            A[i][j] = (*crs)[i][j];
        else
            ALGEBRA::randomizeElement(A[i][j]); // select a new random element
    }

    // Compute a hash of the CRS, to be used as its fingerprint
    crypto_generichash_state state;
    crypto_generichash_init(&state, (unsigned char*)t2.data(), t2.size(), sizeof(Ahash));
    unsigned char buf[32*ell];
    for (int i=0; i<A.NumRows(); i++) for (int j=0; j<A.NumCols(); j++) {
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
    if (pk.length() != kay) {
        throw std::runtime_error("Public keys must be "+std::to_string(kay)+"-vectors");
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
    resize(noise,kay);

    assert(rho==2); // sanity check, just in case we ever change that

    // Choose a random secret key, each entry in [+-3], reset until
    // the size is no more than 2*Sqrt(kk)
    {BoundedSizeElement rSK(rho);
    int bound = 4*kay*ell;
    for (int nTrials = 0; ; nTrials++) {
        if (nTrials > 50) {
            throw std::runtime_error("internalKeyGen: too many retrys choosing sk");
        }
        for (int i=0; i<sk.length(); i++) rSK.randomize(sk[i]);
        if (normSquaredBigInt(sk) <= bound)
            break;
    }}

    // The error vector entries are chosen from [+-2^{sigmaEnc1}],
    // reset until the size is no more than 2^{sigmaEnc1}*Sqrt(kk/2)
    BoundedSizeElement rNoise(sigmaEnc1);
    BigInt bound = (BigInt(1)<<(2*sigmaEnc1)) * kay*ell/2;
    for (int nTrials = 0; ; nTrials++) {
        if (nTrials > 50) {
            throw std::runtime_error("internalKeyGen: too many retrys choosing noise");
        }
        for (int i=0; i<noise.length(); i++) rNoise.randomize(noise[i]);
        if (normSquaredBigInt(noise) <= bound)
            break;
    }
    pk = sk * A + noise;
    //printEvec(std::cout<<"keygen noise = ",noise) << std::endl;
}

// Encrypt a vector of plaintext scalars
void GlobalKey::internalEncrypt(EVector& ctxt1, EVector& ctxt2,
                const SVector& ptxt, EVector& arr, EVector& e1, EVector& e2) const {
    if (A.NumRows() != kay || A.NumCols() != kay
        || B.NumRows() != enn || B.NumCols() != kay) { // sanity check
        throw std::runtime_error("mal-formed public key, expected "+std::to_string(kay)
            +"-by-"+std::to_string(kay)+" CRS and "+std::to_string(enn)
            +"-by-"+std::to_string(kay)+" global PK");
    }
    // # plaintext elements must equal # of rows in the global key
    if (ptxt.length() != B.NumRows()) {
        throw std::runtime_error("encrypt size mismatch, "
            + std::to_string(B.NumRows())+" public key rows but asked to encrypt "
            + std::to_string(ptxt.length())+" scalars");
    }

    resize(arr,kay);    // the dimension-m encryption-randomness vector
    // choose the randomness, each entry in [+-3], reset until
    // the size is no more than 2*Sqrt(kk)
    {BoundedSizeElement rSK(rho);
    int bound = 4 * kay*ell;
    for (int nTrials = 0; ; nTrials++) {
        if (nTrials > 50) {
            throw std::runtime_error("internalEncrypt: too many retrys choosing r");
        }
        for (int i=0; i<arr.length(); i++) rSK.randomize(arr[i]);
        if (normSquaredBigInt(arr) <= bound)
            break;
    }}

    // Compute an encrypiton of zero as (CRS*arr, PK*arr)
    ctxt1 = A * arr;
    ctxt2 = B * arr;

    // choose bounded-size noise
    resize(e1, kay);
    // The error vector entries are chosen from [+-2^{sigmaEnc1}],
    // reset until the size is no more than 2^{sigmaEnc1}*Sqrt(kk/2)
    {BoundedSizeElement noise1(sigmaEnc1);
    BigInt bound = (BigInt(1)<<(2*sigmaEnc1)) * kay*ell/2;
    for (int nTrials = 0; ; nTrials++) {
        if (++nTrials > 50)
            throw std::runtime_error("internalEncrypt: too many retrys choosing e1");
        for (size_t i=0; i<kay; i++) noise1.randomize(e1[i]);
        if (normSquaredBigInt(e1) <= bound)
            break;
    }}
    resize(e2, enn);
    BoundedSizeElement noise2(sigmaEnc2);
    BigInt bound = (BigInt(1)<<(2*sigmaEnc2)) * enn*ell/2;
    for (int nTrials = 0; ; nTrials++) {
        if (++nTrials > 50)
            throw std::runtime_error("internalEncrypt: too many retrys choosing e2");
        for (size_t i=0; i<enn; i++) noise2.randomize(e2[i]);
        if (normSquaredBigInt(e2) <= bound)
            break;
    }

    // Add the noise, and also g * ptxt to the bottom n rows
    for (size_t i=0; i<kay; i++)
        ctxt1[i] += e1[i];
    for (size_t i=0; i<enn; i++)
        ctxt2[i] += g()*ptxt[i] + e2[i];
}

// Decrypts a ciphertext, returning ptxt and noise. This function gets
// the idx of this specific secret key in the global one, and then it
// decrypts the relevant part of the ciphertext.
void GlobalKey::internalDecrypt(Scalar& ptxt,Element& noise,const EVector& sk,
                        int idx, const EVector& ct1, const EVector& ct2) const
{
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
    Element noisyPtxt = innerProduct(sk,ct1) - ct2[idx];
 
    // Decode the plaintext scalar from the noisy element, which has the
    // form (z0,z1) = -(x,x*Delta) -(e0,e1).  To decode, first compute
    // y = z0*Delta-z1 = e1-e0*Delta (mod P). If |e1 -e0*Delta|<P/2 then
    // y = e1 -e0*Delta over the integers, and if also |e1| <Delta/2 then
    // (y mod Delta)= e1. Then extract x = -((y mod Delta)+z1)/Delta.
    ptxt = decodePtxt(noisyPtxt, &noise);
}

// Decode the plaintext scalar from the noisy element, which has the
// form (z0,z1) = -(x,x*Delta) -(e0,e1).  To decode, first compute
// y = z0*Delta-z1 = e1-e0*Delta (mod P). If |e1 -e0*Delta|<P/2 then
// y = e1 -e0*Delta over the integers, and if also |e1| <Delta/2 then
// (y mod Delta)= e1. Then extract x = -((y mod Delta)+z1)/Delta.
Scalar GlobalKey::decodePtxt(Element& noisyPtxt, Element* noise) const {
    static const BigInt deltaZZ = scalar2bigInt(delta());
    SVector noisyPtVec;
    conv(noisyPtVec, noisyPtxt);

    BIVector tmpVec;
    resize(tmpVec, ell);
    BigInt& tmp = tmpVec[ell-1];
    for (size_t i=0; i<ell-1; i++) { // tmpVec[i] = e[i+1] - Delta*e[i]
        tmpVec[i] = scalar2bigInt( noisyPtVec[i]*delta() -noisyPtVec[i+1] );
        if (tmpVec[i] > P()/2)       // map to [+- P/2]
            tmpVec[i] -= P();
    }

    // sum_{i=0}^{ell-2} Delta^{ell-2-i}*tmpVec[i] = e[ell-1] -Delta^{ell-1}*e[0]
    tmp = tmpVec[0];
    for (int i=1; i<ell-1; i++) {
        tmp *= deltaZZ;
        tmp += tmpVec[i];
    }

    // reduce modulo Delta^{ell-1} and map to  [+- Delta^{ell-1}/2]
    tmp %= delta2ellMinus1();
    if (tmp >= delta2ellMinus1()/2)
        tmp -= delta2ellMinus1();
    else if (tmp < -delta2ellMinus1()/2)
        tmp += delta2ellMinus1();
    // now tmp = e[ell-1]
    //std::cout << "e[ell-1] = " << tmp << std::endl;

    for (int i=ell-2; i>=0; --i) {
        tmpVec[i] = tmpVec[i+1] -tmpVec[i]; // = Delta*e[i]
        tmpVec[i] /= deltaZZ;               // = e[i]
    }
    SVector noiseVec;
    conv(noiseVec, tmpVec); // convert to scalars mod P

    if (noise != nullptr) conv(*noise, noiseVec);

    return -noisyPtVec[0] -noiseVec[0];
}

} // end of namespace REGEVENC