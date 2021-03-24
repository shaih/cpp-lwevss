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
#include "regevEnc.hpp"

namespace REGEVENC {

BigInt GlobalKey::Pmod;
Scalar GlobalKey::deltaScalar = GlobalKey::initPdelta(); // force to run initpDelta
Scalar GlobalKey::initPdelta() { // Implementation is NTL-specific
    // Initizlie the NTL global modulus to 2^{252} + 27742...493
    GlobalKey::Pmod = (NTL::conv<NTL::ZZ>(1L)<<252)
                    + NTL::conv<NTL::ZZ>("27742317777372353535851937790883648493");
    NTL::ZZ_p::init(GlobalKey::Pmod);

    // Initialize delta = 2^{126} as a ZZ_p
    return NTL::to_ZZ_p(NTL::conv<NTL::ZZ>(1L)<<126);
    // will be assigned to GlobalKey::deltaScalar
}

void GlobalKey::internalKeyGen(Matrix& sk, Matrix& noise, Matrix& pk) const
{
    // allocate space for the different components
    resize(sk,ell,kay);
    resize(noise,ell,emm);

    // Choose a random secret key, each entry in [+-(2^{skSize} -1)]
    BoundedSizeScalar rSK(skSize);
    for (int i=0; i<sk.NumRows(); i++) for (int j=0; j<sk.NumCols(); j++) {
        rSK.randomize(sk[i][j]);
    }

    // The error vector entries are chosen from [+-3]
    BoundedSizeScalar rNoise(sigma);
    for (int i=0; i<noise.NumRows(); i++) for (int j=0; j<noise.NumCols(); j++) {
        rNoise.randomize(noise[i][j]);
    }
    pk = sk * A + noise;
}

// Encrypt a vector of plaintext scalars
void GlobalKey::internalEncrypt(Vector& ctxt1, Vector& ctxt2, const Vector& ptxt) const{
    if (A.NumRows() != kay || A.NumCols() != emm
        || B.NumRows() != ell*enn || B.NumCols() != emm) { // sanity check
        throw std::runtime_error("mal-formed public key, expected "+std::to_string(kay)
            +"-by-"+std::to_string(emm)+" CRS and "+std::to_string(ell*enn)
            +"-by-"+std::to_string(emm)+" global PK");
    }
    // # plaintext elements must be ell times # of rows in the global key
    if (ell*ptxt.length() != B.NumRows()) {
        throw std::runtime_error("encrypt size mismatch, "
            + std::to_string(B.NumRows())+" public key rows but asked to encrypt "
            + std::to_string(ptxt.length())+" scalars");
    }

    Vector arr;
    resize(arr,emm);       // the dimension-m encryption-randomness vector
    BoundedSizeScalar rEnc(rho);// entries are signed (rho+1)-bit integers
    for (auto& s: arr) {
        rEnc.randomize(s);
    }

    // Compute an encrypiton of zero as (CRS*arr, PK*arr)
    ctxt1 = A * arr;
    ctxt2 = B * arr;

    // add ptxt \otimes g to the bottom ell*n rows
    int i=0;
    for (auto x: ptxt) {
        ctxt2[i++] += x;
        for (int j=1; j<ell; j++) {
            x *= delta();
            ctxt2[i++] += x;
        }
    }
}

// Decrypts a ciphertext, returning ptxt and noise. This function gets
// the idx of this specific secret key in the global one, and then it
// decrypts the relevant part of the ciphertext.
void
GlobalKey::internalDecrypt(Scalar& ptxt, Vector& noise, const Matrix& sk,
                          int idx, const Vector& ct1, const Vector& ct2) const
{
    static const BigInt deltaZZ = scalar2bigInt(delta());

    // sanity checks
    if (sk.NumRows() != ell || sk.NumCols() != kay) {
        throw std::runtime_error("mal-formed secret key, expected a "+
            std::to_string(ell)+"-by-"+std::to_string(kay)+" matrix");
    }
    if (ct1.length() != kay || ct2.length() != ell*enn) {
        throw std::runtime_error("mal-formed ciphertext, expected a "+
            std::to_string(kay + ell*enn)+"-vector");
    }
    if (idx < 0 || idx >= enn) {
        throw std::runtime_error("invalid secret-key index "+std::to_string(idx));
    }

    // Set the noisy plaintext as SK x ct1 - relevantEntriesOf(ct2)
    // = Sk A r -(B r + x*g) = (SK A -(Sk A + E))r -x*g = -Er -x*g
    Vector noisyPtxt = sk * ct1;
    for (int i=0; i<ell; i++)
        noisyPtxt.at(i) -= ct2.at(i + ell*idx);

    // Decode the plaintext scalar from the noisy vector, which has the
    // form (z0,z1) = -(x,x*Delta) -(e0,e1).  To decode, first compute
    // y = z0*Delta-z1 = e1-e0*Delta (mod P). If |e1 -e0*Delta|<P/2 then
    // y = e1 -e0*Delta over the integers, and if also |e1| <Delta/2 then
    // (y mod Delta)= e1. Then extract x = -((y mod Delta)+z1)/Delta.

    BigInt tmp = scalar2bigInt(noisyPtxt[0]*delta() -noisyPtxt[1]);
    if (tmp >= Pmod/2)
        tmp -= Pmod;

    // reduce modulo Delta, and map to [+- Delta/2]
    tmp %= deltaZZ;
    if (tmp >= deltaZZ/2)
        tmp -= deltaZZ;
    else if (tmp < -deltaZZ/2)
        tmp +=deltaZZ;

    resize(noise, ell);  // allocate space

    conv(noise[1], tmp); // e1
    ptxt = (noise[1]+noisyPtxt[1])/ delta(); // -x=(e1+z1)/Delta

    noise[0] = ptxt-noisyPtxt[0]; // -x -(-x-e0) = e0
    ptxt = -ptxt;                 // x
}

} // end of namespace REGEVENC