/* regevProofs.cpp - Proofs for Regev encrypiotn
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
#include <cassert>
#include "regevProofs.hpp"

using namespace ALGEBRA;

namespace REGEVENC {
using CRV25519::Point, DLPROOFS::PedersenContext,
    DLPROOFS::MerlinBPctx, DLPROOFS::LinConstraint, DLPROOFS::QuadConstraint;
// NOTE: REGEVENC::Scalar is not the same as CRV25519::Scalar

VerifierData::VerifierData(GlobalKey& g, PedersenContext& p, MerlinRegev& m) {
    gk = &g;
    ped = &p;
    mer = &m;

    // FIXME: compute the nounds from the gk parameters

    B_decNoise = BigInt(1)<<10; // bounds each sub-vector of decryption noise
    B_sk = BigInt(1)<<10;        // bounds the secret-key size
    B_encRnd = BigInt(1)<<10;    // bounds the encryption randomness size
    B_encNoise = BigInt(1)<<10;  // bounds the size of the encryption noise
    B_kGenNoise = BigInt(1)<<10; // bounds the size of the keygen noise
    B_smallness = BigInt(1)<<10;// Used in the approximate smallness protocol

    setIndexes(); // compute al the indexes into the G,H arrays
    computeGenerators();   // compute the generators themselves

    // Allocate empty constraints. For each one of Decryption, Re-sharing,
    // Encryption, and KeyGen, we have linear constraints over GF(p^ell)).
    // In addition we have one more Z_p linear constraint fot the proof of
    // approximate smallness.
    linConstr.resize(4*scalarsPerElement() +1);
    decLinCnstr = &(linConstr[0]);
    encLinCnstr = &(linConstr[scalarsPerElement()]);
    kGenLinCnstr = &(linConstr[2*scalarsPerElement()]);
    reShrLinCnstr= &(linConstr[3*scalarsPerElement()]);
    smlnsLinCnstr = &(linConstr[4*scalarsPerElement()]);

    // Then we have nDecSubvectors norm constraints for the subvectors of
    // the decryption noise, and one more norm constraint for each of the
    // encryption randomness, the encrypiton noise, the new secret-key, and
    // the key-generation noise. (Note that the norm constraint for the old
    // secret key was included with the proof of the previous step.)
    normConstr.resize(nDecSubvectors +4);
    rQuadCnstr = &(normConstr[nDecSubvectors]);
    encErrQuadCnstr = &(normConstr[nDecSubvectors+1]);
    skQuadCnstr= &(normConstr[nDecSubvectors+2]);
    kgErrQuadCnstr = &(normConstr[nDecSubvectors+3]);

    // dec noise will be broken into nDecSubvectors pieces, for each peice
    // we will commit separately to the noise itself and to the padding,
    // and each of these will be committed twice, wrt the Gs and te Hs.

    decErrCom.resize(nDecSubvectors); // each entry holds two commitments
    decErrPadCom.resize(nDecSubvectors);
}

// Compute the indexes of the first scalar in the (representation
// of) the various vectors. These indexes will be used to refer
// to all the variables in the linear and nor constraints.
void VerifierData::setIndexes() {
    // How many subvectors do we have for the decryption randomness
    assert((gk->tee*gk->ell) % DEC_ERRV_SZ == 0);
    nDecSubvectors = (gk->tee*gk->ell) / DEC_ERRV_SZ;

    // number of scalar variables representing each of the vectors
    int pt1Len, skLen, decErrLen, // decryption
        pt2Len, rLen, encErrLen,  // encryption
        kGenErrLen, decErrPadLen; // key generation and padding

    // the len variables denote the total number of scalars it takes to
    // represent each vector. Most of these vectors are over GF(P^ell),
    // except the plaintext and y vectors that are vectors of scalars.

    skLen = gk->kay * gk->ell;
    decErrLen = gk->tee * gk->ell; // = DEC_ERRV_SZ * nDecSubvectors
    rLen = gk->emm * gk->ell;
    encErrLen = kGenErrLen = JLDIM;
    pt1Len = gk->tee;
    pt2Len = gk->enn;
    decErrPadLen = PAD_SIZE * nDecSubvectors;

    // The indexes, in order: sk1,sk2,decErr,r,encErr,kGenErr,pt1,pt2,y
    sk1Idx = 0;
    sk1PadIdx    = sk1Idx + skLen;
    sk2Idx       = sk1PadIdx + PAD_SIZE;
    sk2PadIdx    = sk2Idx + skLen;
    decErrIdx    = sk2PadIdx + PAD_SIZE;
    decErrPadIdx = decErrIdx + decErrLen;
    rIdx         = decErrPadIdx + decErrPadLen;
    rPadIdx      = rIdx + rLen;
    encErrIdx    = rPadIdx + PAD_SIZE;
    encErrPadIdx = encErrIdx + encErrLen;
    kGenErrIdx   = encErrPadIdx + PAD_SIZE;
    kGenErrPadIdx= kGenErrIdx + kGenErrLen;
    pt1Idx       = kGenErrPadIdx + PAD_SIZE;
    pt2Idx       = pt1Idx + pt1Len;
    yIdx         = pt2Idx + pt2Len;
}

// Allocate G,H generators
void VerifierData::computeGenerators() {
    // How many generators: The +1 is due to the transformation that
    // makes the linear and quadratic lists disjoint, which adds another
    // variable. The indexing assumes that pt1,pt2,y are at the end after
    // all the others.
    int gLen = yIdx+LINYDIM+1; 
    int hLen = pt1Idx+1;
    Gs.resize(gLen);
    Hs.resize(hLen);
    for (int i=0; i<gLen; i++)
        Gs[i] = ped->getG(i);
    for (int i=0; i<hLen; i++)
        Hs[i] = ped->getH(i);
}


// Commit to a slice of the vector
Point commit(const SVector& v, size_t genIdx,
             const std::vector<Point>& Gs, CRV25519::Scalar& r,
             int fromIdx, int toIdx) {
    if (toIdx<0)
        toIdx = v.length();
    if (Gs.size() < genIdx + toIdx-fromIdx) {
        throw std::runtime_error("commit: generators not defined");
    }
    std::vector<CRV25519::Scalar> xes(toIdx - fromIdx);
    for (size_t i=fromIdx; i<toIdx; i++) {
        conv(xes[i], v[i]);
    }
    r.randomize();
    return DLPROOFS::commit(&(Gs[genIdx]), xes.data(), xes.size(), r);
}
Point commit(const EVector& v, size_t genIdx,
             const std::vector<Point>& Gs, CRV25519::Scalar& r,
             int fromIdx, int toIdx) {
    if (toIdx<0)
        toIdx = v.length();
    int n = scalarsPerElement()*(toIdx-fromIdx);
    if (Gs.size() < genIdx +n) {
        throw std::runtime_error("commit: generators not defined");
    }
    std::vector<CRV25519::Scalar> xes(n);
    size_t idx = 0;
    for (size_t i=fromIdx; i<toIdx; i++)
        for (size_t j=0; j<scalarsPerElement(); j++) {
            conv(xes[idx], coeff(v[i], j));
            idx++;
        }
    r.randomize();
    return DLPROOFS::commit(&(Gs[genIdx]), xes.data(), xes.size(), r);
}


// Compute the norm-squared of v as a bigInt (not modular reduction)
BigInt normSquaredBI(BIVector& vv) {
    // map integers to the range [-P/2,P/2]
    const BigInt POver2 = GlobalKey::P() / 2;
    for (size_t i=0; i<vv.length(); i++) {
        if (vv[i] > POver2)
            vv[i] -= GlobalKey::P();
    }
    BigInt normSquared;
    InnerProduct(normSquared, vv, vv);
    return normSquared;
}
BigInt normSquaredBigInt(const SVector& v) {
    BIVector vv;
    conv(vv, v); // convert from sclars mod P to integers
    return normSquaredBI(vv);
}
BigInt normSquaredBigInt(const Element* v, size_t len) {
    BIVector vv;
    resize(vv, len*scalarsPerElement());
    for (size_t i=0; i<len; i++) for (size_t j=0; j<scalarsPerElement(); j++)
        conv(vv[i*scalarsPerElement() +j], coeff(v[i], j));
    return normSquaredBI(vv);
}
BigInt normSquaredBigInt(const EVector& v) {
    BIVector vv;
    ALGEBRA::conv(vv, v); // convert from GF(p^e) to integers
    return normSquaredBI(vv);
}

// Add to v four integers a,b,c,d such that the result
// (v | a,b,c,d) has norm exactly equal to the bound
void pad2exactNorm(const SVector& v, SVector& pad, const BigInt& bound) {
    BigInt delta = bound*bound - normSquaredBigInt(v);
    auto fourSqrt = decompose4(delta);
    // returns four BigInts s.t., a^2+b^2+c^2+d^2 = delta

    for (size_t i=0; i<PAD_SIZE; i++)
        conv(pad[i], fourSqrt[i]); // convert to scalars modulo P
}
void pad2exactNorm(const ALGEBRA::Element* v, size_t len,
        ALGEBRA::Element* padSpace, const ALGEBRA::BigInt& bound) {
    BigInt norm2 = normSquaredBigInt(v, len);
    BigInt delta = bound*bound - norm2;
    auto fourSqrt = decompose4(delta);
        // returns four BigInts s.t., a^2+b^2+c^2+d^2 = delta

    // How many elements to make up at least PAD_SIZE scalars
    size_t extra = ceilDiv(PAD_SIZE,scalarsPerElement());
    SVector tmp;
    resize(tmp, scalarsPerElement());
    size_t idx = 0; // index into the fourSqrt array
    for (size_t i=0; i<extra; i++) {
        for (size_t j=0; j<scalarsPerElement(); j++)
            if (idx < PAD_SIZE)
                conv(tmp[j], fourSqrt[idx++]); // convert to scalars modulo P
            else
                tmp[j] = Scalar::zero();
        ALGEBRA::conv(padSpace[i], tmp); // conv from vector of scalars to element
    }
}
void pad2exactNorm(const EVector& v, EVector& pad, const BigInt& bound) {
    size_t n = v.length();
    size_t extra = ceilDiv(PAD_SIZE,scalarsPerElement());
    pad2exactNorm(&(v[0]), n, &(pad[0]), bound);
}
    

// Expand a constraint a*x with a in GF(p^e) to e constrints over scalars,
// namely store in e constraints in e variables the e-by-e matrix representing
// the multiply-by-a matrix over the mase field.
// The variables in the constraints are idx,idx+1,... I.e., the constraints
// are idx -> a.freeTerm, idx+1 -> a.coeffOf(X), idx+2 -> a.coeffOf(X^2),...
// These functions assume that GF(p^e) is represented modulo X^e +1.
void expandConstraints(LinConstraint* constrs, int idx, const Element& a) {
    // expand e into the scalar matrix representing multiply-by-e

    for (int i=0; i<scalarsPerElement(); i++) {
        for (int j=0; j<scalarsPerElement(); j++) {
            CRV25519::Scalar s;
            if (i>=j)
                conv(s, coeff(a,i-j)); // convert a_{i-j} to CRV25519::Scalar
            else
                conv(s, -coeff(a,i+scalarsPerElement()-j)); // -a{i-j mod e}
            constrs[i].addTerm(idx+j, s);
        }
    }
}
// Expand <v,x> for a slice of a vector v over GF(p^e)
void expandConstraints(LinConstraint* constrs, int idx,
                      const EVector& v, int from, int to) {
    if (to < 0)
        to = v.length();

    for (size_t i=from; i<to; i++, idx += scalarsPerElement())
        expandConstraints(constrs, idx, v[i]);
}
// Convert <v,x> for a slice of a vector v over GF(p^e), where x is over Z_p
void makeConstraints(LinConstraint* constrs, int idx,
                      const EVector& v, int from, int to) {
    if (to < 0)
        to = v.length();
    for (int j=0; j<scalarsPerElement(); j++) { // expand to ell constraints
        auto& c = constrs[j];
        for (int i=from; i<to; i++) {
            CRV25519::Scalar s;
            conv(s, coeff(v[i], j)); // convert v[i]_j to CRV25519::Scalar
            c.addTerm(idx+i-from, s);
        }
    }
}
void setEqsTo(LinConstraint* constrs, const ALGEBRA::Element& e) {
    for (int j=0; j<scalarsPerElement(); j++) {
        auto& c = constrs[j];
        conv(c.equalsTo, coeff(e,j));
    }
}

// compute the vector (1,x,x^2,...,x^{len-1})
void powerVector(EVector& vec, const Element& x, int len) {
    resize(vec, len);
    conv(vec[0], 1);
    for (int i=1; i<vec.length(); i++)
        vec[i] = vec[i-1] * x;
}

} // end of namespace REGEVENC