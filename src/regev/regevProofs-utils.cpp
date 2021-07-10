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
#include <cmath>
#include <cassert>
#include <numeric>
#include "algebra.hpp"
#include "regevProofs.hpp"

namespace ALGEBRA {
// Compute the norm-squared of v as a bigInt (no modular reduction)
BigInt normSquaredBI(BIVector& vv) {
    // map integers to the range [-P/2,P/2]
    const BigInt POver2 = REGEVENC::GlobalKey::P() / 2;
    for (size_t i=0; i<vv.length(); i++) {
        if (vv[i] > POver2)
            vv[i] -= REGEVENC::GlobalKey::P();
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
// Compute the infinity norm of v
BigInt lInftyNorm(const EVector& v) {
    BigInt ret = NTL::ZZ::zero();
    for (int i=0; i<v.length(); i++) {
        for (int j=0; j<scalarsPerElement(); j++) {
            BigInt x = abs(ALGEBRA::balanced( coeff(v[i],j) ));
            if (ret < x)
                ret = x;
        }
    }
    return ret;
}

// Break a mod-P vector v (considered in [+-P/2]) into two "digit" vector
// hi,lo, where lo \in [+-radix/2] and hi = (v-lo)/radix.
void breakTwoDigits(EVector& hi, EVector& lo, const EVector& v, const BigInt& radix) {
    resize(hi, v.length());
    resize(lo, v.length());
    // initialize scratch working space
    SVector sHi; resize(sHi, scalarsPerElement());
    SVector sLo; resize(sLo, scalarsPerElement());
    BigInt half = radix/2;
    for (int i=0; i<v.length(); i++) {
        BIVector vi = balanced(v[i]); // convert to an ell-vector of BigInts
        for (int j=0; j<scalarsPerElement(); j++) {
            BigInt lo_ij = vi[j] % radix;
            BigInt hi_ij = (vi[j]-lo_ij) / radix;
            if (lo_ij > half) {
                lo_ij -= radix;
                hi_ij++;
            }
            else if (lo_ij < -half) {
                lo_ij += radix;
                hi_ij--;
            }
            conv(sLo[j], lo_ij);
            conv(sHi[j], hi_ij);
        }
        conv(lo[i], sLo);
        conv(hi[i], sHi);
    }
}

} // end of ALGEBRA namespace

using namespace ALGEBRA;
namespace REGEVENC {
using CRV25519::Point, DLPROOFS::PedersenContext,
    DLPROOFS::MerlinBPctx, DLPROOFS::LinConstraint, DLPROOFS::QuadConstraint;
// NOTE: REGEVENC::Scalar is not the same as CRV25519::Scalar

VerifierData::VerifierData(GlobalKey& g, PedersenContext& p,
                           MerlinRegev& mr, const SharingParams& _sp) {
    gk = &g;
    ped = &p;
    mer = &mr;
    sp = (SharingParams*) &_sp;

    // The params k,m,n in scalars (rather than GF(p^ell) elements)
    int kk = g.kay*g.ell;
    int nn = g.enn*g.ell;

    // Set the values of the various bounds on the compressed vectors

    BigInt sig_kg = BigInt(1)<<g.sigmaEnc1; // "small" noise size
    BigInt sig_e2 = BigInt(1)<<g.sigmaEnc2; // "large" noise size

    // A bound on the l-infty norm of the compressed sk and enc randomness:
    // These vectors bounded in l2 norm by 2*sqrt(kk), so the compressed
    // vector is bounded by sqrt(337) * 2*sqrt(kk)
    B_r = B_sk = BigInt((long)ceil(2*sqrt(337*kk)));

    // A bound on the l-infty norm of the compressed "small" noise vectors:
    // The small noise is bounded in l2 by sig_kg*sqrt(kk/2), so the compressed
    // vector is bounded by sqrt(337) * sig_kk*sqrt(kk/2)
    B_eNoise1 = B_kNoise = multDbl(sqrt(kk*337/2.0), sig_kg);

    // A bound on the l-infty norm of the compressed "large" noise vector
    B_eNoise2 = multDbl(sqrt(nn*337/2.0), sig_e2);

    // A bound on the l-infty norm of the compressed decryption noise:
    // The decryption noise itself, for an honest party, is bounded in
    // l2 norm by 1.7*sig_e2*nn + 24*sig_kg*sqrt(kk*nn). The compressed
    // vector, therefore, is bound in l2 norm whp by:
    //     sqrt(337) * (1.7*sig_e2*nn + 24*sig_kg*sqrt(kk*nn)).
    B_dNoise = multDbl(sqrt(337)*1.7, sig_e2*nn) + multDbl(sqrt(kk*nn*377), 24*sig_kg);

    // sanity-check, we should have B_sk < B_eNoise1 < B_eNoise2 < B_dNoise
    if (B_sk >= B_eNoise1 || B_eNoise1 >= B_eNoise2 || B_eNoise2 >= B_dNoise) {
        throw std::runtime_error("VerifierData: must have B_sk < B_eNoise1 < B_eNoise2 < B_dNoise");
    }

    // We are splitting these compressed noise vectors into two digits,
    // all using a radix which is 2*sqrt(e1Noise)/sqrt(256)
    int radixBits = ceil(log2BI(B_kNoise)/2) -3;
    radix = BigInt(1) << radixBits;

    // The l-infinity of the compressed vectors/digits is bounded by
    // B_dNoise/radix, and concatenating all of them has dimension
    // d=10*(JLDIM+PAD_SIZE) so the y offset vector has l-infinity
    // bounded by B_dNoise/radix * 9.75*129*sqrt(d)
    int d = 10*(JLDIM+PAD_SIZE);
    smlnsBits = ceil(log2(9.75*129*sqrt(d))+log2BI(B_dNoise)-radixBits);

    // The smallness bound is 128/129 * yBound
    B_smallness = multDbl(128.0/129.0, BigInt(1)<<smlnsBits);

    setIndexes(); // compute al the indexes into the G,H arrays
    computeGenerators();   // compute the generators themselves

    // Allocate empty linear constraints:
    // - 1*ell for decryption and approximate smallness
    // - 3*ell for encryption
    // - 2*ell for keygen
    // - n+1-t for the proof of correct re-sharing
    linConstr.resize(7*scalarsPerElement() + g.enn-g.tee+1);

    // We also have 10 norm constraints:
    // - 2 for decryption
    // - 5 for encryption
    // - 3 for keygen
    // Note that the norm constraint for the old secret key was
    // included with the proof of the previous step.
    normConstr.resize(10);
}

// Compute the indexes of the first scalar in the representation of
// the various vectors. These indexes will be used to refer to all
// the variables in the linear and nor constraints.
void VerifierData::setIndexes() {
    // How many subvectors do we have for the decryption randomness

    // number of scalar variables representing each of the vectors
    int pt1Len = gk->tee;
    int skLen = gk->kay * gk->ell;
    int pt2Len = gk->enn;
    int rLen = gk->kay * gk->ell;

    // The indexes, the quadratic variables first
    dCompHiIdx = 0;
    dPadHiIdx  = dCompHiIdx + JLDIM;
    dCompLoIdx = dPadHiIdx  + PAD_SIZE;
    dPadLoIdx  = dCompLoIdx + JLDIM;
    rCompIdx   = dPadLoIdx  + PAD_SIZE;
    rPadIdx    = rCompIdx   + JLDIM;
    eComp1HiIdx= rPadIdx    + PAD_SIZE;
    ePad1HiIdx = eComp1HiIdx+ JLDIM;
    eComp1LoIdx= ePad1HiIdx + PAD_SIZE;
    ePad1LoIdx = eComp1LoIdx+ JLDIM;
    eComp2HiIdx= ePad1LoIdx + PAD_SIZE;
    ePad2HiIdx = eComp2HiIdx+ JLDIM;
    eComp2LoIdx= ePad2HiIdx + PAD_SIZE;
    ePad2LoIdx = eComp2LoIdx+ JLDIM;
    sk2CompIdx = ePad2LoIdx + PAD_SIZE;
    sk2PadIdx  = sk2CompIdx + JLDIM;
    kCompHiIdx = sk2PadIdx  + PAD_SIZE;
    kPadHiIdx  = kCompHiIdx + JLDIM;
    kCompLoIdx = kPadHiIdx  + PAD_SIZE;
    kPadLoIdx  = kCompLoIdx + JLDIM;

    // Then the linear-only variables        
    sk1Idx = kPadLoIdx + PAD_SIZE;
    sk2Idx = sk1Idx + skLen;
    rIdx   = sk2Idx + skLen;
    pt1Idx = rIdx   + rLen;
    pt2Idx = pt1Idx + pt1Len;
    yIdx   = pt2Idx + pt2Len;

    // At the end the additional w variable
    wIdx   = yIdx + LINYDIM;
}

// Allocate G,H generators, assumes that setIndexes was called before
void VerifierData::computeGenerators() {
    // How many generators: The +1 is due to the transformation that
    // makes the linear and quadratic lists disjoint, which adds another
    // variable. The indexing assumes that pt1,pt2,y are at the end after
    // all the others.
    int gLen = wIdx +1;
    int hLen = sk1Idx +1;
    Gs.resize(gLen);
    Hs.resize(hLen);
    for (int i=0; i<gLen; i++)
        Gs[i] = ped->getG(i);
    for (int i=0; i<hLen-1; i++)
        Hs[i] = ped->getH(i);
    Hs[hLen-1] = ped->getH(wIdx);
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
// Commit to the same xes wrt both Gs and Hs
Point commit2(const EVector& v, size_t genIdx,
             const std::vector<Point>& Gs, const std::vector<Point>& Hs,
             CRV25519::Scalar& r, int fromIdx, int toIdx) {
    if (toIdx<0)
        toIdx = v.length();
    int n = scalarsPerElement()*(toIdx-fromIdx);
    if (Gs.size() < genIdx +n || Hs.size() < genIdx +n) {
        throw std::runtime_error("commit: G/H generators not defined");
    }
    std::vector<CRV25519::Scalar> xes(n);
    size_t idx = 0;
    for (size_t i=fromIdx; i<toIdx; i++)
        for (size_t j=0; j<scalarsPerElement(); j++) {
            conv(xes[idx], coeff(v[i], j));
            idx++;
        }
    std::vector<Point> GplusH(n);
    for (int i=0; i<n; i++)
        GplusH[i] = Gs[i+genIdx] + Hs[i+genIdx];

    r.randomize();
    Point C = DLPROOFS::commit(GplusH.data(), xes.data(), xes.size(), r);

#ifdef DEBUGGING
    if (C != DLPROOFS::commit2(&(Gs[genIdx]), xes.data(),
                             &(Hs[genIdx]), xes.data(), xes.size(), r))
        throw std::runtime_error("commit and commit2 disagree");
#endif
    return C;
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
    resize(pad,extra);
    pad2exactNorm(&(v[0]), n, &(pad[0]), bound);
}
    
// The expand functions below assume that GF(p^ell) is represented
// modulo X^ell +1.

// Expand a constraint a*x with a in GF(p^ell) to e constrints over scalars,
// namely store in 'constrs' ell constraints in ell variables, representing
// the ell-by-ell scalar matrix for multiply-by-a. The variables in these
// constraints are indexed by idx,idx+1,... For example, the constraints
// for the 1st row has coeffs: idx->a.freeTerm, idx+1 -> a.coeffOf(X),...
void expandConstraints(LinConstraint* constrs, int idx, const Element& a) {
    // expand a into the scalar matrix representing multiply-by-a
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
// Expand <v,x> for a slice of a vector v over GF(p^ell)
void expandConstraints(LinConstraint* constrs, int idx,
                      const EVector& v, int from, int to) {
    if (to < 0) to = v.length();
    for (size_t i=from; i<to; i++, idx += scalarsPerElement())
        expandConstraints(constrs, idx, v[i]);
}
// Convert <v,x> for a slice of a vector v over GF(p^ell), where x is over Z_p
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
void powerVector(SVector& vec, const Scalar& x, int len) {
    resize(vec, len);
    conv(vec[0], 1);
    for (int i=1; i<vec.length(); i++)
        vec[i] = vec[i-1] * x;
}
void powerVector(EVector& vec, const Element& x, int len) {
    resize(vec, len);
    conv(vec[0], 1);
    for (int i=1; i<vec.length(); i++)
        vec[i] = vec[i-1] * x;
}
void powerVector(std::vector<CRV25519::Scalar>& vec, const CRV25519::Scalar& x, int len)
{
    vec.resize(len);
    vec[0].setInteger(1);
    for (int i=1; i<len; i++)
        vec[i] = vec[i-1] * x;
}

// debugging/monitoring tools

bool checkQuadCommit(DLPROOFS::QuadConstraint& c,
    const Point& com, const Point& padCom, const CRV25519::Scalar& rnd,
    const CRV25519::Scalar& padRnd, DLPROOFS::PtxtVec& witness, PedersenContext* ped)
{
    auto comm = com + padCom;
    auto rand = rnd + padRnd;

    std::vector<CRV25519::Scalar> w;
    std::vector<CRV25519::Point> gens;
    for (auto i: c.indexes) {
        gens.push_back(ped->getG(i) + ped->getH(i));
        w.push_back(witness[i]);
    }
    return DLPROOFS::verifyCom(comm, gens.data(), w.data(), gens.size(), rand);
}
bool checkLinCommit(DLPROOFS::PtxtVec& pv,
    const Point& com, const CRV25519::Scalar& rnd,
    DLPROOFS::PtxtVec& witness, PedersenContext* ped)
{
    std::vector<CRV25519::Scalar> w;
    std::vector<CRV25519::Point> gs;
    for (auto& it: pv) {
        gs.push_back(ped->getG(it.first));
        w.push_back(witness[it.first]);
    }
    return DLPROOFS::verifyCom(com, gs.data(), w.data(), gs.size(), rnd);
}

} // end of namespace REGEVENC
