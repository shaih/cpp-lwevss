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
#include <iostream>
#include <stdexcept>
#include <cmath>

#include "utils.hpp"
#include "regevEnc.hpp"
#include "ternaryMatrix.hpp"
#include "merlin.hpp"
#include "pedersen.hpp"
#include "bulletproof.hpp"

namespace REGEVENC {
using CRV25519::Point, DLPROOFS::PedersenContext,
    DLPROOFS::MerlinBPctx, DLPROOFS::LinConstraint, DLPROOFS::QuadConstraint;
// NOTE: REGEVENC::Scalar is not the same as CRV25519::Scalar

constexpr int JLDIM = 256; // The target dimension of Johnson–Lindenstrauss

struct MerlinRegev: public MerlinBPctx {
    void processVector(const std::string& label, const SVector& v) {
        unsigned char buf[32];
        for (size_t i=0; i<v.length(); i++) {
            scalarBytes(buf, v[i], sizeof(buf));
            merlin_transcript_commit_bytes(&mctx,nullptr,0,buf,sizeof(buf));
        }
    }
    void processMatrix(const std::string& label, const SMatrix& m) {
        if (m.NumRows()<1)
            return;
        processVector(label, m[0]);
        for (size_t i=1; i<m.NumRows(); i++) {
            processVector(std::string(), m[i]);
        }
    }
    // a challenge n-by-m trenary matrix
    void newTernaryMatrix(const std::string& label,
                          TernaryMatrix& R, size_t n, size_t m) {
        size_t bufSize = (n*m +3)/4; // two bits per element
        unsigned char buf[bufSize];
        merlin_transcript_challenge_bytes(&mctx,
            (const unsigned char*)label.data(),label.size(),buf,sizeof(buf));
        R.setFromBytes(buf, n, m);
    }
    Scalar newScalar(const std::string& label) {
        unsigned char buf[32];
        merlin_transcript_challenge_bytes(&mctx,
            (const unsigned char*)label.data(),label.size(),buf,sizeof(buf));
        Scalar s;
        scalarFromBytes(s, buf, sizeof(buf));
        return s;
    }
};

void conv(CRV25519::Scalar& to, const ALGEBRA::Scalar& from) {
    scalarBytes(to.bytes, from, sizeof(to.bytes));
}

Point commit(const SVector& v, PedersenContext& ped, size_t genIdx) {
    std::vector<Point> Gs(v.length());
    std::vector<CRV25519::Scalar> xes(v.length());
    for (size_t i=genIdx; i<Gs.size()+genIdx; i++) {
        Gs[i] = ped.getG(i);
        conv(xes[i], v[i]);
    }
    auto r = CRV25519::randomScalar();
    return DLPROOFS::commit(Gs.data(), xes.data(), Gs.size(), r);
}


// Holds the constraints and witnesses for the encryption proof.
// Quadratic is <r2,r2>=bound1, and linear are
// - (M|G) * (r1|ptxt)^t = ctxt, where G = (1,Delta) \tensor I
// - (r1|r2) * (R1/-I) = 0
// - (r2|y) * (R2/I() = z
struct RegevEncProof {
    struct Commitment {
        size_t Gidx; // 1st generator for commitment
        Point c;     // The commitment itself
    } ptCommit, r1Commit, r2Commit, yCommit;
    LinConstraint r1pt, r1r2, r2y;
    QuadConstraint r2r2;
};

// Compute the norm-squared of v as a bigInt (not modular reduction)
BigInt normSquaredBigInt(const SVector& v) {
    const BigInt Pover2 = GlobalKey::P() / 2;
    BIVector vv;
    conv(vv, v); // convert from sclars mod P to integers
    // map integers to the range [-P/2,P/2]
    for (size_t i=0; i<vv.length(); i++) {
        if (vv[i] > Pover2)
            vv[i] -= GlobalKey::P();
    }
    BigInt normSquared;
    InnerProduct(normSquared, vv, vv);
    return normSquared;
}

// Add to v four integers a,b,c,d such that the result
// (v | a,b,c,d) has norm exactly equal to the bound
SVector& pad2exactNorm(SVector& v, const BigInt& bound) {
    BigInt delta = bound*bound - normSquaredBigInt(v);
    auto fourSqrt = ALGEBRA::decompose4(delta);
    // returns four BigInts s.t., a^2+b^2+c^2+d^2 = delta

    size_t n = v.length();
    resize(v, n+4);
    for (size_t i=0; i<4; i++)
        conv(v[n+i], fourSqrt[i]); // convert to scalars modulo P
    return v;
}

RegevEncProof encProof(const GlobalKey& gk,
              const SVector& ptxt, SVector& ctxt1, SVector& ctxt2,
              const SVector& r1, PedersenContext& ped, MerlinRegev& mer) {
    RegevEncProof pf;
    // Compute commitment wrt generators G{n+1}...G{n+m}
    size_t genIdx = ptxt.length() +1;
    pf.r1Commit = {genIdx, commit(r1, ped, genIdx)};
    mer.processPoint("RegevEncRand", pf.r1Commit.c);

    // Rejection sampling #1: Repeatedly choose random matrices R1 until
    // r2=r1*R1 is small enough
    BigInt bound = (toBigInt(1) << (gk.rho+2)) // ceil( 2^{rho+2}sqrt(m) )
                    * (long) std::ceil(std::sqrt((double)gk.emm));
    TernaryMatrix R1;
    SVector r2;    
#ifdef DEBUGGING
    for (int ii=0; i<31; i++) { // don't try more than 30 times
        if (ii==30)
            throw std::runtime_error("encProof: too many rejections #1");
#else
    while (true) {
#endif
        // fresh random commitment wrt generators G1...Gn
        pf.ptCommit = {1, commit(ptxt, ped, 1)};
        MerlinRegev resetCtx = mer;
        resetCtx.processPoint("RegevEncPtxt", pf.ptCommit.c);
        // Generate a challenge m-by-256 ternary matrix
        resetCtx.newTernaryMatrix("RegevEncR1", R1, gk.emm, JLDIM);
        r2 = r1 * R1;
        // check that |r|^2 < 2^{2rho+4}*m
        if (normSquaredBigInt(r2) <= bound*bound) {
            mer = resetCtx;
            break;
        }
    }

    // Pad r2 by four more elements a,b,c,d such that the result has
    // norm exactly ceil( 2^{rho+2}*sqrt(m) )
    pad2exactNorm(r2, bound);

    genIdx = ptxt.length() +r1.length() +1;
    // Compute commitment wrt generators G{n+m+1}...G{n+m+256}
    pf.r2Commit = {genIdx, commit(r2, ped, genIdx)};
    mer.processPoint("RegevEncr2", pf.r2Commit.c);

    // Rejection sampling #1: Repeatedly choose random masking vectors y
    // and matrices R2 until both u=r2*R2 and z=u+y are small enough
    // r2=r1*R1 is small enough

    // We set the bound beta to prove (which should be \approx sqrt(P)/520)
    // as beta=2^{119}*128/129, so the masking vector is chosen at random
    // from [+-2^{119}]^128. We check that |u|_{infty} < beta/128 and
    // that |z|_{infty} < beta.
    BigInt bound2 = (toBigInt(1) << 126) / 129; // 2^119 * 128/129
    bound2 *= bound2;                           // squared
    BoundedSizeScalar rzr(119);  // for choosing elements in [+-(2^119-1)]

    // starting index for generators for committing to the masking vector y
    genIdx = ptxt.length() +r1.length() +JLDIM +1;

    TernaryMatrix R2;
    SVector u,y,z;
    resize(y,128);

#ifdef DEBUGGING
    for (int ii=0; i<31; i++) { // don't try more than 30 times
        if (ii==30)
            throw std::runtime_error("encProof: too many rejections #2");
#else
    while (true) {
#endif
        for (size_t i=0; i<128; i++) rzr.randomize(y[i]);

        // Compute commitment wrt generators G{n+m+257}...G{n+m+384}
        pf.yCommit = {genIdx, commit(y, ped, genIdx)};

        MerlinRegev reserCtx = mer;
        reserCtx.processPoint("RegevEncPtxt", pf.yCommit.c);

        // Generate a challenge 256-by-128 ternary matrix
        reserCtx.newTernaryMatrix("RegevEncR2", R2, JLDIM, 128);
        u = r2 * R1;
        z = u + y;
        // check that u,z are small enough
        if (normSquaredBigInt(u) <= (bound2>>14)  // |u| <= beta/128
            &&  normSquaredBigInt(z) <= bound2) { // |z| <= beta
            mer = reserCtx;
            break;
        }
    }

    // Add quadratic constraint <r2,r2>=bound1, and linear constraints
    // - (M|G) * (r1|ptxt)^t = ctxt, where G = (1,Delta) \tensor I
    // - (r1|r2) * (R1/-I) = 0
    // - (r2|y) * (R2/I() = z
    // The corresponding witnesses are r1,r2,y,ptxt.
    // The linear constraints are compressed into a single constraint
    // by taking a random linear combination of them.

    // Derive a random challenge x, the linear combination of the linear
    // constraints will be (1,x,x^2,...)
    Scalar x = mer.newScalar("RegevEncX");
    SVector vA, vB, vR1, vR2; 

    // Build the constraint for (M|G) * (r1|ptxt)^t = ctxt
    resize(vA, gk.kay); // to multiply by the CRS
    conv(vA[0], 1);
    for (size_t i=1; i<vA.length(); i++) vA[i] = vA[i-1]*x;

    resize(vB, ell*gk.enn); // to multiply by the keys
    vB[0] = vA[vA.length()-1] * x;
    for (size_t i=1; i<vB.length(); i++) vB[i] = vB[i-1]*x;

    // uM = (vA|vB)*(A/B)
    SVector uM = vA * gk.A + vA * gk.B;

    // The first linear constraint is 
    // \sum (vB[2i]+Delta*vB[2i+1]) * pt[i] + \sum uM[i] * r1[i]
    //                              = \sum (vA|vB)[i] * (ct1|ct2)[i]
    // Note: the code converts from REGEVENC::Scalar to CRV25519::Scalar
    size_t baseIdx = pf.ptCommit.Gidx;
    for (size_t i=0; i<ptxt.length(); i++) { // FIXME: Assumes ell=2
        conv(pf.r1pt.terms[baseIdx+i], vB[2*i] + gk.delta()*vB[2*i +1]);
    }
    baseIdx = pf.r1Commit.Gidx;
    for (size_t i=0; i<r1.length(); i++) {
        conv(pf.r1pt.terms[baseIdx+i], uM[i]);
    }
    conv(pf.r1pt.equalsTo, innerProduct(ctxt1,vA)+innerProduct(ctxt2,vB));

    // The second linear constraint is <r1,R1*vR1) + <r2,-vR1> = 0
    resize(vR1, R1.NumCols()); // to multiply by R1
    vR1[0] = vB[vB.length()-1] * x;
    for (size_t i=1; i<vR1.length(); i++) vR1[i] = vR1[i-1]*x;
    SVector uR1 = R1 * vR1;

    baseIdx = pf.r1Commit.Gidx;
    for (size_t i=0; i<r1.length(); i++) {
        conv(pf.r1r2.terms[baseIdx+i], uR1[i]);
    }
    baseIdx = pf.r2Commit.Gidx;
    for (size_t i=0; i<r2.length(); i++) {
        conv(pf.r1r2.terms[baseIdx+i], -vR1[i]);
    }
    pf.r1r2.equalsTo.setInteger(0);

    // The third linear constraint is <r2,R2*vR2) + <y,-vR2> = 0
    resize(vR2, R2.NumCols()); // to multiply by R2
    vR2[0] = vR1[vR1.length()-1] * x;
    for (size_t i=1; i<vR2.length(); i++) vR2[i] = vR2[i-1]*x;
    SVector uR2 = R2 * vR2;

    baseIdx = pf.r2Commit.Gidx;
    for (size_t i=0; i<r2.length(); i++) {
        conv(pf.r2y.terms[baseIdx+i], uR2[i]);
    }
    baseIdx = pf.yCommit.Gidx;
    for (size_t i=0; i<y.length(); i++) {
        conv(pf.r2y.terms[baseIdx+i], -vR2[i]);
    }
    pf.r2y.equalsTo.setInteger(0);

    return pf;
}
} // end of namespace REGEVENC