#ifndef _REGEVPROOFS_HPP_
#define _REGEVPROOFS_HPP_
/* regevProofs.hpp - Proofs of correct behavior for Regev encryption
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
#include <iostream>
#include <stdexcept>
#include <cmath>

#include <NTL/mat_ZZ.h>

#include "utils.hpp"
#include "regevEnc.hpp"
#include "ternaryMatrix.hpp"
#include "merlin.hpp"
#include "pedersen.hpp"
#include "shamir.hpp"
#include "bulletproof.hpp"

namespace REGEVENC {
using CRV25519::Point, DLPROOFS::PedersenContext, TOOLS::SharingParams,
    DLPROOFS::MerlinBPctx, DLPROOFS::LinConstraint, DLPROOFS::QuadConstraint;
// NOTE: REGEVENC::Scalar is not the same as CRV25519::Scalar

typedef std::array<Point,2> TwoPoints;
typedef std::array<CRV25519::Scalar,2> TwoScalars;

#define DEBUGGING

inline constexpr int PAD_SIZE=4; // add 4 scalars to pad to a specific sum-of-squares
// We break the decryption error vector into subvectors, each with this many scalars
#ifndef DEBUGGING
inline constexpr int DEC_ERRV_SZ=16; // size of decryption noise subvectors
inline constexpr int JLDIM = 256;    // Target dimension of Johnson–Lindenstrauss
inline constexpr int LINYDIM=128;    // Target dimension in approximate l-infty proofs
#else
inline constexpr int DEC_ERRV_SZ=2;
inline constexpr int JLDIM = 8;
inline constexpr int LINYDIM=4;
#endif
inline void conv(CRV25519::Scalar& to, const ALGEBRA::BigInt& from) {
    ALGEBRA::bigIntBytes(to.bytes, from, sizeof(to.bytes));
}
inline void conv(CRV25519::Scalar& to, const ALGEBRA::Scalar& from) {
    ALGEBRA::scalarBytes(to.bytes, from, sizeof(to.bytes));
}
inline void conv(ALGEBRA::Scalar& to, const CRV25519::Scalar& from) {
    ALGEBRA::scalarFromBytes(to, from.bytes, sizeof(from.bytes));
}

// More functionality for a Merlin-context wrapper
struct MerlinRegev: public MerlinBPctx {
    MerlinRegev() = default;
    explicit MerlinRegev(const merlin_transcript& m): MerlinBPctx(m) {}
    explicit MerlinRegev(const std::string& st): MerlinBPctx(st) {}

    void processVector(const ALGEBRA::SVector& v,
                       unsigned char* label=nullptr, size_t llen=0) {
        if (v.length()==0) return;
        unsigned char buf[ALGEBRA::bytesPerScalar()];
        ALGEBRA::scalarBytes(buf, v[0], sizeof(buf));
        merlin_transcript_commit_bytes(&mctx,label,llen,buf,sizeof(buf));
        for (size_t i=1; i<v.length(); i++) {
            ALGEBRA::scalarBytes(buf, v[i], sizeof(buf));
            merlin_transcript_commit_bytes(&mctx,nullptr,0,buf,sizeof(buf));
        }
    }
    void processVector(const ALGEBRA::EVector& v,
                       unsigned char* label=nullptr, size_t llen=0) {
        if (v.length()==0) return;
        unsigned char buf[ALGEBRA::bytesPerScalar()*ALGEBRA::scalarsPerElement()];
        ALGEBRA::elementBytes(buf, v[0], sizeof(buf));
        merlin_transcript_commit_bytes(&mctx,label,llen,buf,sizeof(buf));
        for (size_t i=1; i<v.length(); i++) {
            ALGEBRA::elementBytes(buf, v[i], sizeof(buf));
            merlin_transcript_commit_bytes(&mctx,nullptr,0,buf,sizeof(buf));
        }
    }
    void processMatrix(const ALGEBRA::SMatrix& M,
                       unsigned char* label=nullptr, size_t llen=0) {
        if (M.NumRows()<1)
            return;
        processVector(M[0],label,llen);
        for (size_t i=1; i<M.NumRows(); i++) {
            processVector(M[i]);
        }
    }
    void processMatrix(const ALGEBRA::EMatrix& M,
                       unsigned char* label=nullptr, size_t llen=0) {
        if (M.NumRows()<1)
            return;
        processVector(M[0],label,llen);
        for (size_t i=1; i<M.NumRows(); i++) {
            processVector(M[i]);
        }
    }
    // a challenge n-by-m trenary matrix
    void newTernaryMatrix(const std::string& label,
                          ALGEBRA::TernaryMatrix& R, size_t n=0, size_t m=0) {
        if (n<=0) n = R.NumRows();
        if (m<=0) m = R.NumCols();
        if (n==0 || m==0) return; // nothing to do
        size_t bufSize = (n*m +3)/4; // two bits per element
        unsigned char buf[bufSize];
        merlin_transcript_challenge_bytes(&mctx,
            (const unsigned char*)label.data(),label.size(),buf,sizeof(buf));
        R.setFromBytes(buf, n, m);
    }
    void newTernaryEMatrix(const std::string& label,
                          ALGEBRA::TernaryEMatrix& R, size_t n=0, size_t m=0) {
        if (n<=0) n = R.NumRows();
        if (m<=0) m = R.NumCols();
        if (n==0 || m==0) return; // nothing to do
        size_t bufSize = ALGEBRA::scalarsPerElement()*((n*m +3)/4); // two bits per element
        unsigned char buf[bufSize];
        merlin_transcript_challenge_bytes(&mctx,
            (const unsigned char*)label.data(),label.size(),buf,sizeof(buf));
        R.setFromBytes(buf, n, m);
    }
    ALGEBRA::Scalar newScalar(const std::string& label) {
        unsigned char buf[ALGEBRA::bytesPerScalar()];
        merlin_transcript_challenge_bytes(&mctx,
            (const unsigned char*)label.data(),label.size(),buf,sizeof(buf));
        ALGEBRA::Scalar s;
        ALGEBRA::scalarFromBytes(s, buf, sizeof(buf));
        return s;
    }
    ALGEBRA::Element newElement(const std::string& label) {
        int bufSize = ALGEBRA::bytesPerScalar()*ALGEBRA::scalarsPerElement();
        unsigned char buf[bufSize];
        merlin_transcript_challenge_bytes(&mctx,
            (const unsigned char*)label.data(),label.size(),buf,sizeof(buf));
        ALGEBRA::Element e;
        ALGEBRA::elementFromBytes(e, buf, bufSize);
        return e;
    }
};

inline constexpr int smlnsBits = 20; // The bitsize of B_smallness below

// A stucture for holding all the public data that both the prover and
// the verifier knows. The prover will fill in the commitments, both
// can use them to derive the various challenges in the proof prootcols.
struct VerifierData {
    // The global public key, and utility objects for Pedersen commitments
    // and for "Merlin Transcripts" (to derive challenges in Fiat-Shamir)
    GlobalKey *gk;        // global Regev key
    PedersenContext *ped; // Pedersen commitment context
    MerlinRegev *mer;     // Merlin transcript context
    SharingParams *sp;    // parameters of Shamir sharing

    // The various public size bounds
    ALGEBRA::BigInt B_decNoise;// bounds each sub-vector of decryption noise
    ALGEBRA::BigInt B_sk;      // bounds the secret-key size
    ALGEBRA::BigInt B_encRnd;  // bounds the encryption randomness size
    ALGEBRA::BigInt B_encNoise;// bounds the size of the encryption noise
    ALGEBRA::BigInt B_kGenNoise;// bounds the size of the keygen noise
    ALGEBRA::BigInt B_smallness;// Used in the approximate smallness protocol

    std::vector<Point> Gs, Hs; // lists of generators

    // For most vectors, we have both the vector itself (e.g., decErr*1) and
    // the padding that the prover computes to pad it to some pre-determined
    // size (e.g., decErr*2). The only ones without padding are pt1, pt2, y

    int nDecSubvectors; // number of decryption-noise subvectors

    // indexes into the generator list
    int pt1Idx, sk1Idx, decErrIdx, decErrPadIdx,        // decryption
        pt2Idx, rIdx, rPadIdx, encErrIdx, encErrPadIdx, // encryption
        sk2Idx, sk2PadIdx, kGenErrIdx, kGenErrPadIdx,   // key generation
        yIdx;                                          // smallness proof

    // Commitments to different variables. The quadratic equations require
    // two commitment per variable, one with G generators and the other
    // with H generators. So everything except pt1, pt2, y needs TwoPoints

    // dec noise will be broken into a number of pieces, for each peice
    // we will commit separately to the noise itself and to the padding,
    // and each of these will be committed twice, wrt the Gs and te Hs.
    std::vector<TwoPoints> decErrCom, decErrPadCom;

    // Most everything else is two commitment per vector
    TwoPoints sk1Com, rCom, rPadCom, encErrCom, encErrPadCom,
            sk2Com, sk2PadCom, kGenErrCom, kGenErrPadCom;

    Point pt1Com, pt2Com, yCom;

    std::vector<DLPROOFS::LinConstraint> linConstr;
    std::vector<DLPROOFS::QuadConstraint> normConstr;

    // pointers into the above vectors
    DLPROOFS::LinConstraint *decLinCnstr, *encLinCnstr, *kGenLinCnstr, *reShrLinCnstr, *smlnsLinCnstr;
    DLPROOFS::QuadConstraint *rQuadCnstr, *encErrQuadCnstr, *skQuadCnstr, *kgErrQuadCnstr;

    ALGEBRA::EVector z; // the masked vector z from the proof of smallness

    // Set the indexes to their default values
    void setIndexes();
    void computeGenerators();

    // Reset when preparing for a new proof at the prover's site
    void prepareForNextProof() {
        std::swap(sk1Idx,sk2Idx);
        sk1Com = sk2Com; // copy commitment to the previous sk

        // zero out all the commitments and constraints
        TwoPoints empty2points;
        decErrCom.assign(decErrCom.size(), empty2points);
        decErrPadCom.assign(decErrPadCom.size(), empty2points);
        rCom =rPadCom =encErrCom =encErrPadCom =sk2Com =sk2PadCom
            =kGenErrCom =kGenErrPadCom =empty2points;
        pt1Com = pt2Com = yCom = Point::identity();

        // empty the constraints w/o invalidating the pointers to them
        DLPROOFS::LinConstraint emptyLin;
        for (auto& lc : linConstr) lc = emptyLin;
        DLPROOFS::QuadConstraint emptyQuad;
        for (auto& qc : normConstr) qc = emptyQuad;
    }

    VerifierData() = default;
    VerifierData(GlobalKey& gk, PedersenContext& ped, MerlinRegev& mer,
                 const SharingParams& sp);
};

// For each commitment in the VerifierData, the ProverData must hold
// the corresponding opening: the randomness r and the witness values
struct ProverData {
    VerifierData *vd;

    // commitment randomness: For most vectors we have four commitment,
    // to the vector and its padding, each wrt both the Gs and the Hs.
    // For decryption noise we have four commitments per subvector.
    // The plaintext and the y vector have just one commitment each.
    std::vector<TwoScalars> decErrRnd, decErrPadRnd;
    TwoScalars sk1Rnd, rRnd, rPadRnd, encErrRnd, encErrPadRnd,
                sk2Rnd, sk2PadRnd, kGenErrRnd, kGenErrPadRnd;
    CRV25519::Scalar pt1Rnd, pt2Rnd, yRnd;

    // committed values: all except pt1, pt2, y consist of the original
    // vector, and padding to make them of a certain public size. For
    // the original vector we just keep a pointer to them, for the padding
    // we allocate separate EVectors to hold them.

    ALGEBRA::EVector *sk1, *decErr, *r, *sk2;
    ALGEBRA::SVector *pt1, *pt2;

    ALGEBRA::EVector decErrPadding, rPadding, 
        encErr, encErrPadding, sk2Padding, kGenErr, kGenErrPadding, y;

    // Collect all the secret variables in a DLPROOFS::PtxtVec map
    void assembleFullWitness(DLPROOFS::PtxtVec& witness);

    // Reset when preparing for a new proof at the prover's site
    void prepareForNextProof() {
        vd->prepareForNextProof(); // reset the public data
        sk1Rnd = sk2Rnd; // randomness of commitment to secret key
        sk1 = sk2;       // the secret key itself

        // zero-out everything else
        TwoScalars empty2scalars;
        decErrRnd.assign(vd->nDecSubvectors, empty2scalars);
        decErrPadRnd.assign(vd->nDecSubvectors, empty2scalars);
        rRnd =rPadRnd =encErrRnd =encErrPadRnd =sk2Rnd
            =sk2PadRnd =kGenErrRnd =kGenErrPadRnd =empty2scalars;
        pt1Rnd =pt2Rnd =yRnd = CRV25519::Scalar();

        decErr = r = sk2 = nullptr;
        pt1 = pt2 = nullptr;
        clear(decErrPadding);  clear(rPadding);
        clear(encErr);     clear(encErrPadding);  clear(sk2Padding);
        clear(kGenErr);    clear(kGenErrPadding); clear(y);
    }

    ProverData() = default;    
    ProverData(VerifierData& verData): vd(&verData) {
        // Allocate space for commitment randomness to decryption noise
        int paddingSize = ALGEBRA::ceilDiv(PAD_SIZE,ALGEBRA::scalarsPerElement());
        decErrRnd.resize(vd->nDecSubvectors);
        decErrPadRnd.resize(vd->nDecSubvectors);
        // Allocate space for padding
        ALGEBRA::resize(decErrPadding, vd->nDecSubvectors*paddingSize);
        ALGEBRA::resize(rPadding, paddingSize);
        ALGEBRA::resize(encErrPadding, paddingSize);
        ALGEBRA::resize(sk2Padding, paddingSize);
        ALGEBRA::resize(kGenErrPadding, paddingSize);
        sk1 = decErr = r = sk2 = nullptr;
        pt1 = pt2 = nullptr;
    }
};

// Proof of decryption. We assume that the ProverData,VerifierData are
// already initialized, and that ProverData contains the padded sk1
// and VerifierData contains a commitment to it.
void proveDecryption(ProverData& pd, const ALGEBRA::SVector& ptxt,
        const ALGEBRA::EVector& noise, const ALGEBRA::EMatrix& ctMat,
        const ALGEBRA::EVector& ctVec);

void verifyDecryption(VerifierData& vd, // vd has all the commitments
        const ALGEBRA::EMatrix& ctMat, const ALGEBRA::EVector& ctVec);

// Proof of encryption
void proveEncryption(ProverData& pd, const ALGEBRA::SVector& ptxt,
        const ALGEBRA::EVector& rnd, const ALGEBRA::EVector& noise,
        const ALGEBRA::EVector& ct1, const ALGEBRA::EVector& ct2);

void verifyEncryption(VerifierData& vd,
        const ALGEBRA::EVector& ct1, const ALGEBRA::EVector& ct2);

// Proof of key-generation. pkNum is index of the pkey in the GlobalKey
void proveKeyGen(ProverData& pd, const ALGEBRA::EVector& sk,
        const ALGEBRA::EVector& noise, int pkNum);

void verifyKeyGen(VerifierData& vd, int pkNum);

// Proof of correct re-sharing. It is assumed that pt1, pt2
// are already initialized in the ps structure
void proveReShare(ProverData& pd, const TOOLS::EvalSet& recSet);

void verifyKeyGen(VerifierData& vd, const TOOLS::EvalSet& recSet);

// Proof of approximate smallness (of all except the plaintext variables)
void proveSmallness(ProverData& pd);

void verifySmallness(VerifierData& vd);







/****** utility functions *******/

// record the secret variables in a DLPROOFS::PtxtVec map as needed
// for the Bulletproof protocols
void addToWitness(DLPROOFS::PtxtVec& witness, int idx, const ALGEBRA::SVector& v);
void addToWitness(DLPROOFS::PtxtVec& witness, int idx, const ALGEBRA::EVector& v);

// compute the vector (1,x,x^2,...,x^{len-1})
void powerVector(ALGEBRA::SVector& vec, const ALGEBRA::Scalar& x, int len);
void powerVector(ALGEBRA::EVector& vec, const ALGEBRA::Element& x, int len);

// Commit to a slice of the vector
Point commit(const ALGEBRA::SVector& v, size_t genIdx,
             const std::vector<Point>& Gs, CRV25519::Scalar& r,
             int fromIdx=0, int toIdx=-1);
Point commit(const ALGEBRA::EVector& v, size_t genIdx,
             const std::vector<Point>& Gs, CRV25519::Scalar& r,
             int fromIdx=0, int toIdx=-1);

// Compute the norm-squared of v as a bigInt (no modular reduction)
ALGEBRA::BigInt normSquaredBI(ALGEBRA::BIVector& vv);
ALGEBRA::BigInt normSquaredBigInt(const ALGEBRA::SVector& v);
ALGEBRA::BigInt normSquaredBigInt(const ALGEBRA::EVector& v);
ALGEBRA::BigInt normSquaredBigInt(const ALGEBRA::Element* v, size_t len);

// Add to v four integers a,b,c,d such that the result
// (v | a,b,c,d) has norm exactly equal to the bound
void pad2exactNorm(const ALGEBRA::SVector& v,
         ALGEBRA::SVector& padding, const ALGEBRA::BigInt& bound);
void pad2exactNorm(const ALGEBRA::EVector& v,
        ALGEBRA::EVector& padding, const ALGEBRA::BigInt& bound);
void pad2exactNorm(const ALGEBRA::Element* v, size_t len,
        ALGEBRA::Element* padSpace, const ALGEBRA::BigInt& bound);

// Expand a constraint a*x with a in GF(p^e) to e constrints over scalars,
// namely store in e constraints in e variables the e-by-e matrix representing
// the multiply-by-a matrix over the mase field.
// The variables in the constraints are idx,idx+1,... I.e., the constraints
// are idx -> a.freeTerm, idx+1 -> a.coeffOf(X), idx+2 -> a.coeffOf(X^2),...
// These functions assume that GF(p^e) is represented modulo X^e +1.
void expandConstraints(LinConstraint* constrs, int idx, const ALGEBRA::Element& a);
void expandConstraints(LinConstraint* constrs, int idx,
                       const ALGEBRA::EVector& v, int from=0, int to=-1);

// This function is for the case where the secret variables are from Z_p,
// namely we have the constraint <x,v>=b over GF(p^e), but x iv over Z_p.
void makeConstraints(LinConstraint* constrs, int idx,
                     const ALGEBRA::EVector& v, int from=0, int to=-1);

// This function sets the equalsTo field for the ell constraints
// corresponding to the ell scalars representing the element r
void setEqsTo(LinConstraint* constrs, const ALGEBRA::Element& e);

// Useful routines for printing ZZ_p's with small magnitude

inline ALGEBRA::BigInt balanced(const CRV25519::Scalar& s) {
    ALGEBRA::Scalar as;
    conv(as,s);
    return ALGEBRA::balanced(as);
}

inline std::ostream& prettyPrint(std::ostream& st, const DLPROOFS::PtxtVec& v) {
    st << "[";
    for (auto& x : v) {
        st << x.first << "->" << balanced(x.second) << ", ";
    }
    return (st << "]");
}
inline std::ostream& prettyPrint(std::ostream& st, const DLPROOFS::LinConstraint& c) {
    prettyPrint(st<<"{", c.terms) << ", " << balanced(c.equalsTo) << "}";
    return st;
}
inline std::ostream& prettyPrint(std::ostream& st, const DLPROOFS::QuadConstraint& c) {
    st<<"{[";
    for (auto i : c.indexes) { st << i<< " "; }
    st << "], " << balanced(c.equalsTo) << "}";
    return st;
}


} // end of namespace REGEVENC
#endif // ifndef _REGEVPROOFS_HPP_
