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
#include "utils.hpp"

//#define DEBUGGING

namespace REGEVENC {
using CRV25519::Point, DLPROOFS::PedersenContext, TOOLS::SharingParams,
    DLPROOFS::MerlinBPctx, DLPROOFS::LinConstraint, DLPROOFS::QuadConstraint;
// NOTE: REGEVENC::Scalar is not the same as CRV25519::Scalar


inline constexpr int PAD_SIZE=4; // add 4 scalars to pad to a specific sum-of-squares

// We break the decryption error vector into subvectors, each with this many scalars
#if 1 //ifndef DEBUGGING
inline constexpr int JLDIM = 256;  // Target dimension of Johnson–Lindenstrauss
inline constexpr int SQRT_JL =16;
inline constexpr int LINYDIM=128;  // Target dimension in approximate l-infty proofs
#else
inline constexpr int JLDIM = 16;
inline constexpr int SQRT_JL =4;
inline constexpr int LINYDIM =8;
#endif

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

    // Size bounds for the various compressed (JL) vectors
    ALGEBRA::BigInt B_dNoise; // compressed decryption noise
    ALGEBRA::BigInt B_sk;     // compressed secret-key
    ALGEBRA::BigInt B_r;      // comressed encryption randomness
    ALGEBRA::BigInt B_eNoise1;// compressed small encryption noise
    ALGEBRA::BigInt B_eNoise2;// compressed large encryption noise
    ALGEBRA::BigInt B_kNoise; // compressed keygen noise
    ALGEBRA::BigInt B_smallness;// Used in the approximate smallness protocol
    int smlnsBits;  // The bitsize of B_smallness above
    ALGEBRA::BigInt radix; // the radix used to split large integers into digits

    std::vector<Point> Gs, Hs; // lists of generators

    // For most vectors, we have the vector itself (e.g., sk2), the
    // compressed vector (e.g., sk2Comp) and the padding that the prover
    // computes to pad the compressed vector to some pre-determined size
    // (e.g., sk2Pad). The ones without compression and padding are
    // sk1,pt1,pt2,y. For the noise vectors we only need the indexes
    // of the compressed vector and padding, not the original vector
    // (since there is no Pedersen commitment to that vector).

    // indexes into the generator list
    int pt1Idx, sk1Idx, dCompHiIdx, dPadHiIdx, dCompLoIdx, dPadLoIdx, // dec
        pt2Idx, rIdx, rCompIdx, rPadIdx, eComp1HiIdx, ePad1HiIdx, eComp1LoIdx,
        ePad1LoIdx, eComp2HiIdx, ePad2HiIdx, eComp2LoIdx, ePad2LoIdx,  // enc
        sk2Idx, sk2CompIdx, sk2PadIdx,
        kCompHiIdx, kPadHiIdx, kCompLoIdx, kPadLoIdx,               // keygen
        yIdx, wIdx;                        // smallness proof and aggregation

    // Commitments to different variables. The quadratic equations require
    // a double-commitment with respect to both the G and H generators,
    // while the linear constraints only need commitment wrt the Gs.

    Point pt1Com, sk1Com, dCompHiCom, dPadHiCom, dCompLoCom, dPadLoCom,// dec
        pt2Com, rCom, rCompCom, rPadCom, eComp1HiCom, ePad1HiCom, eComp1LoCom,
        ePad1LoCom, eComp2HiCom, ePad2HiCom, eComp2LoCom, ePad2LoCom,  // enc
        sk2Com, sk2CompCom, sk2PadCom,
        kCompHiCom, kPadHiCom, kCompLoCom, kPadLoCom,               // keygen
        yCom, wCom;                        // smallness proof and aggregation

    // A list of all the linear and quadratic constraints
    std::vector<DLPROOFS::LinConstraint> linConstr;
    std::vector<DLPROOFS::QuadConstraint> normConstr;

    // pointers into the above vectors of constraints
    static constexpr int dLinIdx=0,   // dec
        eLin1Idx=GlobalKey::ell,
        eLin2Idx=2*GlobalKey::ell,
        rLinIdx=3*GlobalKey::ell,     // enc
        kLinIdx=4*GlobalKey::ell,
        sk2LinIdx=5*GlobalKey::ell,   // keygen,
        smlnsLinIdx=6*GlobalKey::ell, // smallness
        reShrLinIdx=7*GlobalKey::ell; // resharing
    static constexpr int dHiQuadIdx=0, dLoQuadIdx=1, rQuadIdx=2,
        e1HiQuadIdx=3, e1LoQuadIdx=4, e2HiQuadIdx=5, e2LoQuadIdx=6,
        sk2QuadIdx=7, kHiQuadIdx=8, kLoQuadIdx=9;

    ALGEBRA::EVector z; // the masked vector z from the proof of smallness

    // Set the indexes to their default values
    void setIndexes();
    void computeGenerators();

    // Reset when preparing for a new proof at the prover's site
    void prepareForNextProof() {
        std::swap(sk1Idx,sk2Idx);
        sk1Com = sk2Com; // copy commitment to the previous sk wrt the Gs

        // zero out all the commitments and constraints
        pt1Com= dCompHiCom= dPadHiCom= dCompLoCom= dPadLoCom= pt2Com= // dec
        rCom= rCompCom= rPadCom= eComp1HiCom= ePad1HiCom= eComp1LoCom=
        ePad1LoCom= eComp2HiCom= ePad2HiCom= eComp2LoCom= ePad2LoCom= // enc
        sk2Com= sk2CompCom= sk2PadCom=
        kCompHiCom= kPadHiCom= kCompLoCom= kPadLoCom=              // keygen
        yCom= wCom = Point::identity();

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

    // commitment randomness
    CRV25519::Scalar pt1Rnd, sk1Rnd,
        dCompHiRnd, dPadHiRnd, dCompLoRnd, dPadLoRnd,                  // dec
        pt2Rnd, rRnd, rCompRnd, rPadRnd, eComp1HiRnd, ePad1HiRnd, eComp1LoRnd,
        ePad1LoRnd, eComp2HiRnd, ePad2HiRnd, eComp2LoRnd, ePad2LoRnd,  // enc
        sk2Rnd, sk2CompRnd, sk2PadRnd,
        kCompHiRnd, kPadHiRnd, kCompLoRnd, kPadLoRnd,               // keygen
        yRnd, wRnd;                    // smallness proof and aggregation

    // The compressed vectors, concatenated
    ALGEBRA::EVector compressed;

    // The witnesses for the linear and quadratic constraints

    DLPROOFS::PtxtVec linWitness;
    DLPROOFS::PtxtVec quadWitnessG, quadWitnessH;

    // Reset when preparing for a new proof at the prover's site
    void prepareForNextProof() {
        vd->prepareForNextProof(); // reset the public data
        sk1Rnd = sk2Rnd; // randomness of commitment to secret key wrt Gs
    }

    ProverData() = default;    
    ProverData(VerifierData& verData): vd(&verData) {
        compressed.SetLength(10*(JLDIM+PAD_SIZE)/ALGEBRA::scalarsPerElement());
   }
};

// Proof of decryption. We assume that the ProverData,VerifierData are
// already initialized, and that ProverData contains sk1 and VerifierData
// contains a commitment to it.
void proveDecryption(ProverData& pd, 
    const ALGEBRA::EMatrix& ctMat, const ALGEBRA::EVector& ctVec,
    const ALGEBRA::SVector& ptxt, const ALGEBRA::EVector& skey,
    const ALGEBRA::EVector& noise);

void verifyDecryption(VerifierData& vd, // vd has all the commitments
        const ALGEBRA::EMatrix& ctMat, const ALGEBRA::EVector& ctVec);

// Proof of encryption
void proveEncryption(ProverData& pd,
        const ALGEBRA::EVector& ct1, const ALGEBRA::EVector& ct2, 
        const ALGEBRA::SVector& ptxt, const ALGEBRA::EVector& rnd,
        const ALGEBRA::EVector& noise1,const ALGEBRA::EVector& noise2);

void verifyEncryption(VerifierData& vd,
        const ALGEBRA::EVector& ct1, const ALGEBRA::EVector& ct2);

// Proof of key-generation. pkNum is index of the pkey in the GlobalKey
void proveKeyGen(ProverData& pd, int pkNum,
        const ALGEBRA::EVector& sk, const ALGEBRA::EVector& noise);

void verifyKeyGen(VerifierData& vd, int pkNum);

// Proof of correct re-sharing. It is assumed that pt1, pt2
// are already initialized in the ps structure
void proveReShare(ProverData& pd, const ALGEBRA::SVector& lagrange,
        const ALGEBRA::SVector& pt1, const ALGEBRA::SVector& pt2);
void verifyReShare(VerifierData& vd, const ALGEBRA::SVector& lagrange);
    // TOOLS::EvalSet from shamir.hpp describes the reconstruction set

// Proof of approximate smallness (of all except the compressed vectors)
void proveSmallness(ProverData& pd);
void verifySmallness(VerifierData& vd);

struct ReadyToVerify {
    // The linear and quadratic constraints and commitments
    DLPROOFS::LinConstraint linCnstr;
    Point linCom;
    DLPROOFS::QuadConstraint quadCnstr;
    Point quadCom;

    // The offset used for the G, H witnesses in the quadratic proof
    DLPROOFS::PtxtVec deltaG, deltaH;

    // temporary variables used in aggregating the proofs
    std::vector<CRV25519::Scalar> rVec, uVec;
    DLPROOFS::PtxtVec as, bs;

    // Flattened versions of the statements and generators
    std::vector<Point> linGs;
    std::vector<CRV25519::Scalar> linStmnt;

    std::vector<Point> quadGs;
    std::vector<Point> quadHs;
    std::vector<CRV25519::Scalar> offstG;
    std::vector<CRV25519::Scalar> offstH;

    void aggregateVerifier1(VerifierData& vd);
    void aggregateVerifier2(VerifierData& vd);

    void flattenLinVer(VerifierData& vd);
    void flattenQuadVer(VerifierData& vd);
};
struct ReadyToProve : public ReadyToVerify {
    // Randomness used for linCom and quadCom
    CRV25519::Scalar lComRnd, qComRnd;

    // Flattened versions of the witnesses
    std::vector<CRV25519::Scalar> linWtns;
    std::vector<CRV25519::Scalar> quadWtnsG, quadWtnsH;

    void aggregateProver(ProverData& pd);
    void flattenLinPrv(ProverData& pd);
    void flattenQuadPrv(ProverData& pd);
};


/****** utility functions *******/

// Compute the vector (1,x,x^2,...,x^{len-1})
void powerVector(ALGEBRA::SVector& vec, const ALGEBRA::Scalar& x, int len);
void powerVector(ALGEBRA::EVector& vec, const ALGEBRA::Element& x, int len);
void powerVector(std::vector<CRV25519::Scalar>& vec, const CRV25519::Scalar& x, int len);

// Commit to a slice of the vector
Point commit(const ALGEBRA::SVector& v, size_t genIdx,
             const std::vector<Point>& Gs, CRV25519::Scalar& r,
             int fromIdx=0, int toIdx=-1);
Point commit(const ALGEBRA::EVector& v, size_t genIdx,
             const std::vector<Point>& Gs, CRV25519::Scalar& r,
             int fromIdx=0, int toIdx=-1);
// commit to the same xes wrt both Gs and Hs
Point commit2(const ALGEBRA::EVector& v, size_t genIdx,
             const std::vector<Point>& Gs, const std::vector<Point>& Hs,
             CRV25519::Scalar& r, int fromIdx=0, int toIdx=-1);

// Add to v four integers a,b,c,d such that the result
// (v | a,b,c,d) has norm exactly equal to the bound
void pad2exactNorm(const ALGEBRA::SVector& v,
         ALGEBRA::SVector& padding, const ALGEBRA::BigInt& bound);
void pad2exactNorm(const ALGEBRA::EVector& v,
        ALGEBRA::EVector& padding, const ALGEBRA::BigInt& bound);
void pad2exactNorm(const ALGEBRA::Element* v, size_t len,
        ALGEBRA::Element* padSpace, const ALGEBRA::BigInt& bound);

// The expand functions below assume that GF(p^ell) is represented
// modulo X^ell +1.

// Expand a constraint a*x with a in GF(p^ell) to e constrints over scalars,
// namely store in 'constrs' ell constraints in ell variables, representing
// the ell-by-ell scalar matrix for multiply-by-a. The variables in these
// constraints are indexed by idx,idx+1,... For example, the constraints
// for the 1st row has coeffs: idx->a.freeTerm, idx+1 -> a.coeffOf(X),...
void expandConstraints(LinConstraint* constrs, int idx, const ALGEBRA::Element& a);

// Expand each of the constraints v[i]*x with successive indexes
void expandConstraints(LinConstraint* constrs, int idx,
                       const ALGEBRA::EVector& v, int from=0, int to=-1);

// This function is for the case where the secret variables are from Z_p,
// namely we have the constraint <x,v>=b over GF(p^ell), but x is over Z_p.
void makeConstraints(LinConstraint* constrs, int idx,
                     const ALGEBRA::EVector& v, int from=0, int to=-1);

// This function sets the equalsTo field for the ell constraints
// corresponding to the ell scalars representing the element e
void setEqsTo(LinConstraint* constrs, const ALGEBRA::Element& e);

bool checkQuadCommit(DLPROOFS::QuadConstraint& c,
    const Point& com, const Point& padCom, const CRV25519::Scalar& rnd,
    const CRV25519::Scalar& padRnd, DLPROOFS::PtxtVec& witness, PedersenContext* ped);
bool checkLinCommit(DLPROOFS::PtxtVec& pv,
    const Point& com, const CRV25519::Scalar& rnd,
    DLPROOFS::PtxtVec& witness, PedersenContext* ped);

} // end of namespace REGEVENC
#endif // ifndef _REGEVPROOFS_HPP_
