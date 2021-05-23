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
//#define DEBUGGING
#include <cassert>
#include <chrono>
#include "utils.hpp"
#include "regevProofs.hpp"
#ifdef DEBUGGING
#include <NTL/RR.h>
#endif

using namespace ALGEBRA;

namespace REGEVENC {
using CRV25519::Point, DLPROOFS::PedersenContext,
    DLPROOFS::MerlinBPctx, DLPROOFS::LinConstraint, DLPROOFS::QuadConstraint;
// NOTE: REGEVENC::Scalar is not the same as CRV25519::Scalar

// Proof of decryption. We assume that the ProverData,VerifierData are
// already initialized, and that ProverData contains sk1, VerifierData
// has a commitment to sk1, and ProverData has the commitment randomness.
void proveDecryption(ProverData& pd, const SVector& ptxt,
        const EVector& noise, const EMatrix& ctMat, const EVector& ctVec)
{
    VerifierData& vd = *(pd.vd);
    pd.pt1 = (SVector*) &ptxt;
    pd.decErr = (EVector*) &noise;
#ifdef DEBUGGING
    std::cout << "|decNoise|_infty=2^"<<log2BI(lInftyNorm(noise))
        << ", |decNoise|^2=2^"<<log2BI(normSquaredBigInt(noise))
        <<", B_decNoise=2^"<<log2BI(vd.B_decNoise)<<std::endl;
#endif
    // commitment to decrypted plaintext
    vd.pt1Com = commit(ptxt, vd.pt1Idx, vd.Gs, pd.pt1Rnd);
    vd.mer->processPoint("RegevDecPtxt", vd.pt1Com);

    // commitments to decryption noise subvectors
    int elementsPerSubvec= DEC_ERRV_SZ / scalarsPerElement();
    int paddingElements = PAD_SIZE / scalarsPerElement();

    // ComPute the noise padding, then commit to the noise variables
    // and their padding, each wrt both the Gs and the Hs
    for (int i=0; i<vd.nDecSubvectors; i++) {
        int elementIdx = i*elementsPerSubvec;
        int scalarIdx = vd.decErrIdx + i*DEC_ERRV_SZ;
        int paddingIdx = i*paddingElements;
        int scalarPadIdx = vd.decErrPadIdx + i*PAD_SIZE;

        // pad with four scalars to get l2 norm=B_decNoise
        pad2exactNorm(&(noise[elementIdx]), elementsPerSubvec,
                      &(pd.decErrPadding[paddingIdx]), vd.B_decNoise);

        // Commit to the noise variables, wrt both the G's and H's
        auto& com2Noise = vd.decErrCom[i];
        auto& randOfNoise = pd.decErrRnd[i];
        com2Noise[0] = commit(noise, scalarIdx, vd.Gs, randOfNoise[0],
                              elementIdx, elementIdx+elementsPerSubvec);
        com2Noise[1] = commit(noise, scalarIdx, vd.Hs, randOfNoise[1],
                              elementIdx, elementIdx+elementsPerSubvec);

        // commit to the padding, wrt both the G's and the H's
        auto& com2Pad = vd.decErrPadCom[i];
        auto& randOfPad = pd.decErrPadRnd[i];
        com2Pad[0] = commit(pd.decErrPadding, scalarPadIdx, vd.Gs, randOfPad[0],
                            paddingIdx, paddingIdx+paddingElements);
        com2Pad[1] = commit(pd.decErrPadding, scalarPadIdx, vd.Hs, randOfPad[1],
                            paddingIdx, paddingIdx+paddingElements);
    }

    // include these commitments in the Merlin transcript
    for (int i=0; i<vd.nDecSubvectors; i++) {
        auto& com2Noise = vd.decErrCom[i];
        auto& com2Pad = vd.decErrPadCom[i];
        vd.mer->processPoint("RegevDecNoise"+std::to_string(i), com2Noise[0]);
        vd.mer->processPoint(std::string(), com2Noise[1]);
        vd.mer->processPoint(std::string(), com2Pad[0]);
        vd.mer->processPoint(std::string(), com2Pad[1]);
    }
    // A challenge scalar x, defines the vector xvec=(1,x,x^2,...)
    Element x = vd.mer->newElement("RegevDec");
    EVector xvec;
    powerVector(xvec, x, ptxt.length()); // the vector xvec=(1,x,x^2,...)

    // Record the linear constraints
    //            <sk,ctMat*xvec> +<ptxt,g*xvec> +<noise,xvec> = <ctVec,xvec>

    // The element <ctVec,cvec>
    setEqsTo(&(vd.linConstr[0]), innerProduct(ctVec, xvec));

    // expand <sk,ctMat*xvec> 
    EVector yvec = ctMat * xvec;
    expandConstraints(&(vd.linConstr[0]), vd.sk1Idx, yvec);

    // Expand <noise,xvec>
    expandConstraints(&(vd.linConstr[0]), vd.decErrIdx, xvec);

    // Constraints for <ptxt,g*xvec>, where ptxt is a Z_p vector, not GF(p^e)
    makeConstraints(&(vd.linConstr[0]), vd.pt1Idx, xvec*vd.gk->g());

    // Record the norm constraints |paddedNoise[i]|^2 =B_decNoise^2 forall i
    // The indexes for each of them are set as follows: all the sub-vectors
    // together make the two intervals: 
    //  - for the vectors themselves [decErrIdx1, decErrIdx1+decErrLen1-1]
    //  - for the padding            [decErrIdx2, decErrIdx2+decErrLen2-1]
    // Each sub-vector has one slice from from each interval, of sizes
    // DEC_ERRV_SZ = decErrLen1/nDecSubvectors for the vectors, and
    // PAD_SIZE = decErrLen2/nDecSubvectors for the padding.

    auto normSquared = vd.B_decNoise*vd.B_decNoise;
    for (int i=0; i<vd.nDecSubvectors; i++) { // go over the sub-vectors
        int start1 = vd.decErrIdx + i*DEC_ERRV_SZ;
        int start2 = vd.decErrPadIdx + i*PAD_SIZE;

        auto& normConstr = vd.normConstr[i];
        for (int j=0; j<DEC_ERRV_SZ; j++)
            normConstr.indexes.insert(normConstr.indexes.end(), start1+j);
        for (int j=0; j<PAD_SIZE; j++)
            normConstr.indexes.insert(normConstr.indexes.end(), start2+j);

        // Records the norm-squared itself
        conv(normConstr.equalsTo, normSquared); // convert to CRV25519::Scalar
    }

#ifdef DEBUGGING
    assert(ptxt.length()==vd.gk->tee);
    assert(xvec.length()==ptxt.length());
    assert(DEC_ERRV_SZ % scalarsPerElement() == 0);
    assert(PAD_SIZE % scalarsPerElement() == 0);
    assert(elementsPerSubvec * vd.nDecSubvectors == noise.length());

    // Start by checking that indeed this constraint holds
    Element sum = innerProduct((*pd.sk1), yvec)
        + innerProduct(noise, xvec) + innerProduct(ptxt, xvec*vd.gk->g());
    assert(sum==innerProduct(ctVec, xvec));

    // verify the constraints
    DLPROOFS::PtxtVec pVec;
    pd.assembleFullWitness(pVec);
    for (int i=0; i<scalarsPerElement(); i++) {
        auto& linConstr = vd.linConstr[i];
        if (!checkConstraintLoose(linConstr, pVec)) {
            std::cout << "  constraints for <noise,xvec> #"<<i<<" failed\n  ";
            prettyPrint(std::cout, linConstr) << std::endl;
            std::cout << "  noise(idx="<<vd.decErrIdx<<")="<<ALGEBRA::balanced(noise)<<std::endl;
            std::cout << "  xvec="<<ALGEBRA::balanced(xvec)<<std::endl;
            exit(0);
        }
    }
    for (int i=0; i<vd.nDecSubvectors; i++) { // go over the sub-vectors
        auto& normConstr = vd.normConstr[i];
        if (!checkConstraintLoose(normConstr, pVec, pVec)) {
            std::cout << "norm constraint #"<<i<<" failed\n";
            prettyPrint(std::cout, normConstr) << std::endl;
            exit(0);
        }
    }
#endif
}

// Proof of encryption. We assume that the ProverData,VerifierData are
// already initialized.
void proveEncryption(ProverData& pd, const ALGEBRA::SVector& ptxt,
        const ALGEBRA::EVector& rnd, const ALGEBRA::EVector& noise,
        const ALGEBRA::EVector& ct1, const ALGEBRA::EVector& ct2) {
    VerifierData& vd = *(pd.vd);
    pd.pt2 = (ALGEBRA::SVector*) &ptxt;
    pd.r   = (ALGEBRA::EVector*) &rnd;

    // commitment to encrypted plaintext
    vd.pt2Com = commit(*pd.pt2, vd.pt2Idx, vd.Gs, pd.pt2Rnd);
    vd.mer->processPoint("RegevEncPtxt", vd.pt2Com);

#if 0 // ifdef DEBUGGING
    BigInt one(1);
    BigInt tmp = one<<(vd.gk->rho);
    BigInt tmp1 = one<<(vd.gk->sigmaEnc1);
    BigInt tmp2 = one<<(vd.gk->sigmaEnc2);
    NTL::RR rndBound = NTL::conv<NTL::RR>(vd.gk->emm * vd.gk->ell* tmp*tmp);
    NTL::RR errBound = NTL::conv<NTL::RR>(
        vd.gk->kay*vd.gk->ell*tmp1*tmp1 + vd.gk->enn*vd.gk->ell*tmp2*tmp2);
    NTL::RR ratioNoise = NTL::conv<NTL::RR>(normSquaredBigInt(noise))/errBound;
    NTL::RR ratioRnd = NTL::conv<NTL::RR>(normSquaredBigInt(rnd))/rndBound;
    std::cout << "|r|="<<sqrt(ratioRnd)<<"*mu_r, |e|="<<sqrt(ratioNoise)<<"*u_e\n";
#endif
    // Prepare for choosing the trenary matrix R=(R1|R2) and setting
    // noise2 = R*noise = R1*noiseA + R2*noiseB.
    EVector noiseA; resize(noiseA, vd.gk->kay); // the two parts of the noise vector
    for (int i=0; i<vd.gk->kay; i++) noiseA[i]=noise[i];
    EVector noiseB; resize(noiseB, vd.gk->enn);
    for (int i=0; i<vd.gk->enn; i++) noiseB[i]=noise[i +vd.gk->kay];
    // FIXME: Implement R*slice so we don't need to copy these two slices
    //        into separate vectors

    TernaryEMatrix R1, R2, R3;
    int nRrows = JLDIM/scalarsPerElement();

    // Commit to the randomness wrt the G's. Note that we will re-set
    // the randomness in this commitment as needed for rejection sampling.
    vd.rCom = commit(rnd, vd.rIdx, vd.Gs, pd.rRnd);

    // while (true) {
    for (int nTrials=1; true; nTrials++) {
        if (nTrials > 30) {
            throw std::runtime_error("proveEncryption: too many retries choosing R");
        }
        auto merBkp = *(vd.mer);
        merBkp.processPoint("RegevencRnd", vd.rCom);

        // Get the challenge matrices, and set noise' = (R1|R2)*noise
        merBkp.newTernaryEMatrix("RegevEncR1", R1, nRrows, vd.gk->kay);
        merBkp.newTernaryEMatrix("RegevEncR2", R2, nRrows, vd.gk->enn);
        merBkp.newTernaryEMatrix("RegevEncR3", R3, nRrows, vd.gk->emm);

        // Compute the lower-dimenstion r2 and noise2
        pd.encErr = (R1*noiseA) + (R2*noiseB);
        pd.r2 = R3*(*pd.r);
#ifdef DEBUGGING
        {BigInt e1 = normSquaredBigInt(noise);
        BigInt e2 = normSquaredBigInt(pd.encErr);
        std::cout << "encryption: |e|^2=2^"<< log2BI(e1)
            << ", |e'|^2=2^"<<log2BI(e2)
            <<", B_encNoise^2=2^"<<(2*log2BI(vd.B_encNoise))<<std::endl;
        e1 = normSquaredBigInt(rnd);
        e2 = normSquaredBigInt(pd.r2);
        std::cout << "            |r|^2=2^"<< log2BI(e1)
            << ", |r'|^2=2^"<<log2BI(e2)
            <<", B_encRnd^2=2^"<<(2*log2BI(vd.B_encRnd))<<std::endl;}
#endif
       if (normSquaredBigInt(pd.encErr) <= vd.B_encNoise * vd.B_encNoise
            && normSquaredBigInt(pd.r2) <= vd.B_encRnd * vd.B_encRnd) {
             *(vd.mer) = merBkp;
            break;
        }
        // if r2 or noise2 is too large, update the commitment and try again
        pd.rRnd += CRV25519::Scalar().setInteger(1);
        vd.rCom += Point::base();
    }

    // pad r2 with four scalars to get l2 norm=B_encRnd, commit to it wrt
    // both the G's and H's
    pad2exactNorm(pd.r2, pd.r2Padding, vd.B_encRnd);
    vd.r2Com[0] = commit(pd.r2, vd.r2Idx, vd.Gs, pd.r2Rnd[0]);
    vd.r2Com[1] = commit(pd.r2, vd.r2Idx, vd.Hs, pd.r2Rnd[1]);
    vd.r2PadCom[0] = commit(pd.r2Padding, vd.r2PadIdx, vd.Gs, pd.r2PadRnd[0]);
    vd.r2PadCom[1] = commit(pd.r2Padding, vd.r2PadIdx, vd.Hs, pd.r2PadRnd[1]);

    // pad noise2 with four scalars to get l2 norm=B_encNoise, and commit to
    // the padding wrt both the G's and H's
    pad2exactNorm(pd.encErr, pd.encErrPadding, vd.B_encNoise);
    vd.encErrCom[0] = commit(pd.encErr, vd.encErrIdx, vd.Gs, pd.encErrRnd[0]);
    vd.encErrCom[1] = commit(pd.encErr, vd.encErrIdx, vd.Hs, pd.encErrRnd[1]);
    vd.encErrPadCom[0] = commit(pd.encErrPadding, vd.encErrPadIdx,
                              vd.Gs, pd.encErrPadRnd[0]);
    vd.encErrPadCom[1] = commit(pd.encErrPadding, vd.encErrPadIdx,
                              vd.Hs, pd.encErrPadRnd[1]);

    // include these commitments in the Merlin transcript
    vd.mer->processPoint("RegevencRnd2", vd.r2Com[0]);
    vd.mer->processPoint(std::string(), vd.r2Com[1]);
    vd.mer->processPoint(std::string(), vd.r2PadCom[0]);
    vd.mer->processPoint(std::string(), vd.r2PadCom[1]);

    vd.mer->processPoint("RegevEncNoise", vd.encErrCom[0]);
    vd.mer->processPoint(std::string(), vd.encErrCom[1]);
    vd.mer->processPoint(std::string(), vd.encErrPadCom[0]);
    vd.mer->processPoint(std::string(), vd.encErrPadCom[1]);

    // Record the 1st encryption linear constraint
    //     <x*R𝟏*𝐀+x*R2*B,r> + <x,noise2> + <g*x*R2,ptxt> = <x,R1*ct1+R2*ct2>

    // A challenge element x, defines the vector xvec=(1,x,x^2,...)
    EVector xvec;
    Element x = vd.mer->newElement("RegevEncChallenge");
    powerVector(xvec, x, pd.encErr.length());

    // The term <x, R1*ct1+R2*ct2>
    Element eqTo = innerProduct(xvec, (R1*ct1)+(R2*ct2));
    setEqsTo(vd.encLinCnstr, eqTo);

    // The term <x*R𝟏*𝐀+x*R2*B, r> 
    EVector xR2 = xvec*R2;
    EVector frstTerm = (xvec*R1)*(vd.gk->A) + xR2*(vd.gk->B);
    expandConstraints(vd.encLinCnstr, vd.rIdx, frstTerm);

    // The term <x,noise2>
    expandConstraints(vd.encLinCnstr, vd.encErrIdx, xvec);

    // The term <g*x*R2, ptxt> 
    makeConstraints(vd.encLinCnstr, vd.pt2Idx, vd.gk->g()*xR2);

    // Record the 2nd encryption linear constraint, <x2,r2> -<x2*R3,r> =0

    EVector xvec2;
    Element x2 = vd.mer->newElement("RegevEncChallenge2");
    powerVector(xvec2, x2, pd.r2.length());

    // The eqsTo element is zero
    setEqsTo(vd.encLinCnstr2, Element());

    // The term -<x2*R3,r>
    expandConstraints(vd.encLinCnstr2, vd.rIdx, -xvec2*R3);

    // The term <x2,r2> 
    expandConstraints(vd.encLinCnstr2, vd.r2Idx, xvec2);

    // Record the norm constraints |paddedRnd|^2=B_encRnd^2 and
    // |paddedNoise2|^2 =B_encNoise^2.
    
    for (int i=0; i<pd.r2.length()*scalarsPerElement(); i++)
        vd.rQuadCnstr->indexes.insert(vd.rQuadCnstr->indexes.end(), vd.r2Idx+i);
    for (int i=0; i<PAD_SIZE; i++)
        vd.rQuadCnstr->indexes.insert(vd.rQuadCnstr->indexes.end(), vd.r2PadIdx+i);
    // The norm-squared itself, converted to CRV25519::Scalar
    conv(vd.rQuadCnstr->equalsTo, vd.B_encRnd * vd.B_encRnd);

    for (int i=0; i<pd.encErr.length()*scalarsPerElement(); i++)
        vd.encErrQuadCnstr->indexes.insert(vd.encErrQuadCnstr->indexes.end(), vd.encErrIdx+i);
    for (int i=0; i<PAD_SIZE; i++)
        vd.encErrQuadCnstr->indexes.insert(vd.encErrQuadCnstr->indexes.end(), vd.encErrPadIdx+i);
    // The norm-squared itself, converted to CRV25519::Scalar
    conv(vd.encErrQuadCnstr->equalsTo, vd.B_encNoise * vd.B_encNoise);

#ifdef DEBUGGING
    assert( innerProduct(frstTerm, *pd.r) + innerProduct(xvec,pd.encErr)
             + innerProduct(vd.gk->g()*xR2, *pd.pt2) == eqTo );
    assert( innerProduct(xvec2, pd.r2) == innerProduct(xvec2*R3,*pd.r) );

    // verify the constraints
    DLPROOFS::PtxtVec pVec;
    pd.assembleFullWitness(pVec);
    for (int i=0; i<scalarsPerElement(); i++) { // check the linear constraints
        auto& linConstr = vd.encLinCnstr[i];
        if (!checkConstraintLoose(linConstr, pVec)) {
            std::cout << "constraints for encryption #"<<i<<" failed\n  ";
            prettyPrint(std::cout, linConstr) << std::endl;
            //std::cout << "  ptxt(idx="<<vd.pt1Idx<<")="<<balanced(ptxt)<<std::endl;
            //std::cout << "  xvec*g="<<balanced(xvec2)<<std::endl;
            exit(0);
        }
    }
    for (int i=0; i<scalarsPerElement(); i++) { // check the linear constraints
        auto& linConstr = vd.encLinCnstr2[i];
        if (!checkConstraintLoose(linConstr, pVec)) {
            std::cout << "constraints2 for encryption #"<<i<<" failed\n  ";
            prettyPrint(std::cout, linConstr) << std::endl;
            //std::cout << "  ptxt(idx="<<vd.pt1Idx<<")="<<balanced(ptxt)<<std::endl;
            //std::cout << "  xvec*g="<<balanced(xvec2)<<std::endl;
            exit(0);
        }
    }
    if (!checkConstraintLoose(*vd.rQuadCnstr, pVec, pVec)) { // randomness norm
        std::cout << "norm constraint for r failed\n";
        prettyPrint(std::cout, *vd.rQuadCnstr) << std::endl;
        prettyPrint(std::cout<<"pVec=", pVec) << std::endl;
        exit(0);
    }
    if (!checkConstraintLoose(*vd.encErrQuadCnstr, pVec, pVec)) { // noise norm
        std::cout << "norm constraint for noise' failed\n";
        prettyPrint(std::cout, *vd.encErrQuadCnstr) << std::endl;
        prettyPrint(std::cout<<"pVec=", pVec) << std::endl;
        exit(0);
    }
#endif
}

// Proof of key-generation. We assume that the ProverData,VerifierData
// are already initialized.
// pkNum is the indec of the public key in the GlobalKey.
void proveKeyGen(ProverData& pd, const ALGEBRA::EVector& sk,
        const ALGEBRA::EVector& noise, int pkNum)
{
    VerifierData& vd = *(pd.vd);
    pd.sk2 = (ALGEBRA::EVector*) &sk;

    // commitment to the secret key
    vd.sk2Com = commit(*pd.sk2, vd.sk2Idx, vd.Gs, pd.sk2Rnd);
#if 0 // ifdef DEBUGGING
    BigInt one; conv(one, 1);
    BigInt tmp = one<<(vd.gk->skSize)-1;
    BigInt tmp1 = one<<(vd.gk->sigmaKG)-1;
    NTL::RR skBound = NTL::conv<NTL::RR>(vd.gk->kay * vd.gk->ell* tmp*tmp);
    NTL::RR errBound = NTL::conv<NTL::RR>(vd.gk->emm * vd.gk->ell* tmp1*tmp1);
    NTL::RR ratioNoise = NTL::conv<NTL::RR>(normSquaredBigInt(noise))/errBound;
    NTL::RR ratiosk = NTL::conv<NTL::RR>(normSquaredBigInt(sk))/skBound;
    std::cout << "|s|="<<sqrt(ratiosk)<<"*mu_s, |e|="<<sqrt(ratioNoise)<<"*u_e\n";
#endif

    TernaryEMatrix R1, R2;
    int nRcols = JLDIM/scalarsPerElement();
    // while (true) {
    for (int nTrials=1; true; nTrials++) {
        if (nTrials > 30) {
            throw std::runtime_error("proveKeyGen: too many retrys choosing R");
        }
        auto merBkp = *(vd.mer);
        merBkp.processPoint("RegevSK", vd.sk2Com);

        // Get the challenge matrices and set sk3=R1*sk2, noise2 = R2*noise
        merBkp.newTernaryEMatrix("RegevKeyGenR1", R1, sk.length(), nRcols);
        merBkp.newTernaryEMatrix("RegevKeyGenR2", R2, noise.length(), nRcols);

        // Compute the lower-dimenstion noise'
        pd.sk3 = sk*R1;
        pd.kGenErr = noise*R2;
#ifdef DEBUGGING
        {BigInt e1 = normSquaredBigInt(noise);
        BigInt e2 = normSquaredBigInt(pd.kGenErr);
        std::cout << "keygen: |e|^2=2^"<< log2BI(e1)
            << ", |e'|^2=2^"<<log2BI(e2)
            <<", B_kGenNoise^2=2^"<<(2*log2BI(vd.B_kGenNoise))<<std::endl;
        e1 = normSquaredBigInt(sk);
        e2 = normSquaredBigInt(pd.sk3);
        std::cout << "            |sk|^2=2^"<< log2BI(e1)
            << ", |sk'|^2=2^"<<log2BI(e2)
            <<", B_sk^2=2^"<<(2*log2BI(vd.B_sk))<<std::endl;}
#endif
        if (normSquaredBigInt(pd.kGenErr) <= vd.B_kGenNoise * vd.B_kGenNoise
            && normSquaredBigInt(pd.sk3) <= vd.B_sk * vd.B_sk) {
            *(vd.mer) = merBkp;
            break;
        }
        // if sk3 or noise2 are too large, update the commitment and try again
        pd.sk2Rnd += CRV25519::Scalar().setInteger(1);
        vd.sk2Com += Point::base();
    }

    // pad sk3 and noise2 with four scalars to get l2 norm=B_sk and B_kGenNoise
    pad2exactNorm(pd.sk3, pd.sk3Padding, vd.B_sk);
    pad2exactNorm(pd.kGenErr, pd.kGenErrPadding, vd.B_kGenNoise);

    // Commit to the vectors and paddings
    vd.sk3Com[0] = commit(pd.sk3, vd.sk3Idx, vd.Gs, pd.sk3Rnd[0]);
    vd.sk3Com[1] = commit(pd.sk3, vd.sk3Idx, vd.Hs, pd.sk3Rnd[1]);
    vd.sk3PadCom[0]=commit(pd.sk3Padding,vd.sk3PadIdx,vd.Gs,pd.sk3PadRnd[0]);
    vd.sk3PadCom[1]=commit(pd.sk3Padding,vd.sk3PadIdx,vd.Hs,pd.sk3PadRnd[1]);

    vd.kGenErrCom[0]=commit(pd.kGenErr,vd.kGenErrIdx,vd.Gs,pd.kGenErrRnd[0]);
    vd.kGenErrCom[1]=commit(pd.kGenErr,vd.kGenErrIdx,vd.Hs,pd.kGenErrRnd[1]);
    vd.kGenErrPadCom[0] = commit(pd.kGenErrPadding, vd.kGenErrPadIdx,
                                vd.Gs, pd.kGenErrPadRnd[0]);
    vd.kGenErrPadCom[1] = commit(pd.kGenErrPadding, vd.kGenErrPadIdx,
                                vd.Hs, pd.kGenErrPadRnd[1]);

    // include these commitments in the Merlin transcript
    vd.mer->processPoint("RegevKeyGenSK", vd.sk3Com[0]);
    vd.mer->processPoint(std::string(), vd.sk3Com[1]);
    vd.mer->processPoint(std::string(), vd.sk3PadCom[0]);
    vd.mer->processPoint(std::string(), vd.sk3PadCom[1]);

    vd.mer->processPoint("RegevKeyGenNoise", vd.kGenErrCom[0]);
    vd.mer->processPoint(std::string(), vd.kGenErrCom[1]);
    vd.mer->processPoint(std::string(), vd.kGenErrPadCom[0]);
    vd.mer->processPoint(std::string(), vd.kGenErrPadCom[1]);

    // Record the linear constraints <sk,A*R*x> + <noise',x> = pk*R*x

    // A challenge scalar x, defines the vector xvec=(1,x,x^2,...)
    Element x = vd.mer->newElement("RegevKeyGenChallenge");
    EVector xvec;
    powerVector(xvec, x, pd.kGenErr.length()); // the vector xvec=(1,x,x^2,...)

    // The term pk*R*x
    EVector Rx = R2 * xvec;
    Element eqTo = vd.gk->B[pkNum] * Rx;
    setEqsTo(vd.kGenLinCnstr, eqTo);

    // The term <sk, A*R*x>
    expandConstraints(vd.kGenLinCnstr, vd.sk2Idx, vd.gk->A * Rx);

    // The term <noise2,x>
    expandConstraints(vd.kGenLinCnstr, vd.kGenErrIdx, xvec);

    // Record the second linear constraints <sk2,R1*x2> -<sk3,x2> = 0

    Element x2 = vd.mer->newElement("RegevKeyGenChallenge2");
    EVector xvec2;
    powerVector(xvec2, x2, pd.sk3.length()); // the vector xvec=(1,x,x^2,...)

    setEqsTo(vd.kGenLinCnstr2, Element());

    // The term <sk2, R1*x2>
    expandConstraints(vd.kGenLinCnstr2, vd.sk2Idx, R1*xvec2);

    // The term -<sk3, x2>
    expandConstraints(vd.kGenLinCnstr2, vd.sk3Idx, -xvec2);


    // Record the norm constraints |paddedSK|^2=B_sk^2 and
    // |paddedNoise'|^2 =B_kGenNoise^2.
    
    for (int i=0; i<pd.sk3.length()*scalarsPerElement(); i++)
        vd.skQuadCnstr->indexes.insert(vd.skQuadCnstr->indexes.end(), vd.sk3Idx+i);
    for (int i=0; i<PAD_SIZE; i++)
        vd.skQuadCnstr->indexes.insert(vd.skQuadCnstr->indexes.end(), vd.sk3PadIdx+i);
    // The norm-squared itself, converted to CRV25519::Scalar
    conv(vd.skQuadCnstr->equalsTo, vd.B_sk * vd.B_sk);

    for (int i=0; i<pd.kGenErr.length()*scalarsPerElement(); i++)
        vd.kgErrQuadCnstr->indexes.insert(vd.kgErrQuadCnstr->indexes.end(),vd.kGenErrIdx+i);
    for (int i=0; i<PAD_SIZE; i++)
        vd.kgErrQuadCnstr->indexes.insert(vd.kgErrQuadCnstr->indexes.end(),vd.kGenErrPadIdx+i);
    // The norm-squared itself, converted to CRV25519::Scalar
    conv(vd.kgErrQuadCnstr->equalsTo, vd.B_kGenNoise * vd.B_kGenNoise);

#ifdef DEBUGGING
    assert(innerProduct(*pd.sk2, vd.gk->A*Rx)+innerProduct(pd.kGenErr,xvec)==eqTo);
    assert(innerProduct(pd.sk3, xvec2)==innerProduct(*pd.sk2, R1*xvec2));

    // verify the constraints
    DLPROOFS::PtxtVec pVec;
    pd.assembleFullWitness(pVec);
    for (int i=0; i<scalarsPerElement(); i++) { // check the linear constraints
        auto& linConstr = vd.kGenLinCnstr[i];
        if (!checkConstraintLoose(linConstr, pVec)) {
            std::cout << "constraints for keyGen #"<<i<<" failed\n  ";
            prettyPrint(std::cout, linConstr) << std::endl;
            prettyPrint(std::cout<<"  pVec=", pVec) << std::endl;
            exit(0);
        }
    }
    for (int i=0; i<scalarsPerElement(); i++) { // check the linear constraints
        auto& linConstr = vd.kGenLinCnstr2[i];
        if (!checkConstraintLoose(linConstr, pVec)) {
            std::cout << "constraints2 for keyGen #"<<i<<" failed\n  ";
            prettyPrint(std::cout, linConstr) << std::endl;
            prettyPrint(std::cout<<"  pVec=", pVec) << std::endl;
            exit(0);
        }
    }
    if (!checkConstraintLoose(*vd.skQuadCnstr, pVec, pVec)) { // sk norm
        std::cout << "norm constraint for sk failed\n  ";
        prettyPrint(std::cout, *vd.skQuadCnstr) << std::endl;
        prettyPrint(std::cout<<"  pVec=", pVec) << std::endl;
        exit(0);
    }
    if (!checkConstraintLoose(*vd.kgErrQuadCnstr, pVec, pVec)) { // noise norm
        std::cout << "norm constraint for noise' failed\n  ";
        prettyPrint(std::cout, *vd.kgErrQuadCnstr) << std::endl;
        prettyPrint(std::cout<<"  pVec=", pVec) << std::endl;
        exit(0);
    }
#endif
}

// Proof of correct re-sharing. It is assumed that pt1, pt2
// are already initialized in the ps structure
void proveReShare(ProverData& pd, const TOOLS::EvalSet& recSet) {
    VerifierData& vd = *(pd.vd);

    // Compute the Lagrange coefficients for the given reconstruction set
    SVector lagrange = vd.sp->lagrangeCoeffs(recSet);

    // Recall that we have the parity-check matrix H=pd.sp.H such that
    // a vector x is a valid sharing iff H*x=0. In our case the 1st entry
    // in x is the secret itself, computed as
    //      secret = x[0]=\sum_i lagrange[i]*pd.pt1[i]
    // The other entries are just the entries of pd.pt2. 
    // Hence the linear constraints for valid re-sharing are for all j:
    // sum_i lagrange[i]*H[0][j]*pd.pt1[i] + sum_i H[i][j]*pd.pt2[i] = 0

    const SMatrix& H = vd.sp->H;
    assert(lagrange.length()==pd.pt1->length() && H.NumCols()==1+pd.pt2->length());
    for (int i=0; i<vd.sp->H.NumRows(); i++) { // the j'th constraint
        // The terms lagrange[i]*H[0][j] * pd.pt1[i]
        int varIdx = vd.pt1Idx;
        for (int j=0; j<lagrange.length(); j++) {
            CRV25519::Scalar s;
            conv(s, lagrange[j] * H[i][0]); // convert to CRV25519::Scalar
            vd.reShrLinCnstr[i].addTerm(varIdx++, s);
        }
        // The terms H[i][j] * pd.pt2[i]
        varIdx = vd.pt2Idx;
        for (int j=1; j<=pd.pt2->length(); j++) {
            CRV25519::Scalar s;
            conv(s, H[i][j]);
            vd.reShrLinCnstr[i].addTerm(varIdx++, s);
        }
    }
#ifdef DEBUGGING
    SVector shares;
    resize(shares, pd.pt2->length()+1);
    shares[0] = innerProduct(lagrange, *pd.pt1);
    for (int i=1; i<=pd.pt2->length(); i++)
        shares[i] = (*pd.pt2)[i-1];
    SVector zeroVec; resize(zeroVec, H.NumRows());
    assert(H*shares == zeroVec);

    // verify the constraints
    DLPROOFS::PtxtVec pVec;
    pd.assembleFullWitness(pVec);
    for (int i=0; i<vd.sp->H.NumRows(); i++) { // the j'th constraint
        if (!checkConstraintLoose(vd.reShrLinCnstr[i], pVec)) {
            std::cout << "constraints #"<<i<<" for re-sharing failed\n  ";
            prettyPrint(std::cout, vd.reShrLinCnstr[i]) << std::endl;
            prettyPrint(std::cout<<"  pVec=", pVec) << std::endl;
            exit(0);  
        }
    }
#endif
}

// Concatenate all the secrets for the approximate proof of smallness,
// namely the ones that have padding, all vectors over GF(p^ell). For
// each entry j, idxMap[j] is the index of the 1st Scalar corresponding
// to this secret in the various constraints. 
static EVector concatSecrets(const ProverData& pd, std::vector<int>& idxMap) {
    VerifierData& vd = *(pd.vd);
    int totalLen= pd.decErr->length()+ pd.decErrPadding.length()
            + pd.r2.length()      + pd.r2Padding.length()
            + pd.encErr.length()  + pd.encErrPadding.length()
            + pd.sk3.length()     + pd.sk3Padding.length()
            + pd.kGenErr.length() + pd.kGenErrPadding.length();
    idxMap.resize(totalLen);

    EVector v;
    v.SetMaxLength(totalLen); // reserve memory

    int start = 0;
    v.append(*pd.decErr);
    for (int i=start; i<v.length(); i++)
        idxMap[i] = vd.decErrIdx + (i-start)*scalarsPerElement();

    start = v.length();
    v.append(pd.decErrPadding);
    for (int i=start; i<v.length(); i++)
        idxMap[i] = vd.decErrPadIdx + (i-start)*scalarsPerElement();

    start = v.length();
    v.append(pd.r2);
    for (int i=start; i<v.length(); i++)
        idxMap[i] = vd.r2Idx + (i-start)*scalarsPerElement();

    start = v.length();
    v.append(pd.r2Padding);
    for (int i=start; i<v.length(); i++)
        idxMap[i] = vd.r2PadIdx + (i-start)*scalarsPerElement();

    start = v.length();
    v.append(pd.encErr);
    for (int i=start; i<v.length(); i++)
        idxMap[i] = vd.encErrIdx + (i-start)*scalarsPerElement();

    start = v.length();
    v.append(pd.encErrPadding);
    for (int i=start; i<v.length(); i++)
        idxMap[i] = vd.encErrPadIdx + (i-start)*scalarsPerElement();

    start = v.length();
    v.append(pd.sk3);
    for (int i=start; i<v.length(); i++)
        idxMap[i] = vd.sk3Idx + (i-start)*scalarsPerElement();

    start = v.length();
    v.append(pd.sk3Padding);
    for (int i=start; i<v.length(); i++)
        idxMap[i] = vd.sk3PadIdx + (i-start)*scalarsPerElement();

    start = v.length();
    v.append(pd.kGenErr);
    for (int i=start; i<v.length(); i++)
        idxMap[i] = vd.kGenErrIdx + (i-start)*scalarsPerElement();

    start = v.length();
    v.append(pd.kGenErrPadding);
    for (int i=start; i<v.length(); i++)
        idxMap[i] = vd.kGenErrPadIdx + (i-start)*scalarsPerElement();

    assert(v.length()==totalLen);
    return v;
}


void proveSmallness(ProverData& pd) {
    VerifierData& vd = *(pd.vd);
    std::vector<int> idxMap;
    EVector allSecrets = concatSecrets(pd, idxMap);

    // Rejection sampling: Repeatedly choose random masking vectors y
    // and matrices R until both u=allSecrets*R and z=u+y are small enough.
    // The vector y is chosen from [+-B_smallness]^128, and we check that
    // |u|_{infty} <B_smallness/129 and |z|_{infty} <B_smallness*128/129.

    int paddingElements = PAD_SIZE / scalarsPerElement();
    int subvecElements = DEC_ERRV_SZ/scalarsPerElement();
    int JLelement = JLDIM / scalarsPerElement();

    int nCols = LINYDIM/scalarsPerElement();
    int nRows = 4*(JLelement +paddingElements)
                + vd.nDecSubvectors*(subvecElements +paddingElements);
    assert(allSecrets.length() == nRows);

    EVector u;
    TernaryEMatrix R;
    resize(pd.y, nCols);
    BoundedSizeElement randomzr(vd.smlnsBits); // for choosing in [+-2^smlnsBits]
    int uRetries = 0, zRetries = 0;
    for (int nTrials=0; true; nTrials++) {
        if (nTrials > 99) {
            throw std::runtime_error("proveSmallness: too many retrys choosing R");
        }
        auto merBkp = *(vd.mer);

        // choose a random y and commit to it
        for (Element& el: pd.y) randomzr.randomize(el);
            // FIXME: better to use the Merlin transcript for the purpose
            // choosing this masking vectors. Requires implemenetation of
            // choosing bounded-size random numbers from Merlin transcrypt

        vd.yCom = commit(pd.y, vd.yIdx, vd.Gs, pd.yRnd);
        merBkp.processPoint("smallnessPf", vd.yCom);

        merBkp.newTernaryEMatrix("Smallness", R, nRows, nCols);
        u = allSecrets * R;
        vd.z = u + pd.y;
#if 0 //def DEBUGGING
        std::cout << "smallness |secrets|_infty=2^"<<log2BI(lInftyNorm(allSecrets))
            << ", |secrets|^2=2^"<<log2BI(normSquaredBigInt(allSecrets))
            << " (dim=" << (allSecrets.length()*scalarsPerElement())
            << ")\n";
        std::cout << "    |u|_infty=2^" << log2BI(lInftyNorm(u))
            << ", |u|^2=2^"<<log2BI(normSquaredBigInt(u))
            << " (dim=" << (u.length()*scalarsPerElement()) << ")\n";
        std::cout << "    |y|_infty=2^" << log2BI(lInftyNorm(pd.y))
            << ", |z|_infty=2^" << log2BI(lInftyNorm(vd.z)) << std::endl;
#endif
        // check that u,z are small enough
        BigInt zBound = (vd.B_smallness*LINYDIM)/(LINYDIM+1);// B_smallness*128/129
        BigInt uBound = zBound/LINYDIM;                      // B_smallness/129
        if (lInftyNorm(u) <= uBound && lInftyNorm(vd.z) <= zBound) {
#ifdef DEBUGGING
            std::cout << "smallness proofs succeeded after "<<nTrials<< " trials, "
                << "uRetires="<< uRetries <<", zRetries="<<zRetries<< std::endl;
#endif
            *vd.mer = merBkp;
            break;
        }
#ifdef DEBUGGING
        if (lInftyNorm(u) > uBound) uRetries++;
        if (lInftyNorm(vd.z) > zBound) zRetries++;
#endif
    } // if u or z are too long, choose another y and try again

    // A challenge scalar x, defines the vector xvec=(1,x,x^2,...)
    vd.mer->processVector(vd.z, /*label=*/(unsigned char*)"masked reply",
                          /*label length=*/12);
    Element x = vd.mer->newElement("SmallnessChallenge");
    EVector xvec;
    powerVector(xvec, x, pd.y.length()); // the vector xvec=(1,x,x^2,...)

    // Record the linear constraint <allSecrets,R*x> + <y,x> = <z,x>

    EVector Rx = R*xvec;
    for (int i=0; i<idxMap.size(); i++)
        expandConstraints(vd.smlnsLinCnstr, idxMap[i], Rx[i]);

    // The term <y,x>
    expandConstraints(vd.smlnsLinCnstr, vd.yIdx, xvec);

    // The term <z,x>
    setEqsTo(vd.smlnsLinCnstr, innerProduct(vd.z, xvec));
#ifdef DEBUGGING
    assert(Rx.length()==idxMap.size());
    assert(innerProduct(allSecrets,Rx) + innerProduct(pd.y,xvec) == innerProduct(vd.z,xvec));

    // verify the constraints
    DLPROOFS::PtxtVec pVec;
    pd.assembleFullWitness(pVec);
    for (int i=0; i<scalarsPerElement(); i++) { // check the linear constraints
        auto& linConstr = vd.smlnsLinCnstr[i];
        if (!checkConstraintLoose(linConstr, pVec)) {
            std::cout << "constraints for smallness #"<<i<<" failed\n";
            std::cout << "  expected "<<balanced(DLPROOFS::dbgSum)<<std::endl;
            prettyPrint(std::cout<<"  cnstr=", linConstr) << std::endl;
            prettyPrint(std::cout<<"  pVec =", pVec) << std::endl;
            exit(0);
        }
    }
#endif
}

void ReadyToVerify::aggregateVerifier1(VerifierData& vd) {
    // Step 1: aggregate linear constraints, no change in the commitments
    CRV25519::Scalar r = vd.mer->newChallenge("aggregateLinear");
    powerVector(rVec, r, vd.linConstr.size()); // vector (1,r,r^2,...)
    linCnstr.merge(vd.linConstr, rVec);

    // Step 2: aggregate the quadratic constraints. This step also
    // modifies the linear constraint and the commitments

    // 2a. merge the quadratic constraints, a side effect of this is changing
    // the witness, multiplying the witness vector for contrs[i] by coeffs[i]
    r = vd.mer->newChallenge("aggregateNorms");
    powerVector(rVec, r, vd.normConstr.size()); // vector (1,r,r^2,...)
    quadCnstr.merge(vd.normConstr, rVec);

    // 2b. Adjust the linear constraints to compensate for the chnage to
    // the witness: when changing w->w*f we change the corresponding linear
    // coefficient from a to a/f.
    for (int i=0; i<rVec.size(); i++) {
        DLPROOFS::QuadConstraint& cnstr = vd.normConstr[i];
        for (int idx: cnstr.indexes)
            linCnstr.terms[idx] /= rVec[i];
    }

    // Split the linear contraints terms to ones that also appear in
    // the quadratic (as) vs ones that ony apppear in linear (bs)
    int wIdx=DLPROOFS::splitPtxtVec(as, bs, linCnstr.terms, quadCnstr.indexes);
    assert(wIdx == vd.wIdx);

    // 2c. Modify the commitments to reflect the change in witness
    for (int i=0; i<vd.nDecSubvectors; i++) {
        vd.decErrCom[i] *= rVec[i];
        vd.decErrPadCom[i] *= rVec[i];
    }
    vd.r2Com *= rVec[vd.nDecSubvectors];
    vd.r2PadCom *= rVec[vd.nDecSubvectors];
    vd.encErrCom *= rVec[vd.nDecSubvectors+1];
    vd.encErrPadCom *= rVec[vd.nDecSubvectors+1];
    vd.sk3Com *= rVec[vd.nDecSubvectors+2];
    vd.sk3PadCom *= rVec[vd.nDecSubvectors+2];
    vd.kGenErrCom *= rVec[vd.nDecSubvectors+3];
    vd.kGenErrPadCom *= rVec[vd.nDecSubvectors+3];

    // Step 3. Aggregate the commitments
    
    // 3a. The commitment in the linear-only constraint
    linCom = vd.pt1Com +vd.pt2Com +vd.sk1Com +vd.sk2Com +vd.rCom +vd.yCom;

    // 3a. The commitment in the quadratic constraint
    quadCom = vd.r2Com[0]+vd.r2Com[1]  +vd.r2PadCom[0]    +vd.r2PadCom[1]
     +vd.encErrCom[0]+vd.encErrCom[1]  +vd.encErrPadCom[0]+vd.encErrPadCom[1]
     +vd.sk3Com[0]      +vd.sk3Com[1]  +vd.sk3PadCom[0]   +vd.sk3PadCom[1]
     +vd.kGenErrCom[0]+vd.kGenErrCom[1]+vd.kGenErrPadCom[0]+vd.kGenErrPadCom[1];
    for (int i=0; i<vd.nDecSubvectors; i++) {
        quadCom += vd.decErrCom[i][0] + vd.decErrCom[i][1]
                        + vd.decErrPadCom[i][0] + vd.decErrPadCom[i][1];
    }
}

void ReadyToProve::aggregateProver(ProverData& pd)
{
    auto start = std::chrono::steady_clock::now();

    // Collect all the secret variables
    pd.assembleNormWitness(quadWitnessG); // all but sk1,pt1,pt2,y
    pd.assembleLinearWitness(linWitness);// only sk1,pt1,pt2,y

    auto end = std::chrono::steady_clock::now();
    auto ticks = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();

    // Reduce to a single quadratic and a single linear constraint
    VerifierData& vd = *pd.vd;
    aggregateVerifier1(vd);

    auto startExp = DLPROOFS::Point::counter;
    start = std::chrono::steady_clock::now();

    // The aggregate function implies modifying the secret variables
    // in the quadratic equations, and hence also the commitments and
    // their corresponding randomness

    for (int i=0; i<vd.nDecSubvectors; i++) {
        auto& c = vd.normConstr[i];// norm constraint for decryption subvector
        auto& factor = rVec[i];
        for (auto& idx: c.indexes) quadWitnessG[idx] *= factor;
        pd.decErrRnd[i] *= factor;
        pd.decErrPadRnd[i] *= factor;
    }

    for (auto& idx: vd.rQuadCnstr->indexes) // compressed encryption randomness
        quadWitnessG[idx] *= rVec[vd.nDecSubvectors];
    pd.r2Rnd *= rVec[vd.nDecSubvectors];
    pd.r2PadRnd *= rVec[vd.nDecSubvectors];

    for (auto& idx: vd.encErrQuadCnstr->indexes) // encryption noise
        quadWitnessG[idx] *= rVec[vd.nDecSubvectors+1];
    pd.encErrRnd *= rVec[vd.nDecSubvectors+1];
    pd.encErrPadRnd *= rVec[vd.nDecSubvectors+1];

    for (auto& idx: vd.skQuadCnstr->indexes) // compressed secret key
        quadWitnessG[idx] *= rVec[vd.nDecSubvectors+2];
    pd.sk3Rnd *= rVec[vd.nDecSubvectors+2];
    pd.sk3PadRnd *= rVec[vd.nDecSubvectors+2];

    for (auto& idx: vd.kgErrQuadCnstr->indexes) // key-generation noise
        quadWitnessG[idx] *= rVec[vd.nDecSubvectors+3];
    pd.kGenErrRnd *= rVec[vd.nDecSubvectors+3];
    pd.kGenErrPadRnd *= rVec[vd.nDecSubvectors+3];

    // reset from original constraints
     {DLPROOFS::LinConstraint emptyLin;
     DLPROOFS::QuadConstraint emptyQuad;
    for (auto& lc : vd.linConstr) lc = emptyLin;
    for (auto& qc : pd.vd->normConstr) qc = emptyQuad;}

    // Aggregate the commitment randomness for linear-only variables
    lComRnd = pd.pt1Rnd +pd.pt2Rnd +pd.sk1Rnd +pd.sk2Rnd +pd.rRnd +pd.yRnd;
#ifdef DEBUGGING
    assert(checkConstraintLoose(quadCnstr, quadWitnessG, quadWitnessG));
    {std::vector<CRV25519::Scalar> linWt;
    std::vector<CRV25519::Point> linGs;
    for (auto& b: bs) { 
        linWt.push_back(linWitness[b.first]);
        linGs.push_back(vd.Gs[b.first]);
    }
    assert(DLPROOFS::verifyCom(linCom, linGs.data(), linWt.data(), linGs.size(),lComRnd));
    }
#endif

    // Aggregate commitment randomness for the quadratic variables
    qComRnd = pd.r2Rnd[0] +pd.r2Rnd[1]  +pd.r2PadRnd[0]     +pd.r2PadRnd[1]
     +pd.encErrRnd[0] +pd.encErrRnd[1]  +pd.encErrPadRnd[0] +pd.encErrPadRnd[1]
     +pd.sk3Rnd[0]    +pd.sk3Rnd[1]     +pd.sk3PadRnd[0]    +pd.sk3PadRnd[1]
     +pd.kGenErrRnd[0]+pd.kGenErrRnd[1] +pd.kGenErrPadRnd[0]+pd.kGenErrPadRnd[1];
    for (int i=0; i<vd.nDecSubvectors; i++) {
        qComRnd += pd.decErrRnd[i][0] + pd.decErrRnd[i][1]
                        + pd.decErrPadRnd[i][0] + pd.decErrPadRnd[i][1];
    }
#ifdef DEBUGGING
    {std::vector<CRV25519::Scalar> wt;
    std::vector<Point> gs, hs;
    for (auto i: quadCnstr.indexes) {
        gs.push_back(vd.Gs[i]);
        hs.push_back(vd.Hs[i]);
        wt.push_back(quadWitnessG[i]);
    }
    assert(DLPROOFS::verifyCom2(quadCom, gs.data(), wt.data(),
                                hs.data(), wt.data(), gs.size(), qComRnd));
    }
#endif

    // Compute and commit to the outcome of the linear-only constraint
    linWitness[vd.wIdx] = quadWitnessG[vd.wIdx]
                        = DLPROOFS::innerProduct(bs, linWitness);
    const CRV25519::Scalar& w = quadWitnessG[vd.wIdx];// just for convenience
    pd.wRnd = CRV25519::randomScalar();
    assert(vd.wIdx == vd.Gs.size()-1);
    Point& wG = vd.Gs[vd.wIdx];
    vd.wCom = Point::base()*pd.wRnd + wG*w;
    bs[vd.wIdx].setInteger(-1); // add the term wIdx -> -1

    // Add commitment to w to both linCom and quadCom
    linCom += vd.wCom;
    lComRnd += pd.wRnd;
    quadCom += vd.wCom;
    qComRnd += pd.wRnd;
#ifdef DEBUGGING
    // check the commitments again
    {std::vector<CRV25519::Scalar> linWt;
    std::vector<CRV25519::Point> linGs;
    for (auto& b: bs) { 
        linWt.push_back(linWitness[b.first]);
        linGs.push_back(vd.Gs[b.first]);
    }
    assert(DLPROOFS::verifyCom(linCom, linGs.data(), linWt.data(), linGs.size(),lComRnd));
    }
    {std::vector<CRV25519::Scalar> wtG;
    std::vector<Point> gs, hs;
    for (auto i: quadCnstr.indexes) {
        gs.push_back(vd.Gs[i]);
        hs.push_back(vd.Hs[i]);
        wtG.push_back(quadWitnessG[i]);
    }
    std::vector<CRV25519::Scalar> wtH = wtG;
    wtG.push_back(quadWitnessG[vd.wIdx]);
    wtH.push_back(CRV25519::Scalar()); // add zero
    gs.push_back(vd.Gs[vd.wIdx]);
    hs.push_back(vd.Hs[vd.Hs.size()-1]);
    assert(DLPROOFS::verifyCom2(quadCom, gs.data(), wtG.data(),
                                hs.data(), wtH.data(), gs.size(), qComRnd));
    }
#endif
    end = std::chrono::steady_clock::now();
    ticks += std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();
    std::cout << "prover-only aggregation uses "
        << (DLPROOFS::Point::counter - startExp) << " exponentiations, ";

    // enforce norm constraint and separate linear and quadratic variables
    aggregateVerifier2(vd);

    // release memory of intermediate vectors
    start = std::chrono::steady_clock::now();
    rVec.clear(); uVec.clear(); as.clear(); bs.clear();

    // add the offsets deltaG, deltaH into quadWitnessG, quadWitnessH
    quadWitnessH = quadWitnessG;           // so far we only used quadWitnessG
    quadWitnessH[vd.wIdx] = CRV25519::Scalar(); // quadWitnessH doesn't have w
    auto itWitG = quadWitnessG.begin();
    auto itDeltaG = deltaG.begin();
    while (itWitG != quadWitnessG.end() && itDeltaG != deltaG.end()) {
        assert(itWitG->first == itDeltaG->first);
        itWitG->second -= itDeltaG->second;
        itWitG++; itDeltaG++;
    }
    assert(itWitG == quadWitnessG.end() && itDeltaG == deltaG.end());

    auto itWitH = quadWitnessH.begin();
    auto itDeltaH = deltaH.begin();
    while (itWitH != quadWitnessH.end() && itDeltaH != deltaH.end()) {
        assert(itWitH->first == itDeltaH->first);
        itWitH->second -= itDeltaH->second;
        itWitH++; itDeltaH++;
    }
    assert(itWitH == quadWitnessH.end() && itDeltaH == deltaH.end());
#ifdef DEBUGGING
    assert(checkConstraint(quadCnstr, quadWitnessG, quadWitnessH));
    assert(checkConstraint(linCnstr, linWitness));
#endif
    end = std::chrono::steady_clock::now();
    ticks += std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();
    std::cout << ticks << " millseconds\n";
}

void ReadyToVerify::aggregateVerifier2(VerifierData& vd) {
    // Step 4: enforce norm constraint and separate linear from quadratic
    // variables. At this point we have only two constraints:
    //    Linear:   <as,xs> + <bs,ys> = A (bs without the last term for w)
    //    Quadratic <xs,xs> = B

    // 4a. Modify the quadratic constraint to enforce norm constraint,
    // namely change the constraint to <xs-us,xs+us> = B-|us|^2, where
    // the us are a random challemge sent by the verifier. That is, each
    // witness variable xs[i] is replaced by xs[i]+us[i] for the Gs and
    // by xs[i]-us[i] for the Hs, hence the product changes from xs[i]^2
    // to xs[i]^2 - us[i]^2.
    CRV25519::Scalar u = vd.mer->newChallenge("enforceNorm");
    powerVector(uVec, u, quadCnstr.indexes.size()); // vector (1,r,r^2,...)
    assert(uVec.size()==as.size());
    quadCnstr.equalsTo -= innerProduct(uVec.data(),uVec.data(),uVec.size());

    // 4b. Separate the linear and quadratic constraint variables: The
    // linear constraint will become <(bs|-1), ys|w> = 0, so it have only
    // the variables in bs, plus the new variable w, and equalsTo = 0.
    // The quadratic constaints will include the old linear constraint
    // times a random challenge rho, so it will become
    //     <(xs+us+rho*as|w),(xs-us|rho)> = B-|us|^2+rho(A-<as,us>)
    // Hence the indexes will include also the index of w, and we will
    // set equalsTo = B-|us|^2+rho(A-<as,us>). We also incorporate w
    // in the commitments, namely C' = C + w*G_w.
    CRV25519::Scalar& A = linCnstr.equalsTo;
    CRV25519::Scalar rho = vd.mer->newChallenge("separareLinQuad");
    quadCnstr.indexes.insert(quadCnstr.indexes.end(), vd.wIdx);
    int idx = 0;
    for (auto& aPair: as) { // set A -= <as,us>
        assert(idx<uVec.size());
        A -= aPair.second * uVec[idx++];
    }
    quadCnstr.equalsTo += rho*A;

    linCnstr.terms = bs;             // including the term wIdx -> -1
    linCnstr.equalsTo = CRV25519::Scalar(); // set to equalsTo = zero

    // 4c. Finally, we avoid changing the commitments to the witness in
    // the quadratic proof by giving the verifier the offset vectors
    // deltaG, deltaH, such that
    // (1) the quadratic commitment is C=r*F+<x',Gs>+<y',Hs> for some x',y'
    // (2) these x',y' satisfy <x'-deltaG, y'-deltaH> = equalsTo
    // In our case we have deltaG = (-us-rho*as|0) and deltaH=(us|-rho).
    idx = 0;
    deltaG.clear();
    deltaH.clear();
    rho.negate(); // -rho
    for (auto& aPair : as) {
        aPair.second *= rho;
        aPair.second -= uVec[idx];
        deltaG.insert(deltaG.end(), aPair);
        deltaH.insert(deltaH.end(), std::make_pair(aPair.first,uVec[idx]));
        idx++;
    }
    deltaG[vd.wIdx] = CRV25519::Scalar();
    deltaH[vd.wIdx] = rho;
}

void ReadyToVerify::flattenLinVer(VerifierData& vd)
{
    linGs.clear(); linStmnt.clear();
    linGs.reserve(linCnstr.terms.size());
    linStmnt.reserve(linCnstr.terms.size());
    for (auto& aPair: linCnstr.terms) {
        linGs.push_back(vd.Gs[aPair.first]);
        linStmnt.push_back(aPair.second);
    }
    // release memory
    linCnstr.terms.clear();
}
void ReadyToVerify::flattenQuadVer(VerifierData& vd)
{
    quadGs.clear(); quadHs.clear(); offstG.clear(); offstH.clear();
    quadGs.reserve(quadCnstr.indexes.size());
    quadHs.reserve(quadCnstr.indexes.size());
    offstG.reserve(quadCnstr.indexes.size());
    offstH.reserve(quadCnstr.indexes.size());
    for (auto i: quadCnstr.indexes) {
        quadGs.push_back(vd.Gs[i]);
        if (i != vd.wIdx) quadHs.push_back(vd.Hs[i]);
        else              quadHs.push_back(vd.Hs[quadHs.size()-1]);
        offstG.push_back(deltaG[i]); // these two lines can be more efficient
        offstH.push_back(deltaH[i]); //    using iterators over deltaG,deltaH
    }
}

void ReadyToProve::flattenLinPrv(VerifierData& vd)
{
    assert(linWitness.size()==linCnstr.terms.size()); // sanity check
    flattenLinVer(vd);              // first flatten the public parts

    linWtns.clear(); linWtns.reserve(linWitness.size());
    for (auto& aPair: linWitness) { // then flatten the witness
        linWtns.push_back(aPair.second);
    }
    linWitness.clear();             // release memory
#ifdef DEBUGGING
    assert(innerProduct(linWtns.data(),linStmnt.data(),linStmnt.size())==linCnstr.equalsTo);
    assert(DLPROOFS::verifyCom(linCom, linGs.data(),
                               linWtns.data(),linWtns.size(),lComRnd));
#endif
}
void ReadyToProve::flattenQuadPrv(VerifierData& vd)
{
    flattenQuadVer(vd);              // first flatten the public parts
    quadWtnsG.clear(); quadWtnsH.clear();
    quadWtnsG.reserve(quadWitnessG.size()); // allocate memory
    quadWtnsH.reserve(quadWitnessH.size());
    auto itG = quadWitnessG.begin(); // then flatten the witnesses
    auto itH = quadWitnessH.begin();
    while (itG != quadWitnessG.end() && itH != quadWitnessH.end()) {
        assert(itG->first == itH->first);
        quadWtnsG.push_back(itG->second);
        quadWtnsH.push_back(itH->second);
        itG++; itH++;
    }
    assert(itG==quadWitnessG.end() && itH==quadWitnessH.end());// sanity check
    quadWitnessG.clear(); // release memory
    quadWitnessH.clear();
#ifdef DEBUGGING
    assert(innerProduct(quadWtnsG.data(),quadWtnsH.data(),quadWtnsG.size())==quadCnstr.equalsTo);
    std::vector<CRV25519::Scalar> shiftedWtG(quadWtnsG.size());
    assert(quadWtnsG.size()==offstG.size());
    for (int i=0; i<shiftedWtG.size(); i++)
        shiftedWtG[i] = quadWtnsG[i] + offstG[i];
    std::vector<CRV25519::Scalar> shiftedWtH(quadWtnsH.size());
    assert(quadWtnsH.size()==offstH.size());
    for (int i=0; i<shiftedWtH.size(); i++)
        shiftedWtH[i] = quadWtnsH[i] + offstH[i];
    assert(DLPROOFS::verifyCom2(quadCom, quadGs.data(), shiftedWtG.data(),
                quadHs.data(), shiftedWtH.data(), quadGs.size(), qComRnd));
#endif
}


} // end of namespace REGEVENC
