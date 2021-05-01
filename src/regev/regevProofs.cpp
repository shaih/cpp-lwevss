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
#include "utils.hpp"
#include "regevProofs.hpp"

using namespace ALGEBRA;

namespace REGEVENC {
using CRV25519::Point, DLPROOFS::PedersenContext,
    DLPROOFS::MerlinBPctx, DLPROOFS::LinConstraint, DLPROOFS::QuadConstraint;
// NOTE: REGEVENC::Scalar is not the same as CRV25519::Scalar

// Proof of decryption. We assume that the ProverData,VerifierData are
// already initialized, and that ProverData contains the padded sk1
// and VerifierData contains a commitment to it.
void proveDecryption(ProverData& pd, const SVector& ptxt,
        const EVector& noise, const EMatrix& ctMat, const EVector& ctVec)
{
    VerifierData& vd = *(pd.vd);
    pd.pt1 = (SVector*) &ptxt;
    pd.decErr = (EVector*) &noise;

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
    Element sum = innerProduct((*pd.sk1), yvec) + innerProduct(noise, xvec) + innerProduct(ptxt, xvec*vd.gk->g());
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

// Prepare the constrints fo the proof of decryption, at the verifier's site.
// We assume that the ProverData,VerifierData contains all teh commitments.
void verifyDecryption(VerifierData& vd, // vd has all the commitments
        const ALGEBRA::EMatrix& ctMat, const ALGEBRA::EVector& ctVec)
{
    // commitment to decrypted plaintext
    vd.mer->processPoint("RegevDecPtxt", vd.pt1Com);

    // include the commitments to noise,padding in the Merlin transcript
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
    powerVector(xvec, x, vd.gk->tee); // the vector xvec=(1,x,x^2,...)

    // Record the linear constraints
    //            <sk,ctMat*xvec> +<ptxt,g*xvec> +<noise,xvec> = <ctVec,xvec>

    setEqsTo(&(vd.linConstr[0]), innerProduct(ctVec, xvec));

    // expand <sk,ctMat*xvec> 
    EVector yvec = ctMat * xvec;
    expandConstraints(&(vd.linConstr[0]), vd.sk1Idx, yvec);

    // Expand <noise,xvec>
    expandConstraints(&(vd.linConstr[0]), vd.decErrIdx, xvec);

    // Constraints for <ptxt,g*xvec>, where ptxt is a Z_p vector, not GF(p^e)
    makeConstraints(&(vd.linConstr[0]), vd.pt1Idx, xvec * vd.gk->g());

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
}

// Proof of encryption. We assume that the ProverData,VerifierData are
// already initialized.
void proveEncryption(ProverData& pd, const ALGEBRA::SVector& ptxt,
        const ALGEBRA::EVector& rnd, const ALGEBRA::EVector& noise,
        const ALGEBRA::EVector& ct1, const ALGEBRA::EVector& ct2)
{
    VerifierData& vd = *(pd.vd);
    pd.pt2 = (ALGEBRA::SVector*) &ptxt;
    pd.r   = (ALGEBRA::EVector*) &rnd;

    // commitment to encrypted plaintext
    vd.pt2Com = commit(ptxt, vd.pt2Idx, vd.Gs, pd.pt2Rnd);
    vd.mer->processPoint("RegevEncPtxt", vd.pt2Com);
    
    // pad the randomness with four scalars to get l2 norm=B_encRnd
    pad2exactNorm(rnd, pd.rPadding, vd.B_encRnd);

    // Commit to the randomness and include these commitments in the
    // Merlin transcript, then choose the trenary matrix R=(R1|R2)
    // and set noise2=R*noise.
    EVector noiseA; resize(noiseA, vd.gk->kay); // the two parts of the noise vector
    for (int i=0; i<vd.gk->kay; i++) noiseA[i]=noise[i];
    EVector noiseB; resize(noiseB, vd.gk->enn);
    for (int i=0; i<vd.gk->enn; i++) noiseB[i]=noise[i +vd.gk->kay];

    // Commit to the randomness wrt both the G's and H's
    vd.rCom[0] = commit(rnd, vd.rIdx, vd.Gs, pd.rRnd[0]);
    vd.rCom[1] = commit(rnd, vd.rIdx, vd.Hs, pd.rRnd[1]);

    // Commit to the padding wrt both the G's and H's
    vd.rPadCom[0] = commit(pd.rPadding, vd.rPadIdx, vd.Gs, pd.rPadRnd[0]);
    // We re-do the last commitment until R*noise is small enough

    vd.mer->processPoint("RegevEncRnd", vd.rCom[0]);
    vd.mer->processPoint(std::string(), vd.rCom[1]);
    vd.mer->processPoint(std::string(), vd.rPadCom[0]);

    TernaryEMatrix R1, R2;
    int nRrows = JLDIM/scalarsPerElement();
    // while (true) {
    for (int nTrials=1; true; nTrials++) {
        auto merBkp = *(vd.mer);
        vd.rPadCom[1] = commit(pd.rPadding, vd.rPadIdx, vd.Hs, pd.rPadRnd[1]);
        merBkp.processPoint(std::string(), vd.rPadCom[1]);

        // Get the challenge matrices, and set noise' = (R1|R2)*noise
        merBkp.newTernaryEMatrix("RegevEncR1", R1, nRrows, vd.gk->kay);
        merBkp.newTernaryEMatrix("RegevEncR2", R2, nRrows, vd.gk->enn);

        // Compute the lower-dimenstion noise'
        pd.encErr = (R1*noiseA) + (R2*noiseB);
        if (normSquaredBigInt(pd.encErr) <= vd.B_encNoise * vd.B_encNoise) {
            *(vd.mer) = merBkp;
            break;
        }
        if (nTrials > 30) {
            throw std::runtime_error("proveEncryption: too many retrys choosing R");
        }
    } // if the noise' is too large, try again

    // pad noise' with four scalars to get l2 norm=B_encNoise
    pad2exactNorm(pd.encErr, pd.encErrPadding, vd.B_encNoise);

    // Commit to noise' wrt both the G's and H's
    vd.encErrCom[0] = commit(pd.encErr, vd.encErrIdx, vd.Gs, pd.encErrRnd[0]);
    vd.encErrCom[1] = commit(pd.encErr, vd.encErrIdx, vd.Hs, pd.encErrRnd[1]);

    // Commit to the padding wrt both the G's and H's
    vd.encErrPadCom[0] = commit(pd.encErrPadding,
                                vd.encErrPadIdx, vd.Gs, pd.encErrPadRnd[0]);
    vd.encErrPadCom[1] = commit(pd.encErrPadding,
                                vd.encErrPadIdx, vd.Hs, pd.encErrPadRnd[1]);

    // include these commitments in the Merlin transcript
    vd.mer->processPoint("RegevEncNoise", vd.encErrCom[0]);
    vd.mer->processPoint(std::string(), vd.encErrCom[1]);
    vd.mer->processPoint(std::string(), vd.encErrPadCom[0]);
    vd.mer->processPoint(std::string(), vd.encErrPadCom[1]);

    // A challenge element x, defines the vector xvec=(1,x,x^2,...)
    Element x = vd.mer->newElement("RegevEncChallenge");
    EVector xvec;
    powerVector(xvec, x, pd.encErr.length()); // the vector xvec=(1,x,x^2,...)

    // Record the linear constraints
    //     <x*R𝟏*𝐀+x*R2*B,r> + <x,noise'> + <g*x*R2,ptxt> = <x,R1*ct1+R2*ct2>

    // The term <x, R1*ct1+R2*ct2>
    Element eqTo = innerProduct(xvec, (R1*ct1)+(R2*ct2));
    setEqsTo(vd.encLinCnstr, eqTo);

    // The term <x*R𝟏*𝐀+x*R2*B, r> 
    EVector xR2 = xvec*R2;
    EVector frstTerm = (xvec*R1)*(vd.gk->A) + xR2*(vd.gk->B);
    expandConstraints(vd.encLinCnstr, vd.rIdx, frstTerm);

    // The term <x,noise'>
    expandConstraints(vd.encLinCnstr, vd.encErrIdx, xvec);

    // The term <g*x*R2, ptxt> 
    makeConstraints(vd.encLinCnstr, vd.pt2Idx, vd.gk->g()*xR2);

    // Record the norm constraints |paddedRnd|^2=B_encRnd^2 and
    // |paddedNoise'|^2 =B_encNoise^2.
    
    for (int i=0; i<pd.r->length()*scalarsPerElement(); i++)
        vd.rQuadCnstr->indexes.insert(vd.rQuadCnstr->indexes.end(), vd.rIdx+i);
    for (int i=0; i<PAD_SIZE; i++)
        vd.rQuadCnstr->indexes.insert(vd.rQuadCnstr->indexes.end(), vd.rPadIdx+i);
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

    // pad sk with four scalars to get l2 norm=B_sk
    pad2exactNorm(*pd.sk2, pd.sk2Padding, vd.B_sk);

    // commitment to the secret key and padding, wrt both the Gs and Hs
    vd.sk2Com[0] = commit(*pd.sk2, vd.sk2Idx, vd.Gs, pd.sk2Rnd[0]);
    vd.sk2Com[1] = commit(*pd.sk2, vd.sk2Idx, vd.Hs, pd.sk2Rnd[1]);
    vd.sk2PadCom[0]= commit(pd.sk2Padding, vd.sk2PadIdx, vd.Gs, pd.sk2PadRnd[0]);
    // We re-do the last commitment until R*noise is small enough

    // Process the commitments
    vd.mer->processPoint("RegevSK", vd.sk2Com[0]);
    vd.mer->processPoint(std::string(), vd.sk2Com[1]);
    vd.mer->processPoint(std::string(), vd.sk2PadCom[0]);

    TernaryEMatrix R;
    int nRcols = JLDIM/scalarsPerElement();
    // while (true) {
    for (int nTrials=1; true; nTrials++) {
        auto merBkp = *(vd.mer);
        vd.sk2PadCom[1]= commit(pd.sk2Padding, vd.sk2PadIdx, vd.Hs, pd.sk2PadRnd[1]);
        merBkp.processPoint(std::string(), vd.sk2PadCom[1]);

        // Get the challenge matrix and set noise' = R*noise
        merBkp.newTernaryEMatrix("RegevKeyGenR", R, noise.length(), nRcols);

        // Compute the lower-dimenstion noise'
        pd.kGenErr = noise*R;
        if (normSquaredBigInt(pd.kGenErr) <= vd.B_kGenNoise * vd.B_kGenNoise) {
            *(vd.mer) = merBkp;
            break;
        }
        if (nTrials > 30) {
            throw std::runtime_error("proveKeyGen: too many retrys choosing R");
        }
    } // if the noise' is too large, try again

    // pad the noise' with four scalars to get l2 norm=B_kGenNoise
    pad2exactNorm(pd.kGenErr, pd.kGenErrPadding, vd.B_kGenNoise);

    // Commit to noise' wrt both the G's and H's
    vd.kGenErrCom[0] = commit(pd.kGenErr, vd.kGenErrIdx, vd.Gs, pd.kGenErrRnd[0]);
    vd.kGenErrCom[1] = commit(pd.kGenErr, vd.kGenErrIdx, vd.Hs, pd.kGenErrRnd[1]);

    // Commit to the padding wrt both the G's and H's
    vd.kGenErrPadCom[0] = commit(pd.kGenErrPadding,
                                vd.kGenErrPadIdx, vd.Gs, pd.kGenErrPadRnd[0]);
    vd.kGenErrPadCom[1] = commit(pd.kGenErrPadding,
                                vd.kGenErrPadIdx, vd.Hs, pd.kGenErrPadRnd[1]);

    // include these commitments in the Merlin transcript
    vd.mer->processPoint("RegevKryGenNoise", vd.kGenErrCom[0]);
    vd.mer->processPoint(std::string(), vd.kGenErrCom[1]);
    vd.mer->processPoint(std::string(), vd.kGenErrPadCom[0]);
    vd.mer->processPoint(std::string(), vd.kGenErrPadCom[1]);

    // A challenge scalar x, defines the vector xvec=(1,x,x^2,...)
    Element x = vd.mer->newElement("RegevKeyGenChallenge");
    EVector xvec;
    powerVector(xvec, x, pd.kGenErr.length()); // the vector xvec=(1,x,x^2,...)

    // Record the linear constraints <sk,A*R*x> + <noise',x> = pk*R*x

    // The term pk*R*x
    EVector Rx = R * xvec;
    Element eqTo = vd.gk->B[pkNum] * Rx;
    setEqsTo(vd.kGenLinCnstr, eqTo);

    // The term <sk, A*R*x>
    expandConstraints(vd.kGenLinCnstr, vd.sk2Idx, vd.gk->A * Rx);

    // The term <noise',x>
    expandConstraints(vd.kGenLinCnstr, vd.kGenErrIdx, xvec);

    // Record the norm constraints |paddedSK|^2=B_sk^2 and
    // |paddedNoise'|^2 =B_kGenNoise^2.
    
    for (int i=0; i<pd.sk2->length()*scalarsPerElement(); i++)
        vd.skQuadCnstr->indexes.insert(vd.skQuadCnstr->indexes.end(), vd.sk2Idx+i);
    for (int i=0; i<PAD_SIZE; i++)
        vd.skQuadCnstr->indexes.insert(vd.skQuadCnstr->indexes.end(), vd.sk2PadIdx+i);
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
    // in x is the secret itself, x[0]=\sum_i lagrange[i]*pd.pt1[i], and
    // the other entries are just the entries of pd.pt2.
    // Hence the linear constraints for valid re-sharing are for all j:
    // sum_i lagrange[i]*H[0][j] * pd.pt1[i] + sum_i H[i][j] * pd.pt2[i] = 0

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


static EVector concatSecrets(const ProverData& pd, std::vector<int>& idxMap) {
    VerifierData& vd = *(pd.vd);
    int totalLen = pd.sk2->length() +pd.sk2Padding.length()
            + pd.kGenErr.length()   +pd.kGenErrPadding.length()
            + pd.r->length()        +pd.rPadding.length()
            + pd.encErr.length()    +pd.encErrPadding.length()
            + pd.decErr->length()   +pd.decErrPadding.length();
    idxMap.resize(totalLen);

    EVector v;
    v.SetMaxLength(totalLen); // reserve memory
    int start = 0;

    v.append(*pd.sk2);
    for (int i=start; i<v.length(); i++)
        idxMap[i] = vd.sk2Idx + (i-start)*scalarsPerElement();
    start = v.length();

    v.append(pd.sk2Padding);
    for (int i=start; i<v.length(); i++)
        idxMap[i] = vd.sk2PadIdx + (i-start)*scalarsPerElement();
    start = v.length();

    v.append(pd.kGenErr);
    for (int i=start; i<v.length(); i++)
        idxMap[i] = vd.kGenErrIdx + (i-start)*scalarsPerElement();
    start = v.length();

    v.append(pd.kGenErrPadding);
    for (int i=start; i<v.length(); i++)
        idxMap[i] = vd.kGenErrPadIdx + (i-start)*scalarsPerElement();
    start = v.length();

    v.append(*pd.r);
    for (int i=start; i<v.length(); i++)
        idxMap[i] = vd.rIdx + (i-start)*scalarsPerElement();
    start = v.length();

    v.append(pd.rPadding);
    for (int i=start; i<v.length(); i++)
        idxMap[i] = vd.rPadIdx + (i-start)*scalarsPerElement();
    start = v.length();

    v.append(pd.encErr);
    for (int i=start; i<v.length(); i++)
        idxMap[i] = vd.encErrIdx + (i-start)*scalarsPerElement();
    start = v.length();

    v.append(pd.encErrPadding);
    for (int i=start; i<v.length(); i++)
        idxMap[i] = vd.encErrPadIdx + (i-start)*scalarsPerElement();
    start = v.length();

    v.append(*pd.decErr);
    for (int i=start; i<v.length(); i++)
        idxMap[i] = vd.decErrIdx + (i-start)*scalarsPerElement();
    start = v.length();

    v.append(pd.decErrPadding);
    for (int i=start; i<v.length(); i++)
        idxMap[i] = vd.decErrPadIdx + (i-start)*scalarsPerElement();

    assert(v.length()==totalLen);
    return v;
}


void proveSmallness(ProverData& pd) {
    VerifierData& vd = *(pd.vd);
    std::vector<int> idxMap;
    EVector allSecrets = concatSecrets(pd, idxMap);

    // Rejection sampling: Repeatedly choose random masking vectors y
    // and matrices R until both u=(concatenated-variables)*R and z=u+y
    // are small enough. The vector y is chosen from [+-B_smallness]^128,
    // and we check that |u|_{infty} < B_smallness/129 and that
    // |z|_{infty} < B_smallness*128/129.

    int paddingElements = PAD_SIZE / scalarsPerElement();
    int subvecElements = DEC_ERRV_SZ/scalarsPerElement();
    int JLelement = JLDIM / scalarsPerElement();

    int nCols = LINYDIM/scalarsPerElement();
    int nRows = vd.gk->kay +vd.gk->emm +2*JLelement +paddingElements*4
                + vd.nDecSubvectors*(subvecElements+paddingElements);
    assert(allSecrets.length() == nRows);

    EVector u;
    TernaryEMatrix R;
    resize(pd.y, nCols);
    BoundedSizeElement randomzr(smlnsBits); // for choosing in [+-2^smlnsBits]
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

        // check that u,z are small enough
        BigInt zBound = (vd.B_smallness*LINYDIM)/(LINYDIM+1);// B_smallness*128/129
        BigInt uBound = zBound/LINYDIM;                      // B_smallness/129
        if (normSquaredBigInt(u) <= uBound*uBound
            && normSquaredBigInt(vd.z) <= zBound*zBound) {
            *vd.mer = merBkp;
            break;
        }
    }

    // A challenge scalar x, defines the vector xvec=(1,x,x^2,...)
    Element x = vd.mer->newElement("SmallnessChallenge");
    EVector xvec;
    powerVector(xvec, x, pd.y.length()); // the vector xvec=(1,x,x^2,...)

    // Record the linear constraint
    //     (concatenated-variables) * R*x + <y,x> = <z,x>

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

} // end of namespace REGEVENC
