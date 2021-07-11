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
#include <chrono>
#include "utils.hpp"
#include "regevProofs.hpp"

using namespace ALGEBRA;

namespace REGEVENC {
using CRV25519::Point, DLPROOFS::PedersenContext,
    DLPROOFS::MerlinBPctx, DLPROOFS::LinConstraint, DLPROOFS::QuadConstraint;
// NOTE: REGEVENC::Scalar is not the same as CRV25519::Scalar

// Proof of decryption. We assume that the ProverData,VerifierData are
// already initialized, and that ProverData contains sk1, VerifierData
// has a commitment to sk1, and ProverData has the commitment randomness.
void proveDecryption(ProverData& pd, 
    const ALGEBRA::EMatrix& ctMat, const ALGEBRA::EVector& ctVec,
    const ALGEBRA::SVector& ptxt, const ALGEBRA::EVector& skey,
    const ALGEBRA::EVector& noise)
{
    VerifierData& vd = *(pd.vd);
    int kk = vd.gk->kay * GlobalKey::ell;

    // commitment to decrypted plaintext
    vd.pt1Com = commit(ptxt, vd.pt1Idx, vd.Gs, pd.pt1Rnd);
    vd.mer->processPoint("RegevDecPtxt", vd.pt1Com);

    // Get the challenge t-by-256 matrix and set compressedNoise = noise*R
    TernaryEMatrix R;
    int nRcols = JLDIM/scalarsPerElement();
    vd.mer->newTernaryEMatrix("RegevDecX", R, vd.gk->tee, nRcols);

    // Compute the compressed noise and break it into hi and lo digits

    EVector compNoise = noise*R;
    EVector compHi, compLo;
    breakTwoDigits(compHi, compLo, compNoise, vd.radix);

    // pad each digit with four scalars to get l2-norm euqal to bound
    EVector padHi, padLo;
    BigInt hiBound = (vd.B_dNoise / vd.radix) +int(ceil(sqrt(kk)));
    BigInt loBound = vd.radix * SQRT_JL;
#ifdef DEBUGGING
    std::cout <<"B_decNoise=2^"<<log2BI(vd.B_dNoise)
        << ", radix = 2^"<<log2BI(vd.radix)<<std::endl;
    std::cout << "  |decNoiseHi|^2=2^"<<log2BI(normSquaredBigInt(compHi))
        << ", hiBound = 2^"<<log2BI(hiBound)<<std::endl;
    std::cout << "  |decNoiseLo|^2=2^"<<log2BI(normSquaredBigInt(compLo))
        << ", loBound = 2^"<<log2BI(loBound)<<std::endl;
#endif
    pad2exactNorm(compHi, padHi, hiBound);
    pad2exactNorm(compLo, padLo, loBound);

    // Commit to the vectors and paddings
    vd.dCompHiCom = commit2(compHi, vd.dCompHiIdx, vd.Gs, vd.Hs, pd.dCompHiRnd);
    vd.dPadHiCom = commit2(padHi, vd.dPadHiIdx, vd.Gs, vd.Hs, pd.dPadHiRnd);
    vd.dCompLoCom = commit2(compLo, vd.dCompLoIdx, vd.Gs, vd.Hs, pd.dCompLoRnd);
    vd.dPadLoCom = commit2(padLo, vd.dPadLoIdx, vd.Gs, vd.Hs, pd.dPadLoRnd);

    // include these commitments in the Merlin transcript
    vd.mer->processPoint("RegevDecCompHi", vd.dCompHiCom);
    vd.mer->processPoint("RegevDecPadHi", vd.dPadHiCom);
    vd.mer->processPoint("RegevDecCompLo", vd.dCompLoCom);
    vd.mer->processPoint("RegevDecPadLo", vd.dPadLoCom);

    // A challenge scalar x, defines the vector xvec=(1,x,x^2,...)
    Element x = vd.mer->newElement("RegevDec");
    EVector xvec;
    powerVector(xvec, x, nRcols); // the vector xvec=(1,x,x^2,...)

    // Record the linear constraints
    //     <sk,ctMat*R*xvec> +<ptxt,g*R*xvec> +<eLo,xvec> +<eHi,radix*xvec>
    //     = <ctVec,R*xvec>
    auto* lCnstr = &(vd.linConstr[vd.dLinIdx]);
    for (int i=0; i<GlobalKey::ell; i++)
      lCnstr[i] = DLPROOFS::LinConstraint(); // make sure they are empty

    EVector Rx = R*xvec;

    // The element <ctVec,R*xvec>
    setEqsTo(lCnstr, innerProduct(ctVec,Rx));

    // Expand <eLo,xvec> + <eHi,radix*xvec>
    Scalar B_d; conv(B_d, vd.radix);
    expandConstraints(lCnstr, vd.dCompLoIdx, xvec);
    expandConstraints(lCnstr, vd.dCompHiIdx, B_d*xvec);

    // expand <sk,ctMat*R*xvec>
    expandConstraints(lCnstr, vd.sk1Idx, ctMat*Rx);

    // Constraints for <ptxt,g*R*xvec>, where ptxt is a Z_p vector, not GF(p^e)
    makeConstraints(lCnstr, vd.pt1Idx, Rx*vd.gk->g());

    // Record the linear-constraint witnesses
    addEVec2Map(pd.linWitness, compHi, vd.dCompHiIdx);
    addEVec2Map(pd.linWitness, padHi, vd.dPadHiIdx);
    addEVec2Map(pd.linWitness, compLo, vd.dCompLoIdx);
    addEVec2Map(pd.linWitness, padLo, vd.dPadLoIdx);
    addEVec2Map(pd.linWitness, skey, vd.sk1Idx);
    addSVec2Map(pd.linWitness, ptxt, vd.pt1Idx);
#ifdef DEBUGGING
    for (int i=0; i<scalarsPerElement(); i++)
        if (!checkConstraintLoose(lCnstr[i], pd.linWitness)) {
            std::cout<<"decryption linear constraint "<<(i+1)<<" failed\n";
        }
#endif

    // Norm constraints:
    // |paddedNoiseHi|^2 = hiBound^2, |paddedNoiseLo|^2 = loBound^2
    CRV25519::Scalar normSquared;

    // Norm constraint for the high digit
    conv(normSquared, square(hiBound));
    vd.normConstr[vd.dHiQuadIdx].equalsTo = normSquared;
    ALGEBRA::addRange2Set(vd.normConstr[vd.dHiQuadIdx].indexes, vd.dCompHiIdx, JLDIM);
    ALGEBRA::addRange2Set(vd.normConstr[vd.dHiQuadIdx].indexes, vd.dPadHiIdx, PAD_SIZE);

    // Norm constraint for the low digit
    conv(normSquared, square(loBound));
    vd.normConstr[vd.dLoQuadIdx].equalsTo = normSquared;
    ALGEBRA::addRange2Set(vd.normConstr[vd.dLoQuadIdx].indexes, vd.dCompLoIdx, JLDIM);
    ALGEBRA::addRange2Set(vd.normConstr[vd.dLoQuadIdx].indexes, vd.dPadLoIdx, PAD_SIZE);

    // Record the norm-constraint witnesses
    addEVec2Map(pd.quadWitnessG, compHi, vd.dCompHiIdx);
    addEVec2Map(pd.quadWitnessG, padHi, vd.dPadHiIdx);
    addEVec2Map(pd.quadWitnessG, compLo, vd.dCompLoIdx);
    addEVec2Map(pd.quadWitnessG, padLo, vd.dPadLoIdx);

#ifdef DEBUGGING
    if (!checkConstraintLoose(vd.normConstr[vd.dHiQuadIdx],pd.quadWitnessG,pd.quadWitnessG)){
        std::cout << "decryption norm constraint for high digit failed\n";
    }
    if (!checkConstraintLoose(vd.normConstr[vd.dLoQuadIdx],pd.quadWitnessG,pd.quadWitnessG)){
        std::cout << "decryption norm constraint for low digit failed\n";
    }
#endif
    // Copy the padded digits to ProverData.compressed. Indexes are
    // divided by ell since these are still vectors over GF(P^ell)
    int eIdx = vd.dCompHiIdx / scalarsPerElement();
    for (auto& x : compHi) { pd.compressed[eIdx++] = x; }
    eIdx = vd.dPadHiIdx / scalarsPerElement();
    for (auto& x : padHi)  { pd.compressed[eIdx++] = x; }
    eIdx = vd.dCompLoIdx / scalarsPerElement();
    for (auto& x : compLo) { pd.compressed[eIdx++] = x; }
    eIdx = vd.dPadLoIdx / scalarsPerElement();
    for (auto& x : padLo)  { pd.compressed[eIdx++] = x; }
}

// Proof of encryption. We assume that the ProverData,VerifierData are
// already initialized.
void proveEncryption(ProverData& pd,
        const ALGEBRA::EVector& ct1, const ALGEBRA::EVector& ct2, 
        const ALGEBRA::SVector& ptxt, const ALGEBRA::EVector& rnd,
        const ALGEBRA::EVector& noise1,const ALGEBRA::EVector& noise2)
{
    VerifierData& vd = *(pd.vd);
    int kk = vd.gk->kay * GlobalKey::ell;
    int nn = vd.gk->enn * GlobalKey::ell;

    // commitment to encrypted plaintext and randomness, wrt the G's
    vd.pt2Com = commit(ptxt, vd.pt2Idx, vd.Gs, pd.pt2Rnd);
    vd.rCom = commit(rnd, vd.rIdx, vd.Gs, pd.rRnd);
    vd.mer->processPoint("RegevEncPtxt", vd.pt2Com);
    vd.mer->processPoint("RegevEncRnd", vd.rCom);

    TernaryEMatrix R1, R2, R3;
    int nRrows = JLDIM/scalarsPerElement();

    // Get the challenge matrices, and set comp_i = Ri*noise_i
    vd.mer->newTernaryEMatrix("RegevEncR1", R1, nRrows, vd.gk->kay);
    vd.mer->newTernaryEMatrix("RegevEncR2", R2, nRrows, vd.gk->enn);
    vd.mer->newTernaryEMatrix("RegevEncR3", R3, nRrows, vd.gk->kay);

    EVector compNoise1 = R1*noise1;
    EVector compNoise2 = R2*noise2;
    EVector compR = R3*rnd;

    EVector comp1Hi, comp1Lo, comp2Hi, comp2Lo;
    breakTwoDigits(comp1Hi, comp1Lo, compNoise1, vd.radix);
    breakTwoDigits(comp2Hi, comp2Lo, compNoise2, vd.radix);

    // pad each digit with four scalars to get l2-norm euqal to bound
    EVector padR, pad1Hi, pad1Lo, pad2Hi, pad2Lo;
    BigInt loBound = vd.radix * SQRT_JL;
    BigInt hi1Bound = (vd.B_eNoise1 / vd.radix) +int(ceil(sqrt(kk)));
    BigInt hi2Bound = (vd.B_eNoise2 / vd.radix) +int(ceil(sqrt(nn)));
#ifdef DEBUGGING
    std::cout <<"B_r=2^"<<log2BI(vd.B_r)
        << ", |rComp|^2=2^"<<log2BI(normSquaredBigInt(compR)) <<std::endl;
    std::cout <<"B_eNoise1=2^"<<log2BI(vd.B_eNoise1)
        << ", B_eNoise2=2^"<<log2BI(vd.B_eNoise2) <<std::endl;
    std::cout << "  |eNoise1|^2=2^"<<log2BI(normSquaredBigInt(compNoise1))
        << ", |eNoise2|^2=2^"<<log2BI(normSquaredBigInt(compNoise1)) <<std::endl;

    std::cout << "  |eNoise1Hi|^2=2^"<<log2BI(normSquaredBigInt(comp1Hi))
        << ", hi1Bound = 2^"<<log2BI(hi1Bound)<<std::endl;
    std::cout << "  |eNoise1Lo|^2=2^"<<log2BI(normSquaredBigInt(comp1Lo))
        << ", loBound = 2^"<<log2BI(loBound)<<std::endl;
    std::cout << "  |eNoise2Hi|^2=2^"<<log2BI(normSquaredBigInt(comp2Hi))
        << ", hi1Bound = 2^"<<log2BI(hi2Bound)<<std::endl;
    std::cout << "  |eNoise2Lo|^2=2^"<<log2BI(normSquaredBigInt(comp2Lo))
        << ", loBound = 2^"<<log2BI(loBound)<<std::endl;
#endif

    pad2exactNorm(compR, padR, vd.B_r);
    pad2exactNorm(comp1Hi, pad1Hi, hi1Bound);
    pad2exactNorm(comp1Lo, pad1Lo, loBound);
    pad2exactNorm(comp2Hi, pad2Hi, hi2Bound);
    pad2exactNorm(comp2Lo, pad2Lo, loBound);

    // commit to the compressed vectors and their padding

    vd.rCompCom = commit2(compR, vd.rCompIdx, vd.Gs, vd.Hs, pd.rCompRnd);
    vd.rPadCom = commit2(padR, vd.rPadIdx, vd.Gs, vd.Hs, pd.rPadRnd);
    vd.eComp1HiCom = commit2(comp1Hi, vd.eComp1HiIdx, vd.Gs, vd.Hs, pd.eComp1HiRnd);
    vd.ePad1HiCom = commit2(pad1Hi, vd.ePad1HiIdx, vd.Gs, vd.Hs, pd.ePad1HiRnd);
    vd.eComp1LoCom = commit2(comp1Lo, vd.eComp1LoIdx, vd.Gs, vd.Hs, pd.eComp1LoRnd);
    vd.ePad1LoCom = commit2(pad1Lo, vd.ePad1LoIdx, vd.Gs, vd.Hs, pd.ePad1LoRnd);
    vd.eComp2HiCom = commit2(comp2Hi, vd.eComp2HiIdx, vd.Gs, vd.Hs, pd.eComp2HiRnd); 
    vd.ePad2HiCom = commit2(pad2Hi, vd.ePad2HiIdx, vd.Gs, vd.Hs, pd.ePad2HiRnd);
    vd.eComp2LoCom = commit2(comp2Lo, vd.eComp2LoIdx, vd.Gs, vd.Hs, pd.eComp2LoRnd);
    vd.ePad2LoCom = commit2(pad2Lo, vd.ePad2LoIdx, vd.Gs, vd.Hs, pd.ePad2LoRnd);

    // include these commitments in the Merlin transcript
    vd.mer->processPoint("RegevEncR", vd.rCompCom);
    vd.mer->processPoint(std::string(), vd.rPadCom);

    vd.mer->processPoint("RegevEnc1Hi", vd.eComp1HiCom);
    vd.mer->processPoint(std::string(), vd.ePad1HiCom);

    vd.mer->processPoint("RegevEnc1Lo", vd.eComp1LoCom);
    vd.mer->processPoint(std::string(), vd.ePad1LoCom);

    vd.mer->processPoint("RegevEnc2Hi", vd.eComp2HiCom);
    vd.mer->processPoint(std::string(), vd.ePad2HiCom);

    vd.mer->processPoint("RegevEnc2Lo", vd.eComp2LoCom);
    vd.mer->processPoint(std::string(), vd.ePad2LoCom);

    // Record the encryption linear constraints

    DLPROOFS::LinConstraint* lCnstr1 = &(vd.linConstr[vd.eLin1Idx]);
    DLPROOFS::LinConstraint* lCnstr2 = &(vd.linConstr[vd.eLin2Idx]);
    for (int i=0; i<GlobalKey::ell; i++)
      lCnstr1[i] = DLPROOFS::LinConstraint(); // make sure they are empty
    for (int i=0; i<GlobalKey::ell; i++)
      lCnstr2[i] = DLPROOFS::LinConstraint(); // make sure they are empty

    // First constraint: <x1*R1*A,r>
    //                   +<x1,eComp1Lo> +<x1*radix1,eCompHi> = x1*R1*ct1

    EVector xvec1;
    Element x1 = vd.mer->newElement("RegevEncChallenge1");
    powerVector(xvec1, x1, nRrows);

    // The term x1*R1*ct1
    EVector xR1 = xvec1*R1;
    setEqsTo(lCnstr1, innerProduct(xR1, ct1));

    // The term <x1*R1*A,r>
    auto start = std::chrono::steady_clock::now();
    {auto xR1A = xR1 * vd.gk->A;
    crsTicks += std::chrono::duration_cast<std::chrono::milliseconds>(
        std::chrono::steady_clock::now()-start).count();
    expandConstraints(lCnstr1, vd.rIdx, xR1A);}

    // The terms <x1,eComp1Lo>  and <x1*radix1,eCompHi>
    expandConstraints(lCnstr1, vd.eComp1LoIdx, xvec1);
    Scalar B_e1; conv(B_e1, vd.radix);
    expandConstraints(lCnstr1, vd.eComp1HiIdx, B_e1*xvec1);

    // Second constraint: <x2*R2*B,r> +<x2,eCompLo>
    //   + <radix2*x2,eCompHi> + <g*x2*R2,ptxt> = x2*R2*ct2
    EVector xvec2;
    Element x2 = vd.mer->newElement("RegevEncChallenge2");
    powerVector(xvec2, x2, nRrows);

    // The term x2*R2*ct2
    EVector xR2 = xvec2*R2;
    setEqsTo(lCnstr2, innerProduct(xR2, ct2));

    // The term <x2*R2*B,r>
    expandConstraints(lCnstr2, vd.rIdx, xR2 * vd.gk->B);

    // The terms <x2,eCompLo> and <radix2*x2,eCompHi>
    expandConstraints(lCnstr2, vd.eComp2LoIdx, xvec2);
    Scalar B_e2; conv(B_e2, vd.radix);
    expandConstraints(lCnstr2, vd.eComp2HiIdx, B_e2*xvec2);

    // The term <g*x2*R2, ptxt> 
    makeConstraints(lCnstr2, vd.pt2Idx, vd.gk->g()*xR2);

    // Third constraint: <x3, rComp> -<x3*R3,r> = 0
    EVector xvec3;
    DLPROOFS::LinConstraint* lCnstr3 = &(vd.linConstr[vd.rLinIdx]);
    Element x3 = vd.mer->newElement("RegevEncChallenge3");
    powerVector(xvec3, x3, nRrows);

    // The eqsTo element is zero
    setEqsTo(lCnstr3, Element());

    // The term <x3,rComp> 
    expandConstraints(lCnstr3, vd.rCompIdx, xvec3);

    // The term -<x3*R3,r>
    expandConstraints(lCnstr3, vd.rIdx, -xvec3*R3);

    // Record the linear-constraint witnesses
    addEVec2Map(pd.linWitness, compR, vd.rCompIdx);
    addEVec2Map(pd.linWitness, padR, vd.rPadIdx);
    addEVec2Map(pd.linWitness, comp1Hi, vd.eComp1HiIdx);
    addEVec2Map(pd.linWitness, pad1Hi, vd.ePad1HiIdx);
    addEVec2Map(pd.linWitness, comp1Lo, vd.eComp1LoIdx);
    addEVec2Map(pd.linWitness, pad1Lo, vd.ePad1LoIdx);
    addEVec2Map(pd.linWitness, comp2Hi, vd.eComp2HiIdx);
    addEVec2Map(pd.linWitness, pad2Hi, vd.ePad2HiIdx);
    addEVec2Map(pd.linWitness, comp2Lo, vd.eComp2LoIdx);
    addEVec2Map(pd.linWitness, pad2Lo, vd.ePad2LoIdx);
    addEVec2Map(pd.linWitness, rnd, vd.rIdx);
    addSVec2Map(pd.linWitness, ptxt, vd.pt2Idx);
#ifdef DEBUGGING
    for (int i=0; i<scalarsPerElement(); i++)
        if (!checkConstraintLoose(lCnstr1[i], pd.linWitness)) {
            std::cout << "encryption linear constraint "<<(i+1)<<" failed\n";
        }
    for (int i=0; i<scalarsPerElement(); i++)
        if (!checkConstraintLoose(lCnstr2[i], pd.linWitness)) {
            std::cout << "encryption linear constraint "<<(i+3)<<" failed\n";
        }
    for (int i=0; i<scalarsPerElement(); i++)
        if (!checkConstraintLoose(lCnstr3[i], pd.linWitness)) {
            std::cout << "encryption linear constraint "<<(i+5)<<" failed\n";
        }
#endif

    // Norm constraints: |paddedRnd|^2=B_r^2, |paddedNoise1|^2=B_eNoise1^2
    //                   |paddedNoise2Hi|^2=|paddedNoise2Lo|^2=B_eNoise2^2

    // Norm constraint for the compressed randomness
    conv(vd.normConstr[vd.rQuadIdx].equalsTo, square(vd.B_r));
    ALGEBRA::addRange2Set(vd.normConstr[vd.rQuadIdx].indexes, vd.rCompIdx, JLDIM);
    ALGEBRA::addRange2Set(vd.normConstr[vd.rQuadIdx].indexes, vd.rPadIdx, PAD_SIZE);

    // Norm constraints for the high and lo digits of compressed noise1
    conv(vd.normConstr[vd.e1HiQuadIdx].equalsTo, square(hi1Bound));
    ALGEBRA::addRange2Set(vd.normConstr[vd.e1HiQuadIdx].indexes, vd.eComp1HiIdx, JLDIM);
    ALGEBRA::addRange2Set(vd.normConstr[vd.e1HiQuadIdx].indexes, vd.ePad1HiIdx, PAD_SIZE);

    conv(vd.normConstr[vd.e1LoQuadIdx].equalsTo, square(loBound));
    ALGEBRA::addRange2Set(vd.normConstr[vd.e1LoQuadIdx].indexes, vd.eComp1LoIdx, JLDIM);
    ALGEBRA::addRange2Set(vd.normConstr[vd.e1LoQuadIdx].indexes, vd.ePad1LoIdx, PAD_SIZE);

    // Norm constraints for the high and lo digits of compressed noise2
    conv(vd.normConstr[vd.e2HiQuadIdx].equalsTo, square(hi2Bound));
    ALGEBRA::addRange2Set(vd.normConstr[vd.e2HiQuadIdx].indexes, vd.eComp2HiIdx, JLDIM);
    ALGEBRA::addRange2Set(vd.normConstr[vd.e2HiQuadIdx].indexes, vd.ePad2HiIdx, PAD_SIZE);

    conv(vd.normConstr[vd.e2LoQuadIdx].equalsTo, square(loBound));
    ALGEBRA::addRange2Set(vd.normConstr[vd.e2LoQuadIdx].indexes, vd.eComp2LoIdx, JLDIM);
    ALGEBRA::addRange2Set(vd.normConstr[vd.e2LoQuadIdx].indexes, vd.ePad2LoIdx, PAD_SIZE);

    // Record the norm-constraint witnesses
    addEVec2Map(pd.quadWitnessG, compR, vd.rCompIdx);
    addEVec2Map(pd.quadWitnessG, padR, vd.rPadIdx);
    addEVec2Map(pd.quadWitnessG, comp1Hi, vd.eComp1HiIdx);
    addEVec2Map(pd.quadWitnessG, pad1Hi, vd.ePad1HiIdx);
    addEVec2Map(pd.quadWitnessG, comp1Lo, vd.eComp1LoIdx);
    addEVec2Map(pd.quadWitnessG, pad1Lo, vd.ePad1LoIdx);
    addEVec2Map(pd.quadWitnessG, comp2Hi, vd.eComp2HiIdx);
    addEVec2Map(pd.quadWitnessG, pad2Hi, vd.ePad2HiIdx);
    addEVec2Map(pd.quadWitnessG, comp2Lo, vd.eComp2LoIdx);
    addEVec2Map(pd.quadWitnessG, pad2Lo, vd.ePad2LoIdx);

#ifdef DEBUGGING
    if (!checkConstraintLoose(vd.normConstr[vd.rQuadIdx], pd.quadWitnessG, pd.quadWitnessG)) {
        std::cout << "encryption norm constraint 2 failed\n";
    }
    if (!checkConstraintLoose(vd.normConstr[vd.e1HiQuadIdx], pd.quadWitnessG,pd.quadWitnessG)) {
        std::cout << "encryption norm constraint 3 failed\n";
    }
    if (!checkConstraintLoose(vd.normConstr[vd.e1LoQuadIdx], pd.quadWitnessG,pd.quadWitnessG)) {
        std::cout << "encryption norm constraint 4 failed\n";
    }
    if (!checkConstraintLoose(vd.normConstr[vd.e2HiQuadIdx],pd.quadWitnessG,pd.quadWitnessG)){
        std::cout << "encryption norm constraint 5 failed\n";
    }
    if (!checkConstraintLoose(vd.normConstr[vd.e2LoQuadIdx],pd.quadWitnessG,pd.quadWitnessG)){
        std::cout << "encryption norm constraint 6 failed\n";
    }
#endif
    // Copy the padded vectors to pd.compressed
    int eIdx = vd.rCompIdx / scalarsPerElement();
    for (auto& x : compR) { pd.compressed[eIdx++] = x; }
    eIdx = vd.rPadIdx / scalarsPerElement();
    for (auto& x : padR)  { pd.compressed[eIdx++] = x; }
    eIdx = vd.eComp1HiIdx / scalarsPerElement();
    for (auto& x : comp1Hi) { pd.compressed[eIdx++] = x; }
    eIdx = vd.ePad1HiIdx / scalarsPerElement();
    for (auto& x : pad1Hi)  { pd.compressed[eIdx++] = x; }
    eIdx = vd.eComp1LoIdx / scalarsPerElement();
    for (auto& x : comp1Lo) { pd.compressed[eIdx++] = x; }
    eIdx = vd.ePad1LoIdx / scalarsPerElement();
    for (auto& x : pad1Lo)  { pd.compressed[eIdx++] = x; }
    eIdx = vd.eComp2HiIdx / scalarsPerElement();
    for (auto& x : comp2Hi) { pd.compressed[eIdx++] = x; }
    eIdx = vd.ePad2HiIdx / scalarsPerElement();
    for (auto& x : pad2Hi)  { pd.compressed[eIdx++] = x; }
    eIdx = vd.eComp2LoIdx / scalarsPerElement();
    for (auto& x : comp2Lo) { pd.compressed[eIdx++] = x; }
    eIdx = vd.ePad2LoIdx / scalarsPerElement();
    for (auto& x : pad2Lo)  { pd.compressed[eIdx++] = x; }
}

// Proof of key-generation. We assume that the ProverData,VerifierData
// are already initialized.
// pkNum is the indec of the public key in the GlobalKey.
void proveKeyGen(ProverData& pd, int pkNum,
        const ALGEBRA::EVector& skey, const ALGEBRA::EVector& noise)
{
    VerifierData& vd = *(pd.vd);
    int kk = vd.gk->kay * GlobalKey::ell;

    // commitment to the secret key
    vd.sk2Com = commit(skey, vd.sk2Idx, vd.Gs, pd.sk2Rnd);
    vd.mer->processPoint("RegevSK", vd.sk2Com);

    // Get the challenge matrices and set skComp=R1*sk2, eComp = R2*noise
    TernaryEMatrix R1, R2;
    int nRcols = JLDIM/scalarsPerElement();
    vd.mer->newTernaryEMatrix("RegevKeyGenR1", R1, vd.gk->kay, nRcols);
    vd.mer->newTernaryEMatrix("RegevKeyGenR2", R2, vd.gk->kay, nRcols);
    EVector ekComp = noise*R1;
    EVector skComp = skey*R2;

    EVector eCompHi, eCompLo;
    breakTwoDigits(eCompHi, eCompLo, ekComp, vd.radix);

    // pad each vector/digit with four scalars to get l2-norm euqal to bound
    EVector skPad, ePadHi, ePadLo;
    BigInt hiBound = (vd.B_kNoise / vd.radix) +int(ceil(sqrt(kk)));
    BigInt loBound = vd.radix * SQRT_JL;
    Scalar B_ek; conv(B_ek, vd.radix);
#ifdef DEBUGGING
    std::cout <<"B_sk=2^"<<log2BI(vd.B_sk)
        << ", |skComp|^2=2^"<<log2BI(normSquaredBigInt(skComp))<<std::endl;
    std::cout <<"B_kNoise=2^"<<log2BI(vd.B_kNoise)
        << ", radix = 2^"<<log2BI(vd.radix)<<std::endl;
    std::cout << "  |ekCompHi|^2=2^"<<log2BI(normSquaredBigInt(eCompHi))
        << ", hiBound = 2^"<<log2BI(hiBound)<<std::endl;
    std::cout << "  |ekCompLo|^2=2^"<<log2BI(normSquaredBigInt(eCompLo))
        << ", loBound = 2^"<<log2BI(loBound)<<std::endl;
#endif
    pad2exactNorm(skComp, skPad, vd.B_sk);
    pad2exactNorm(eCompHi, ePadHi, hiBound);
    pad2exactNorm(eCompLo, ePadLo, loBound);

    // Commit to the vectors and paddings
    vd.sk2CompCom = commit2(skComp, vd.sk2CompIdx, vd.Gs, vd.Hs, pd.sk2CompRnd);
    vd.sk2PadCom = commit2(skPad, vd.sk2PadIdx, vd.Gs, vd.Hs, pd.sk2PadRnd);
    vd.kCompHiCom = commit2(eCompHi, vd.kCompHiIdx, vd.Gs, vd.Hs, pd.kCompHiRnd);
    vd.kPadHiCom = commit2(ePadHi, vd.kPadHiIdx, vd.Gs, vd.Hs, pd.kPadHiRnd);
    vd.kCompLoCom = commit2(eCompLo, vd.kCompLoIdx, vd.Gs, vd.Hs, pd.kCompLoRnd);
    vd.kPadLoCom = commit2(ePadLo, vd.kPadLoIdx, vd.Gs, vd.Hs, pd.kPadLoRnd);

    // include these commitments in the Merlin transcript
    vd.mer->processPoint("RegevKeyGenSK", vd.sk2CompCom);
    vd.mer->processPoint(std::string(), vd.sk2PadCom);

    vd.mer->processPoint("RegevKGHi", vd.kCompHiCom);
    vd.mer->processPoint(std::string(), vd.kPadHiCom);

    vd.mer->processPoint("RegevKGHi", vd.kCompLoCom);
    vd.mer->processPoint(std::string(), vd.kPadLoCom);

    DLPROOFS::LinConstraint* lCnstr1 = &(vd.linConstr[vd.kLinIdx]);
    DLPROOFS::LinConstraint* lCnstr2 = &(vd.linConstr[vd.sk2LinIdx]);
    for (int i=0; i<GlobalKey::ell; i++)
      lCnstr1[i] = DLPROOFS::LinConstraint(); // make sure they are empty
    for (int i=0; i<GlobalKey::ell; i++)
      lCnstr2[i] = DLPROOFS::LinConstraint(); // make sure they are empty

    // First linear constraint: <skey,A*R1*x1> +<eLo,x1> +<eHi,radix*x1> = b*R1*x1
    EVector xvec1;
    Element x1 = vd.mer->newElement("RegevKGChallenge1");
    powerVector(xvec1, x1, nRcols);

    // The term b*R*x1
    EVector R1x = R1*xvec1;
    setEqsTo(lCnstr1, innerProduct(R1x, vd.gk->B[pkNum]));

    // The term <skey,A*R1*x1> 
    expandConstraints(lCnstr1, vd.sk2Idx, vd.gk->A * R1x);

    // The terms <eLo,x1> and <eHi,radix*x1> 
    expandConstraints(lCnstr1, vd.kCompLoIdx, xvec1);
    expandConstraints(lCnstr1, vd.kCompHiIdx, B_ek*xvec1);

    // Second linear constraint: <skComp,x2> -<skey, R2*x2> = 0
    EVector xvec2;
    Element x2 = vd.mer->newElement("RegevKGChallenge2");
    powerVector(xvec2, x2, nRcols);

    // The free term is zero
    setEqsTo(lCnstr2, Element());

    // The term <skComp, x2>
    expandConstraints(lCnstr2, vd.sk2CompIdx, xvec2);

    // The term -<skey, R2*x2>
    expandConstraints(lCnstr2, vd.sk2Idx, -(R2*xvec2));

    // Record the linear-constraint witnesses
    addEVec2Map(pd.linWitness, skey, vd.sk2Idx);
    addEVec2Map(pd.linWitness, skComp, vd.sk2CompIdx);
    addEVec2Map(pd.linWitness, skPad, vd.sk2PadIdx);
    addEVec2Map(pd.linWitness, eCompHi, vd.kCompHiIdx);
    addEVec2Map(pd.linWitness, ePadHi, vd.kPadHiIdx);
    addEVec2Map(pd.linWitness, eCompLo, vd.kCompLoIdx);
    addEVec2Map(pd.linWitness, ePadLo, vd.kPadLoIdx);
#ifdef DEBUGGING
    if (!checkConstraintLoose(*lCnstr1, pd.linWitness)) {
        std::cout << "keygen linear constraint 1 failed\n";
    }
    if (!checkConstraintLoose(*lCnstr2, pd.linWitness)) {
        std::cout << "keygen linear constraint 2 failed\n";
    }
#endif

    // Record the norm constraints |paddedskComp|^2=B_sk^2, 
    //        |paddedeCompHi|^2=hiBound^2, |paddedeCompLi|^2=loBound^2.

    conv(vd.normConstr[vd.sk2QuadIdx].equalsTo, square(vd.B_sk));
    ALGEBRA::addRange2Set(vd.normConstr[vd.sk2QuadIdx].indexes, vd.sk2CompIdx, JLDIM);
    ALGEBRA::addRange2Set(vd.normConstr[vd.sk2QuadIdx].indexes, vd.sk2PadIdx, PAD_SIZE);

    conv(vd.normConstr[vd.kHiQuadIdx].equalsTo, square(hiBound));
    ALGEBRA::addRange2Set(vd.normConstr[vd.kHiQuadIdx].indexes, vd.kCompHiIdx, JLDIM);
    ALGEBRA::addRange2Set(vd.normConstr[vd.kHiQuadIdx].indexes, vd.kPadHiIdx, PAD_SIZE);

    conv(vd.normConstr[vd.kLoQuadIdx].equalsTo, square(loBound));
    ALGEBRA::addRange2Set(vd.normConstr[vd.kLoQuadIdx].indexes, vd.kCompLoIdx, JLDIM);
    ALGEBRA::addRange2Set(vd.normConstr[vd.kLoQuadIdx].indexes, vd.kPadLoIdx, PAD_SIZE);

    // Record the norm-constraint witnesses
    addEVec2Map(pd.quadWitnessG, skComp, vd.sk2CompIdx);
    addEVec2Map(pd.quadWitnessG, skPad, vd.sk2PadIdx);
    addEVec2Map(pd.quadWitnessG, eCompHi, vd.kCompHiIdx);
    addEVec2Map(pd.quadWitnessG, ePadHi, vd.kPadHiIdx);
    addEVec2Map(pd.quadWitnessG, eCompLo, vd.kCompLoIdx);
    addEVec2Map(pd.quadWitnessG, ePadLo, vd.kPadLoIdx);
#ifdef DEBUGGING
    if (!checkConstraintLoose(vd.normConstr[vd.sk2QuadIdx],pd.quadWitnessG,pd.quadWitnessG)){
        std::cout << "keygen norm constraint 7 failed\n";
    }
    if (!checkConstraintLoose(vd.normConstr[vd.kHiQuadIdx],pd.quadWitnessG,pd.quadWitnessG)){
        std::cout << "keygen norm constraint 8 failed\n";
    }
    if (!checkConstraintLoose(vd.normConstr[vd.kLoQuadIdx],pd.quadWitnessG,pd.quadWitnessG)){
        std::cout << "keygen norm constraint 9 failed\n";
    }
#endif
    // Copy the padded vectors to pd.compressed
    int eIdx = vd.sk2CompIdx / scalarsPerElement();
    for (auto& x : skComp) { pd.compressed[eIdx++] = x; }
    eIdx = vd.sk2PadIdx / scalarsPerElement();
    for (auto& x : skPad)  { pd.compressed[eIdx++] = x; }
    eIdx = vd.kCompHiIdx / scalarsPerElement();
    for (auto& x : eCompHi) { pd.compressed[eIdx++] = x; }
    eIdx = vd.kPadHiIdx / scalarsPerElement();
    for (auto& x : ePadHi)  { pd.compressed[eIdx++] = x; }
    eIdx = vd.kCompLoIdx / scalarsPerElement();
    for (auto& x : eCompLo) { pd.compressed[eIdx++] = x; }
    eIdx = vd.kPadLoIdx / scalarsPerElement();
    for (auto& x : ePadLo)  { pd.compressed[eIdx++] = x; }
}

// Proof of correct re-sharing. It is assumed that pt1, pt2
// are already initialized in the ps structure
void proveReShare(ProverData& pd, const SVector& lagrange,
        const ALGEBRA::SVector& pt1, const ALGEBRA::SVector& pt2) {
    VerifierData& vd = *(pd.vd);

    // Recall that we have the parity-check matrix H=vd.sp.H such that a
    // vector x is a valid sharing iff H*x=0. In our case the 1st entry
    // in x is the secret, computed as x[0]=\sum_{j<t} lagrange[j]*pt1[j],
    // and the other entries are just the entries of pt2. Hence the
    // condition for valid re-sharing is
    //      H * ((\sum_j lagrange[j]*pt1[j]) pt2[0] ... pt2[n-1])^T = 0.
    // Each row of the above matrix equation is a linear constraint, namely
    // for all i\in [0,n-t] we have the linear constraint:
    //     \sum_{j=0}^{t-1} (H[i][0]*lagrange[j])*pt1[j] 
    //      + \sum_{j=0}^{n-1} H[i][j+1]*pt2[j] = 0.

    const SMatrix& H = vd.sp->H;
    assert(pt1.length()==vd.gk->tee && lagrange.length()==pt1.length()
           && pt2.length()==vd.gk->enn && H.NumCols()==1+pt2.length());
    int constrIdx = vd.reShrLinIdx; // The 1st re-sharing constraint
    assert(constrIdx+H.NumRows() <= vd.linConstr.size());
    for (int i=0; i<H.NumRows(); i++) { // the i'th constraint
        DLPROOFS::LinConstraint& lCnstr = vd.linConstr[constrIdx++];
        lCnstr = DLPROOFS::LinConstraint(); // make sure it is empty

        // The terms H[i][0]*lagrange[j] * pt1[j]
        int varIdx = vd.pt1Idx;
        for (int j=0; j<vd.gk->tee; j++) {
            CRV25519::Scalar s;
            conv(s, H[i][0]*lagrange[j]); // convert to CRV25519::Scalar
            lCnstr.addTerm(varIdx++, s);
        }
        // The terms H[i][j+1] * pt2[j]
        varIdx = vd.pt2Idx;
        for (int j=1; j<=vd.gk->enn; j++) {
            CRV25519::Scalar s;
            conv(s, H[i][j]);
            lCnstr.addTerm(varIdx++, s);
        }
    }
#ifdef DEBUGGING
    SVector shares;
    resize(shares, pt2.length()+1);
    shares[0] = innerProduct(lagrange, pt1);
    for (int i=1; i<=pt2.length(); i++)
        shares[i] = pt2[i-1];
    SVector zeroVec; resize(zeroVec, H.NumRows());
    assert(H*shares == zeroVec);

    // verify the constraints
    // The variables from pt1, pt2 are already part of the witness, as we
    // assume that this is called after proofs of decryption and encryption
    for (int i=vd.reShrLinIdx; i<constrIdx; i++) { // the i'th constraint
        if (!checkConstraintLoose(vd.linConstr[i], pd.linWitness)) {
            std::cout << "constraints #"<<(i-vd.reShrLinIdx+1)<<" for re-sharing failed\n";
        }
    }
#endif
}

// Approximate l-infty proof of shortness for the padded vectors. It
// is assumed that the proofs of decryption, encryption, and keygen
// were already done, and pd.compressed contain tthe concatenation
// of all the padded vectors (eight vectors over GF(P^ell), each of
// dimension 130).
void proveSmallness(ProverData& pd) {
    VerifierData& vd = *(pd.vd);

    // Rejection sampling: Repeatedly choose random masking vectors y and
    // matrices R until both u=pd.compressed *R and z=u+y are small enough.
    // The have B_smallness = 2^smlnsBits *128/129, the vector y is chosen
    // from [+- 2^smlnsBits]^128, and we check that
    //      |u|_{infty} < B_smallness/128, |z|_{infty} < B_smallness

    int paddingElements = PAD_SIZE / scalarsPerElement();
    int JLelements = JLDIM / scalarsPerElement();

    int nCols = LINYDIM/scalarsPerElement();
    int nRows = 10*(JLDIM+PAD_SIZE)/scalarsPerElement();

    assert(pd.compressed.length() == nRows);

    EVector u, y;
    TernaryEMatrix R;

    resize(y, nCols);
    BoundedSizeElement randomzr(vd.smlnsBits); // for choosing in [+-2^smlnsBits]
    int uFailed = 0, zFailed = 0;
    for (int nTrials=0; true; nTrials++) {
        if (nTrials > 99) {
            throw std::runtime_error("proveSmallness: too many retrys choosing R");
        }
        auto merBkp = *(vd.mer);

        // choose a random y and commit to it
        for (Element& el: y) randomzr.randomize(el);
            // FIXME: it would have been better to use Merlin transcript
            // for choosing this masking vectors. It would requires an
            // implemenetation of choosing bounded-size random numbers
            // using Merlin transcrypt

        vd.yCom = commit(y, vd.yIdx, vd.Gs, pd.yRnd);
        merBkp.processPoint("smallnessPf", vd.yCom);

        merBkp.newTernaryEMatrix("Smallness", R, nRows, nCols);
        u = pd.compressed * R;
        vd.z = u + y;

        // check that u,z are small enough
        BigInt uBound = vd.B_smallness/LINYDIM; // B_smallness/128
        if (lInftyNorm(u) <= uBound && lInftyNorm(vd.z) <= vd.B_smallness) {
#ifdef DEBUGGING
            std::cout<<"proveSmallness computed u,z in "<<(nTrials+1)
            << " trials, (uFailed,zFailed)=("<<uFailed<<','<<zFailed<<")\n";
#endif
            *vd.mer = merBkp;
            break;
        }
#ifdef DEBUGGING
        if (lInftyNorm(u) > uBound) uFailed++;
        if (lInftyNorm(vd.z) > vd.B_smallness) zFailed++;
        std::cout << "smallness |secrets|_infty=2^"<<log2BI(lInftyNorm(pd.compressed))
            << ", |secrets|^2=2^"<<log2BI(normSquaredBigInt(pd.compressed))
            << std::endl;
        std::cout << "    |u|_infty=2^" << log2BI(lInftyNorm(u))
            << ", |u|^2=2^"<<log2BI(normSquaredBigInt(u)) << std::endl;
        std::cout << "    |y|_infty=2^" << log2BI(lInftyNorm(y))
            << ", |z|_infty=2^" << log2BI(lInftyNorm(vd.z)) << std::endl;
#endif
    } // if u or z are too long, choose another y and try again

    // A challenge scalar x, defines the vector xvec=(1,x,x^2,...)
    vd.mer->processVector(vd.z, /*label=*/(unsigned char*)"masked reply",
                          /*label length=*/12);

    // Record the linear constraint <pd.compressed,R*x> + <y,x> = <z,x>
    DLPROOFS::LinConstraint* lCnstr = &(vd.linConstr[vd.smlnsLinIdx]);
    for (int i=0; i<GlobalKey::ell; i++)
      lCnstr[i] = DLPROOFS::LinConstraint(); // make sure they are empty

    assert(lCnstr[0].equalsTo == CRV25519::Scalar() && lCnstr[0].terms.size()==0);
    assert(lCnstr[1].equalsTo == CRV25519::Scalar() && lCnstr[1].terms.size()==0);

    EVector xvec;
    Element x = vd.mer->newElement("SmallnessChallenge");
    powerVector(xvec, x, nCols); // the vector xvec=(1,x,x^2,...)

    // The term <z,x>
    setEqsTo(lCnstr, innerProduct(vd.z, xvec));

    // The term <pd.compressed,R*x>
    auto Rx = R*xvec;
    expandConstraints(lCnstr, 0, Rx);

    // The term <y,x>
    expandConstraints(lCnstr, vd.yIdx, xvec);
    addEVec2Map(pd.linWitness, y, vd.yIdx);
#ifdef DEBUGGING
    assert(innerProduct(pd.compressed, Rx) + innerProduct(y,xvec) == innerProduct(vd.z,xvec));
    for (int i=0; i<scalarsPerElement(); i++) { // check the linear constraints
        if (!checkConstraintLoose(lCnstr[i], pd.linWitness)) {
            std::cout << "constraints #"<<(i+1)<<" for smallness failed\n";
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
    // the quadratic (as) vs ones that only apppear in linear (bs)
    int wIdx=DLPROOFS::splitPtxtVec(as, bs, linCnstr.terms, quadCnstr.indexes);
    assert(wIdx == vd.wIdx);

    // 2c. Modify the commitments to reflect the change in witness
    vd.dCompHiCom += vd.dPadHiCom;
    vd.dCompHiCom *= rVec[vd.dHiQuadIdx];

    vd.dCompLoCom += vd.dPadLoCom;
    vd.dCompLoCom *= rVec[vd.dLoQuadIdx];

    vd.rCompCom   += vd.rPadCom;
    vd.rCompCom   *= rVec[vd.rQuadIdx];

    vd.eComp1HiCom+= vd.ePad1HiCom;
    vd.eComp1HiCom*= rVec[vd.e1HiQuadIdx];

    vd.eComp1LoCom+= vd.ePad1LoCom;
    vd.eComp1LoCom*= rVec[vd.e1LoQuadIdx];

    vd.eComp2HiCom+= vd.ePad2HiCom;
    vd.eComp2HiCom*= rVec[vd.e2HiQuadIdx];

    vd.eComp2LoCom+= vd.ePad2LoCom;
    vd.eComp2LoCom*= rVec[vd.e2LoQuadIdx];

    vd.sk2CompCom += vd.sk2PadCom;
    vd.sk2CompCom *= rVec[vd.sk2QuadIdx];

    vd.kCompHiCom += vd.kPadHiCom;
    vd.kCompHiCom *= rVec[vd.kHiQuadIdx];

    vd.kCompLoCom += vd.kPadLoCom;
    vd.kCompLoCom *= rVec[vd.kLoQuadIdx];

   // Step 3. Aggregate the commitments
    
    // 3a. The commitment in the linear-only constraint
    linCom = vd.pt1Com +vd.sk1Com +vd.pt2Com +vd.rCom +vd.sk2Com +vd.yCom;

    // 3a. The commitment in the quadratic constraint
    quadCom = vd.dCompHiCom +vd.dCompLoCom +vd.rCompCom +vd.eComp1HiCom
        +vd.eComp1LoCom +vd.eComp2HiCom +vd.eComp2LoCom +vd.sk2CompCom
        +vd.kCompHiCom +vd.kCompLoCom;
}

void ReadyToProve::aggregateProver(ProverData& pd)
{
    // Reduce to a single quadratic and a single linear constraint
    VerifierData& vd = *pd.vd;
    aggregateVerifier1(vd);

    // The aggregate function implies modifying the secret variables
    // in the quadratic equations, and hence also the commitments and
    // their corresponding randomness

    for (int i=0; i<rVec.size(); i++) { // adjust the witnesses, w -> w*factor
        for (auto& idx: vd.normConstr[i].indexes)
            pd.quadWitnessG[idx] *= rVec[i];
    }

    // Adjust the commitment randomness
    pd.dCompHiRnd += pd.dPadHiRnd;
    pd.dCompHiRnd *= rVec[vd.dHiQuadIdx];

    pd.dCompLoRnd += pd.dPadLoRnd;
    pd.dCompLoRnd *= rVec[vd.dLoQuadIdx];

    pd.rCompRnd   += pd.rPadRnd;
    pd.rCompRnd   *= rVec[vd.rQuadIdx];

    pd.eComp1HiRnd+= pd.ePad1HiRnd;
    pd.eComp1HiRnd*= rVec[vd.e1HiQuadIdx];

    pd.eComp1LoRnd+= pd.ePad1LoRnd;
    pd.eComp1LoRnd*= rVec[vd.e1LoQuadIdx];

    pd.eComp2HiRnd+= pd.ePad2HiRnd;
    pd.eComp2HiRnd*= rVec[vd.e2HiQuadIdx];

    pd.eComp2LoRnd+= pd.ePad2LoRnd;
    pd.eComp2LoRnd*= rVec[vd.e2LoQuadIdx];

    pd.sk2CompRnd += pd.sk2PadRnd;
    pd.sk2CompRnd *= rVec[vd.sk2QuadIdx];

    pd.kCompHiRnd += pd.kPadHiRnd;
    pd.kCompHiRnd *= rVec[vd.kHiQuadIdx];

    pd.kCompLoRnd += pd.kPadLoRnd;
    pd.kCompLoRnd *= rVec[vd.kLoQuadIdx];

    // Aggregate the commitment randomness for linear-only variables
    lComRnd = pd.pt1Rnd +pd.sk1Rnd +pd.pt2Rnd +pd.rRnd +pd.sk2Rnd +pd.yRnd;

    // Aggregate commitment randomness for the quadratic variables
    qComRnd = pd.dCompHiRnd +pd.dCompLoRnd +pd.rCompRnd +pd.eComp1HiRnd
        +pd.eComp1LoRnd +pd.eComp2HiRnd +pd.eComp2LoRnd +pd.sk2CompRnd
        +pd.kCompHiRnd +pd.kCompLoRnd;

    // reset original constraints
     {DLPROOFS::LinConstraint emptyLin;
     DLPROOFS::QuadConstraint emptyQuad;
    for (auto& lc : vd.linConstr) lc = emptyLin;
    for (auto& qc : pd.vd->normConstr) qc = emptyQuad;}

#ifdef DEBUGGING
    assert(checkConstraintLoose(quadCnstr, pd.quadWitnessG, pd.quadWitnessG));
    {std::vector<CRV25519::Scalar> linWt;
    std::vector<CRV25519::Point> linGs;
    for (auto& b: bs) { 
        linWt.push_back(pd.linWitness[b.first]);
        linGs.push_back(vd.Gs[b.first]);
    }
    assert(DLPROOFS::verifyCom(linCom, linGs.data(), linWt.data(), linGs.size(),lComRnd));
    }

    {std::vector<CRV25519::Scalar> wt;
    std::vector<Point> gs, hs;
    for (auto i: quadCnstr.indexes) {
        gs.push_back(vd.Gs[i]);
        hs.push_back(vd.Hs[i]);
        wt.push_back(pd.quadWitnessG[i]);
    }
    assert(DLPROOFS::verifyCom2(quadCom, gs.data(), wt.data(),
                                hs.data(), wt.data(), gs.size(), qComRnd));
    }
#endif

    // Compute and commit to the outcome of the linear-only constraint
    pd.linWitness[vd.wIdx] = pd.quadWitnessG[vd.wIdx]
                        = DLPROOFS::innerProduct(bs, pd.linWitness);

    const CRV25519::Scalar& w = pd.quadWitnessG[vd.wIdx];// just for convenience
    pd.wRnd = CRV25519::randomScalar();
    assert(vd.wIdx == vd.Gs.size()-1);
    Point& wG = vd.Gs[vd.wIdx];
    vd.wCom = Point::base()*pd.wRnd + wG*w;

    // Add commitment to w to both linCom and quadCom
    linCom += vd.wCom;
    lComRnd += pd.wRnd;
    quadCom += vd.wCom;
    qComRnd += pd.wRnd;

    bs[vd.wIdx].setInteger(-1); // add the term wIdx -> -1
#ifdef DEBUGGING
    // check the commitments again
    {std::vector<CRV25519::Scalar> linWt;
    std::vector<CRV25519::Point> linGs;
    for (auto& b: bs) { 
        linWt.push_back(pd.linWitness[b.first]);
        linGs.push_back(vd.Gs[b.first]);
    }
    assert(DLPROOFS::verifyCom(linCom, linGs.data(), linWt.data(), linGs.size(),lComRnd));
    }
    {std::vector<CRV25519::Scalar> wtG;
    std::vector<Point> gs, hs;
    for (auto i: quadCnstr.indexes) {
        gs.push_back(vd.Gs[i]);
        hs.push_back(vd.Hs[i]);
        wtG.push_back(pd.quadWitnessG[i]);
    }
    std::vector<CRV25519::Scalar> wtH = wtG;
    wtG.push_back(pd.quadWitnessG[vd.wIdx]);
    wtH.push_back(CRV25519::Scalar()); // add zero
    gs.push_back(vd.Gs[vd.wIdx]);
    hs.push_back(vd.Hs[vd.Hs.size()-1]);
    assert(DLPROOFS::verifyCom2(quadCom, gs.data(), wtG.data(),
                                hs.data(), wtH.data(), gs.size(), qComRnd));
    }
#endif
    //end = std::chrono::steady_clock::now();
    //ticks += std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();
    //std::cout << "prover-only aggregation uses "
    //    << (DLPROOFS::Point::counter - startExp) << " exponentiations, ";

    // enforce norm constraint and separate linear and quadratic variables
    aggregateVerifier2(vd);

    // release memory of intermediate vectors
    //start = std::chrono::steady_clock::now();
    rVec.clear(); uVec.clear(); as.clear(); bs.clear();

    // add the offsets deltaG, deltaH into quadWitnessG, quadWitnessH
    pd.quadWitnessH = pd.quadWitnessG;          // so far we only used quadWitnessG
    pd.quadWitnessH[vd.wIdx] = CRV25519::Scalar(); // quadWitnessH doesn't have w
    auto itWitG = pd.quadWitnessG.begin();
    auto itDeltaG = deltaG.begin();
    while (itWitG != pd.quadWitnessG.end() && itDeltaG != deltaG.end()) {
        assert(itWitG->first == itDeltaG->first);
        itWitG->second -= itDeltaG->second;
        itWitG++; itDeltaG++;
    }
    assert(itWitG == pd.quadWitnessG.end() && itDeltaG == deltaG.end());

    auto itWitH = pd.quadWitnessH.begin();
    auto itDeltaH = deltaH.begin();
    while (itWitH != pd.quadWitnessH.end() && itDeltaH != deltaH.end()) {
        assert(itWitH->first == itDeltaH->first);
        itWitH->second -= itDeltaH->second;
        itWitH++; itDeltaH++;
    }
    assert(itWitH == pd.quadWitnessH.end() && itDeltaH == deltaH.end());

#ifdef DEBUGGING
    assert(checkConstraint(quadCnstr, pd.quadWitnessG, pd.quadWitnessH));
    assert(checkConstraintLoose(linCnstr, pd.linWitness));
#endif
    // Leave in linWitness only the indexes from linCnstr
    auto itTerms = linCnstr.terms.begin();
    auto itWit = pd.linWitness.begin();
    while (itWit != pd.linWitness.end() && itTerms != linCnstr.terms.end()) {
        if (itTerms->first != itWit->first) // no term for this witness
            itWit = pd.linWitness.erase(itWit);
        else {
            itWit++;
            itTerms++;
        }
    }
    if (itWit != pd.linWitness.end()) // more entries left in witness
        pd.linWitness.erase(itWit, pd.linWitness.end());
#ifdef DEBUGGING
    assert(checkConstraint(linCnstr, pd.linWitness));
#endif

    //end = std::chrono::steady_clock::now();
    //ticks += std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();
    //std::cout << ticks << " millseconds\n";
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

void ReadyToProve::flattenLinPrv(ProverData& pd)
{
    VerifierData& vd = *pd.vd;
    assert(pd.linWitness.size()==linCnstr.terms.size()); // sanity check
    flattenLinVer(vd);              // first flatten the public parts

    linWtns.clear(); linWtns.reserve(pd.linWitness.size());
    for (auto& aPair: pd.linWitness) { // then flatten the witness
        linWtns.push_back(aPair.second);
    }
    pd.linWitness.clear();             // release memory
#ifdef DEBUGGING
    assert(innerProduct(linWtns.data(),linStmnt.data(),linStmnt.size())==linCnstr.equalsTo);
    assert(DLPROOFS::verifyCom(linCom, linGs.data(),
                               linWtns.data(),linWtns.size(),lComRnd));
#endif
}


void ReadyToProve::flattenQuadPrv(ProverData& pd)
{
    VerifierData& vd = *pd.vd;
    flattenQuadVer(vd);              // first flatten the public parts
    quadWtnsG.clear(); quadWtnsH.clear();
    quadWtnsG.reserve(pd.quadWitnessG.size()); // allocate memory
    quadWtnsH.reserve(pd.quadWitnessH.size());
    auto itG = pd.quadWitnessG.begin(); // then flatten the witnesses
    auto itH = pd.quadWitnessH.begin();
    while (itG != pd.quadWitnessG.end() && itH != pd.quadWitnessH.end()) {
        assert(itG->first == itH->first);
        quadWtnsG.push_back(itG->second);
        quadWtnsH.push_back(itH->second);
        itG++; itH++;
    }
    assert(itG==pd.quadWitnessG.end() && itH==pd.quadWitnessH.end());// sanity check
    pd.quadWitnessG.clear(); // release memory
    pd.quadWitnessH.clear();
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
