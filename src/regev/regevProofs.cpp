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

// Proof of decryption. We assume that the ProverData,VerifierData are
// already initialized, and that ProverData contains the padded sk1
// and VerifierData contains a commitment to it.
void proveDecryption(ProverData& pd, const SVector& ptxt,
        const EVector& noise, const EMatrix& ctMat, const EVector& ctVec)
{
    VerifierData& vd = *(pd.vd);
    pd.pt1 = (SVector*) &ptxt;
    pd.decErr = (EVector*) &noise;

#ifdef DEBUGGING
    // check that sk*ctMat + ptxt*g + moise = ctVec
    EVector ptxtTimesG;
    resize(ptxtTimesG, ptxt.length());
    for (int i=0; i<ptxtTimesG.length(); i++)
        ptxtTimesG[i] = ptxt[i] * vd.gk->g();
    assert(((*pd.sk1)*ctMat) + ptxtTimesG + noise == ctVec);
#endif

    // commitment to decrypted plaintext
    vd.pt1Com = commit(ptxt, vd.pt1Idx, vd.Gs, pd.pt1Rnd);
    vd.mer->processPoint("RegevDecPtxt", vd.pt1Com);

    // commitments to decryption noise subvectors
    int elementsPerSubvec= DEC_ERRV_SZ / scalarsPerElement();
    int paddingElements = PAD_SIZE / scalarsPerElement();

    assert(DEC_ERRV_SZ % scalarsPerElement() == 0);
    assert(PAD_SIZE % scalarsPerElement() == 0);
    assert(elementsPerSubvec * vd.nDecSubvectors == noise.length());

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
#if 0 //ifdef DEBUGGING
        std::cout << "noise subvec(idx="<<scalarIdx<<")=[";
        for (int ii=0; ii<elementsPerSubvec; ii++)
            std::cout << pretty(noise[elementIdx+ii])<<" ";
        std::cout << "]\n";

        std::cout << "padding subvec(idx="<<scalarPadIdx<<")=[";
        for (int ii=0; ii<paddingElements; ii++)
            std::cout << pretty(pd.decErrPadding[paddingIdx+ii])<<" ";
        std::cout << "]\n";
#endif
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
#if 0 // ifdef DEBUGGING
    NTL::ZZ_pX px;
    NTL::SetCoeff(px,0); // p(x)=1;
    Element x;
    conv(x,px);
#else
    Element x = vd.mer->newElement("RegevDec");
#endif
    EVector xvec;
    powerVector(xvec, x, ptxt.length()); // the vector xvec=(1,x,x^2,...)

    // Record the linear constraints
    //            <sk,ctMat*xvec> +<ptxt,g*xvec> +<noise,xvec> = <ctVec,xvec>

    EVector yvec = ctMat * xvec;

#ifdef DEBUGGING
    // Start by checking that indeed this constraint holds
    auto xvec2 = xvec * vd.gk->g();
    assert(xvec.length()==ptxt.length());
    Element sum = innerProduct((*pd.sk1), yvec) + innerProduct(noise, xvec) + innerProduct(ptxt, xvec2);
    assert(sum==innerProduct(ctVec, xvec));

    // verify the constraints
    DLPROOFS::PtxtVec pVec;
    // The plaintext variables
    int idx = vd.pt1Idx;
    for (int i=0; i<pd.pt1->length(); i++) {
        conv(pVec[idx++], (*pd.pt1)[i]);
    }
    // The secret key variables
    idx = vd.sk1Idx;
    for (int i=0; i<pd.sk1->length(); i++) {
        for (int j=0; j<scalarsPerElement(); j++)
            conv(pVec[idx++], coeff((*pd.sk1)[i], j));
    }
    // The noise variables
    idx = vd.decErrIdx;
    for (int i=0; i<pd.decErr->length(); i++) {
        for (int j=0; j<scalarsPerElement(); j++)
            conv(pVec[idx++], coeff((*pd.decErr)[i], j));
    }
    // The noise padding
    idx = vd.decErrPadIdx;
    for (int i=0; i<pd.decErrPadding.length(); i++) {
        for (int j=0; j<scalarsPerElement(); j++)
            conv(pVec[idx++], coeff(pd.decErrPadding[i], j));
    }
    clear(sum);
#endif

    // Prepare the linear constraints

    // The element <ctVec,cvec>
    setEqsTo(&(vd.linConstr[0]), innerProduct(ctVec, xvec));

    // expand <sk,ctMat*xvec> 
    expandConstraints(&(vd.linConstr[0]), vd.sk1Idx, yvec);
#ifdef DEBUGGING
    sum += innerProduct((*pd.sk1), yvec);
    setEqsTo(&(vd.linConstr[0]), sum);
    for (int i=0; i<scalarsPerElement(); i++) {
        auto& linConstr = vd.linConstr[i];
        if (!checkConstraintLoose(linConstr, pVec)) {
            std::cout << "  constraints for <sk,yvec> #"<<i<<" failed\n  ";
            prettyPrint(std::cout, linConstr) << std::endl;
            std::cout << "  sk(idx="<<vd.sk1Idx<<")="<<pretty(*pd.sk1)<<std::endl;
            std::cout << "  yvec="<<pretty(yvec)<<std::endl;
            exit(0);
        }
    }
#endif

    // Expand <noise,xvec>
    expandConstraints(&(vd.linConstr[0]), vd.decErrIdx, xvec);
#ifdef DEBUGGING
    sum += innerProduct(noise,xvec);
    setEqsTo(&(vd.linConstr[0]), sum);
    for (int i=0; i<scalarsPerElement(); i++) {
        auto& linConstr = vd.linConstr[i];
        if (!checkConstraintLoose(linConstr, pVec)) {
            std::cout << "  constraints for <noise,xvec> #"<<i<<" failed\n  ";
            prettyPrint(std::cout, linConstr) << std::endl;
            std::cout << "  noise(idx="<<vd.decErrIdx<<")="<<pretty(noise)<<std::endl;
            std::cout << "  xvec="<<pretty(xvec)<<std::endl;
            exit(0);
        }
    }
#endif

    // Constraints for <ptxt,g*xvec>, where ptxt is a Z_p vector, not GF(p^e)
    xvec *= vd.gk->g(); // g*xvec
    makeConstraints(&(vd.linConstr[0]), vd.pt1Idx, xvec);
#ifdef DEBUGGING
    sum += innerProduct(ptxt, xvec2);
    setEqsTo(&(vd.linConstr[0]), sum);
    for (int i=0; i<scalarsPerElement(); i++) {
        auto& linConstr = vd.linConstr[i];
        if (!checkConstraintLoose(linConstr, pVec)) {
            std::cout << "constraints for <ptxt,g*xvec> #"<<i<<" failed\n  ";
            prettyPrint(std::cout, linConstr) << std::endl;
            std::cout << "  ptxt(idx="<<vd.pt1Idx<<")="<<pretty(ptxt)<<std::endl;
            std::cout << "  xvec*g="<<pretty(xvec2)<<std::endl;
            exit(0);
        }
    }
#endif

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

    // A challenge scalar x, defines the vector xvec=(1,x,x^2,...)
//#ifdef DEBUGGING
//    Element x;
//    NTL::ZZ_pX px;
//    NTL::SetCoeff(px,0); // p(x)=1;
//    conv(x,px);
//#else
    Element x = vd.mer->newElement("RegevEncScalar1");
//#endif
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
    // The randomness variables
    int idx = vd.rIdx;
    for (int i=0; i<pd.r->length(); i++) {
        for (int j=0; j<scalarsPerElement(); j++)
            conv(pVec[idx++], coeff((*pd.r)[i], j));
    }
    // The noise variables
    idx = vd.encErrIdx;
    for (int i=0; i<pd.encErr.length(); i++) {
        for (int j=0; j<scalarsPerElement(); j++)
            conv(pVec[idx++], coeff(pd.encErr[i], j));
    }
    // The plaintext variables
    idx = vd.pt2Idx;
    for (int i=0; i<pd.pt2->length(); i++) {
        conv(pVec[idx++], (*pd.pt2)[i]);
    }
    // The randomness padding
    idx = vd.rPadIdx;
    for (int i=0; i<pd.rPadding.length(); i++) {
        for (int j=0; j<scalarsPerElement(); j++)
            conv(pVec[idx++], coeff(pd.rPadding[i], j));
    }
    // The noise padding
    idx = vd.encErrPadIdx;
    for (int i=0; i<pd.encErrPadding.length(); i++) {
        for (int j=0; j<scalarsPerElement(); j++)
            conv(pVec[idx++], coeff(pd.encErrPadding[i], j));
    }

    for (int i=0; i<scalarsPerElement(); i++) { // check the linear constraints
        auto& linConstr = vd.encLinCnstr[i];
        if (!checkConstraintLoose(linConstr, pVec)) {
            std::cout << "constraints for encryption #"<<i<<" failed\n  ";
            prettyPrint(std::cout, linConstr) << std::endl;
            //std::cout << "  ptxt(idx="<<vd.pt1Idx<<")="<<pretty(ptxt)<<std::endl;
            //std::cout << "  xvec*g="<<pretty(xvec2)<<std::endl;
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

} // end of namespace REGEVENC