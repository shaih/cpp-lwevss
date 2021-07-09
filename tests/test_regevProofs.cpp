#include <iostream>
#include <cassert>
#include <numeric>
#include <NTL/ZZ.h>
#include <NTL/mat_ZZ.h>

#define DEBUGGING

#include "tests.hpp" // define strings LWEVSS_TESTS::passed and LWEVSS_TESTS::failed
#include "utils.hpp"
#include "pedersen.hpp"
#include "regevProofs.hpp"

using namespace std;
using namespace ALGEBRA;
using namespace REGEVENC;

bool test_commit() {
    // Initialize a list of 5*ell generators
    PedersenContext ped("blah");
    std::vector<Point> gens(scalarsPerElement()*5);
    for (int i=0; i<gens.size(); i++)
        gens[i] = ped.getG(i);

    SVector svec;
    resize(svec,4);
    for (int i=0; i<4; i++) conv(svec[i], 2); // vector is (2,2,2,2)
    CRV25519::Scalar r;                  // to hold randomness
    auto com = commit(svec, 5, gens, r); // commitment wrt generators 5,6,7,8

    // com should be r*base + 2(g[5]+g[6]+g[7]+g[8])
    Point b = gens[5] +gens[6] +gens[7] +gens[8];
    if (com != Point::base()*r + b+b)
        return false;

    EVector evec;
    resize(evec, 3);
    for (int i=0; i<evec.length(); i++)
        randomizeElement(evec[i]);

    // A vector of CRV25519::Scalar's with the representation of evec
    std::vector<CRV25519::Scalar> evecRep(evec.length()*scalarsPerElement());
    int idx = 0;
    for (int i=0; i<evec.length(); i++) for (int j=0; j<scalarsPerElement(); j++)
        conv(evecRep[idx++], coeff(evec[i], j));
    
    // commitment for the representation of evec[1,2,...]
    // wrt generators 3,4,5,...,3*ell-1
    com = commit(evec, 3, gens, r, /*startIdx=*/1);

    return com == DLPROOFS::commit(&gens[3], &evecRep[scalarsPerElement()],
                                    evecRep.size()-scalarsPerElement(), r);
}

bool test_norms() {
    int iVec[] = {1, 2, -1, 0, 3, 2, -2, 0}; // norm^2 = 23
    BIVector biVec;
    resize(biVec, 8);
    for (int i=0; i<biVec.length(); i++)
        conv(biVec[i], iVec[i]);
    
    if (normSquaredBI(biVec) != toBigInt(23))
        return false;
    
    SVector sVec;
    conv(sVec, biVec);
    if (normSquaredBigInt(sVec) != toBigInt(23))
        return false;
    
    EVector eVec;
    resize(eVec, 2);
    int val = -4;
    int norm2 = 0;
    SVector tmp;
    resize(tmp, scalarsPerElement());
    for (auto& x: eVec) { // initialize one element in the vector
        for (int j=0; j<scalarsPerElement(); j++) {
            norm2 += val*val;
            conv(tmp[j], val++);
        }
        ALGEBRA::conv(x, tmp);
    }
    if (normSquaredBigInt(eVec) != toBigInt(norm2))
        return false;
    
    // Add to v four integers a,b,c,d such that the result
    // (v | a,b,c,d) has norm exactly equal to the bound

    BigInt bound = toBigInt(20);
    SVector sPad; resize(sPad, PAD_SIZE);
    pad2exactNorm(sVec, sPad, bound);
    if (normSquaredBigInt(sVec)+normSquaredBigInt(sPad) != bound*bound) {
        return false;
    }
    
    EVector ePad; resize(ePad, PAD_SIZE/scalarsPerElement());
    pad2exactNorm(eVec, ePad, bound);
    if (normSquaredBigInt(eVec)+normSquaredBigInt(ePad) != bound*bound) {
        return false;
    }
    return true;
}

bool test_constraints() {
    // choose secret variables, one vector over Z_p and one over GF(p^e)
    SVector sVec; resize(sVec,3);
    for (int i=0; i<sVec.length(); i++) randomizeScalar(sVec[i]);

    EVector eVec; resize(eVec,3);
    for (int i=0; i<eVec.length(); i++) randomizeElement(eVec[i]);

    // Choose a few random public coefficients
    EVector coeffs; resize(coeffs, 5);
    for (int i=0; i<coeffs.length(); i++) randomizeElement(coeffs[i]);

    // generate some constraints from the above and check them
    std::vector<LinConstraint> constr(3*scalarsPerElement());

    // first set of constraints: coeffs[0]*eVec[0]
    LinConstraint *cPtr = constr.data();
    DLPROOFS::PtxtVec w1;
    for (int j=0; j<scalarsPerElement(); j++)
        conv(w1[sVec.length() +j], coeff(eVec[0],j));
    expandConstraints(cPtr, sVec.length(), coeffs[0]);

    Element b = coeffs[0]*eVec[0];
    for (int j=0; j<scalarsPerElement(); j++) {
        ALGEBRA::conv(cPtr[j].equalsTo, coeff(b,j));
        if (!checkConstraint(cPtr[j], w1))
            return false;
    }

    // second set of constraints: \sum_{i=0}^2 coeffs[i+1]*eVec[i]
    cPtr += scalarsPerElement();
    DLPROOFS::PtxtVec w2;
    for (int i=0; i<eVec.length(); i++)
        for (int j=0; j<scalarsPerElement(); j++)
            conv(w2[sVec.length()+i*scalarsPerElement()+j], coeff(eVec[i],j));
    expandConstraints(cPtr, sVec.length(), coeffs, 1, 4);
    b = eVec[0]*coeffs[1] + eVec[1]*coeffs[2] + eVec[2]*coeffs[3];
    for (int j=0; j<scalarsPerElement(); j++) {
        ALGEBRA::conv(cPtr[j].equalsTo, coeff(b,j));
        if (!checkConstraint(cPtr[j], w2))
            return false;
    }

    // third set of constraints: \sum_{i=0}^2 coeffs[i+2]*sVec[i]
    cPtr += scalarsPerElement();
    DLPROOFS::PtxtVec w3;
    for (int i=0; i<sVec.length(); i++)
        conv(w3[i], sVec[i]);
    makeConstraints(cPtr, 0, coeffs, 2, 5);
    b = sVec[0]*coeffs[2] + sVec[1]*coeffs[3] + sVec[2]*coeffs[4];
    for (int j=0; j<scalarsPerElement(); j++) {
        ALGEBRA::conv(cPtr[j].equalsTo, coeff(b,j));
        if (!checkConstraint(cPtr[j], w3))
            return false;
    }

    // Make a single vector with all the secret scalars, as CRV25519::Scalas
    int idx = 0;
    DLPROOFS::PtxtVec w; // map i -> a_i
    for (int i=0; i<sVec.length(); i++) {
        CRV25519::Scalar& s = w[idx++]; // insert index idx to w
        conv(s, sVec[i]);         // convert to CRV25519::Scalar
    }
    for (int i=0; i<eVec.length(); i++) 
        for (int j=0; j<scalarsPerElement(); j++) {
            CRV25519::Scalar& s = w[idx++];   // insert index idx to w
            conv(s, coeff(eVec[i], j)); // convert to CRV25519::Scalar
        }

    // merge the constraints from above and check again
    std::vector<CRV25519::Scalar> rnd(constr.size());
    for (auto& s: rnd) s.randomize();
    LinConstraint c;
    c.merge(constr, rnd);
    if (!checkConstraint(c, w))
        return false;

    return true;
}


bool test_proofs() {
    // The dimensions of the the CRX is k-by-m, but note that this is
    // a matrix over GF(p^2) so the lattice dimensions we get it twice
    // that
    //KeyParams kp;
    //kp.k=64; kp.m=64; kp.n=64;
    //kp.sigmaKG=10; kp.sigmaEnc1=10; kp.sigmaEnc2=20;
    KeyParams kp(128);
#ifdef DEBUGGING
    std::cout << "n="<<kp.n<<", k="<<kp.k<<"->128\n";
    //<<", sigma1="<<kp.sigmaEnc1<<"->3, "
    //<< "sigma2="<<kp.sigmaEnc2<<"->13\n";
    //kp.sigmaEnc1 = 13;
    //kp.sigmaEnc1 = 23;
    kp.k=128;// make smaller dimension for debugging
#endif

    GlobalKey gpk("testContext", kp);
    TernaryEMatrix::init();
    MerlinRegev mer;
    PedersenContext ped;
    SharingParams ssp(interval(1,gpk.enn+1), gpk.tee);
    VerifierData vd(gpk, ped, mer, ssp);
    ProverData pd(vd);

    // Generate/verify the proofs by the second party (idx=1)
    int partyIdx = 1;

    // Key generation for all the parties
    std::vector<ALGEBRA::EVector> kgNoise(gpk.enn);
    std::vector<ALGEBRA::EVector> sk(gpk.enn);
    std::vector<ALGEBRA::EVector> pk(gpk.enn);
    for (int i=0; i<gpk.enn; i++) {
        std::tie(sk[i],pk[i]) = gpk.genKeys(&kgNoise[i]);
        gpk.addPK(pk[i]);
    }
    gpk.setKeyHash();
#ifdef DEBUGGING
    std::cout <<"|kgNoise|^2=2^"<<log2BI(normSquaredBigInt(kgNoise[partyIdx]))<<std::endl;
#endif

    // encryption
    std::vector<ALGEBRA::SVector> ptxt1(gpk.enn);
    std::vector<GlobalKey::CtxtPair> ctxt1(gpk.enn);
    // secret sharing of a random value , the secret itself is sshr[0]
    ALGEBRA::SVector sshr;
    ssp.randomSharing(sshr);
    for (int i=0; i<gpk.enn; i++) {
        resize(ptxt1[i], gpk.enn);
        for (int j=0; j<gpk.enn; j++) ptxt1[i][j] = sshr[i+1];
        ctxt1[i] = gpk.encrypt(ptxt1[i]);
    }

    // decryption at party #1
    ALGEBRA::SVector ptxt2;    resize(ptxt2, gpk.tee);
    ALGEBRA::EVector decNoise; resize(decNoise, gpk.tee);
    for (int i=0; i<gpk.tee; i++) { // decrypt 2nd entry in i'th ctxt
        ptxt2[i] = gpk.decrypt(sk[partyIdx], partyIdx, ctxt1[i], &(decNoise[i]));
        if (ptxt2[i] != ptxt1[i][partyIdx])
            return false;
    }
#ifdef DEBUGGING
    std::cout <<"|decNoise|^2=2^"<<log2BI(normSquaredBigInt(decNoise))
        << ", B_decNoise=2^"<<log2BI(vd.B_dNoise) <<std::endl;
#endif

    // re-encryption at party #1
    ALGEBRA::SVector ptxt3;
    resize(ptxt3, gpk.enn);
    for (int j=0; j<gpk.enn; j++) ptxt3[j] = sshr[j+1];
    ALGEBRA::EVector encRnd;
    REGEVENC::GlobalKey::CtxtPair eNoise;
    auto ctxt2 = gpk.encrypt(ptxt3, encRnd, eNoise);
#ifdef DEBUGGING
    std::cout <<"|encNoise1|^2=2^"<<log2BI(normSquaredBigInt(eNoise.first))
    <<", |encNoise2|^2=2^"<<log2BI(normSquaredBigInt(eNoise.second))
    <<std::endl;
#endif

    // Copy the first t ciphertexts into a k x t matrix and another t-vector
    EMatrix ctxtMat;
    resize(ctxtMat, gpk.kay, gpk.tee);
    EVector ctxtVec;
    resize(ctxtVec, gpk.tee);
    for (int i=0; i<gpk.tee; i++) {
        for (int j=0; j<gpk.kay; j++)
            ctxtMat[j][i] = ctxt1[i].first[j];
        ctxtVec[i] = ctxt1[i].second[partyIdx];
    }

    // prepare for proof, pad the secret key to exact norm and commit to it
    int origSize = sk[partyIdx].length(); 
    //pd.sk1 = &(sk[partyIdx]);

    // Commit to the original key wrt the G's
    vd.sk1Com = commit(sk[partyIdx], vd.sk1Idx, vd.Gs, pd.sk1Rnd);

    proveDecryption(pd, ctxtMat, ctxtVec, ptxt2, sk[partyIdx], decNoise);
    proveEncryption(pd, ctxt2.first, ctxt2.second, ptxt3, encRnd, eNoise.first, eNoise.second);
    proveKeyGen(pd, partyIdx, sk[partyIdx], kgNoise[partyIdx]);

    SVector lagrange = vd.sp->lagrangeCoeffs(interval(1,gpk.tee+1));
    proveReShare(pd, lagrange, ptxt2, ptxt3);
    proveSmallness(pd);

    // Verify the commitments and constraints

    for (auto& lncstr: vd.linConstr) {
        if (!checkConstraintLoose(lncstr, pd.linWitness))
            return false;
    }
    for (auto& qdcstr: vd.normConstr) {
        if (!checkConstraintLoose(qdcstr, pd.quadWitnessG, pd.quadWitnessG))
            return false;
    }

    if (!checkQuadCommit(vd.normConstr[vd.dHiQuadIdx], vd.dCompHiCom,
        vd.dPadHiCom,  pd.dCompHiRnd, pd.dPadHiRnd,  pd.quadWitnessG, vd.ped))
        return false;
    if (!checkQuadCommit(vd.normConstr[vd.dLoQuadIdx], vd.dCompLoCom,
        vd.dPadLoCom,  pd.dCompLoRnd, pd.dPadLoRnd,  pd.quadWitnessG, vd.ped))
        return false;
    if (!checkQuadCommit(vd.normConstr[vd.rQuadIdx],   vd.rCompCom,
        vd.rPadCom,    pd.rCompRnd,   pd.rPadRnd,    pd.quadWitnessG, vd.ped))
        return false;
    if (!checkQuadCommit(vd.normConstr[vd.e1HiQuadIdx],vd.eComp1HiCom,
        vd.ePad1HiCom, pd.eComp1HiRnd,pd.ePad1HiRnd, pd.quadWitnessG, vd.ped))
        return false;
    if (!checkQuadCommit(vd.normConstr[vd.e1LoQuadIdx],vd.eComp1LoCom,
        vd.ePad1LoCom, pd.eComp1LoRnd,pd.ePad1LoRnd, pd.quadWitnessG, vd.ped))
        return false;
    if (!checkQuadCommit(vd.normConstr[vd.e2HiQuadIdx],vd.eComp2HiCom,
        vd.ePad2HiCom, pd.eComp2HiRnd,pd.ePad2HiRnd, pd.quadWitnessG, vd.ped))
        return false;
    if (!checkQuadCommit(vd.normConstr[vd.e2LoQuadIdx],vd.eComp2LoCom,
        vd.ePad2LoCom, pd.eComp2LoRnd,pd.ePad2LoRnd, pd.quadWitnessG, vd.ped))
        return false;
    if (!checkQuadCommit(vd.normConstr[vd.sk2QuadIdx], vd.sk2CompCom,
        vd.sk2PadCom,  pd.sk2CompRnd, pd.sk2PadRnd,  pd.quadWitnessG, vd.ped))
        return false;
    if (!checkQuadCommit(vd.normConstr[vd.kHiQuadIdx],   vd.kCompHiCom,
        vd.kPadHiCom,    pd.kCompHiRnd,   pd.kPadHiRnd,    pd.quadWitnessG, vd.ped))
        return false;
    if (!checkQuadCommit(vd.normConstr[vd.kLoQuadIdx],   vd.kCompLoCom,
        vd.kPadLoCom,    pd.kCompLoRnd,   pd.kPadLoRnd,    pd.quadWitnessG, vd.ped))
        return false;


    // commitments for re-sharing linear constraint
    if (!checkLinCommit(vd.linConstr[vd.reShrLinIdx].terms,
        vd.pt1Com +vd.pt2Com, pd.pt1Rnd +pd.pt2Rnd,
        pd.linWitness, vd.ped))
        { return false; }

    // aggregate the constraints and flatten everything before proving
    ReadyToProve rtp;
    rtp.aggregateProver(pd);

    // Make copies of the Merlin transcripts and specialize them
    // for the final constraints before proving/verifying them
    auto merLin = *vd.mer;
    merLin.processConstraint("linear", rtp.linCnstr);

    auto merQuad = *vd.mer;
    merQuad.processConstraint("quadratic", rtp.quadCnstr);

    // Flatten the statements, this relases the memory of the constraints
    // (hence the Merlin processing above must be done before doing this).
    rtp.flattenLinPrv(pd);
    rtp.flattenQuadPrv(pd);

    ReadyToVerify rtv = rtp; // a copy without the secret variables

    // prove and verify the linear statement
    auto merLinVer = merLin; // another copy for verification
    DLPROOFS::LinPfTranscript pfL("Linear");
    pfL.C = rtp.linCom;

    // The actual proof
    DLPROOFS::proveLinear(pfL, rtp.lComRnd, merLin, rtp.linWtns.data(),
            rtp.linStmnt.data(), rtp.linGs.data(), rtp.linGs.size());
    // The actual verification
    if (!DLPROOFS::verifyLinear(pfL, rtv.linStmnt.data(), rtv.linGs.data(),
                      rtv.linGs.size(), rtv.linCnstr.equalsTo, merLinVer))
        return false;

    // prove and verify the quadratic statement
    auto merQuadVer = merQuad; // another copy for verification
    DLPROOFS::QuadPfTranscript pfQ("Quadratic");
    pfQ.C = rtp.quadCom;
     // The actual proof
    DLPROOFS::proveQuadratic(pfQ, rtp.qComRnd, merQuad, rtp.quadGs.data(),
                rtp.quadWtnsG.data(), rtp.quadHs.data(), rtp.quadWtnsH.data(),
                rtp.quadGs.size());
    // The actual verification
    if (!DLPROOFS::verifyQuadratic(pfQ, rtv.quadGs.data(), rtv.quadHs.data(),
                        rtp.quadGs.size(), rtv.quadCnstr.equalsTo, merQuadVer,
                        rtv.offstG.data(), rtv.offstH.data()))
        return false;

    return true;
}

int main(int, char**) {
    assert(scalarsPerElement()==REGEVENC::GlobalKey::ell); // ensuring the init function was called
    if (!test_commit() || !test_norms() || !test_constraints() || !test_proofs())
        std::cout << LWEVSS_TESTS::failed << std::endl;
    else
        std::cout << LWEVSS_TESTS::passed << std::endl;
    return 0;
}
