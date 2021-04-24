#include <iostream>
#include <cassert>
#include <NTL/ZZ.h>
#include <NTL/mat_ZZ.h>

#include "tests.hpp" // define strings LWEVSS_TESTS::passed and LWEVSS_TESTS::failed
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

/*
// Expand a constraint a*x with a in GF(p^e) to e constrints over scalars,
// namely store in e constraints in e variables the e-by-e matrix representing
// the multiply-by-a matrix over the mase field.
// The variables in the constraints are idx,idx+1,... I.e., the constraints
// are idx -> a.freeTerm, idx+1 -> a.coeffOf(X), idx+2 -> a.coeffOf(X^2),...
// These functions assume that GF(p^e) is represented modulo X^e +1.
void expandConstraints(LinConstraint* constrs, int idx,const ALGEBRA::Element& a);
void expandConstraints(LinConstraint* constrs, int idx,
                       const ALGEBRA::EVector& v, int from=0, int to=-1);

// This function is for the case where the secret variables are from Z_p,
// namely we have the constraint <x,v>=b over GF(p^e), but x iv over Z_p.
void makeConstraints(LinConstraint* constrs, int idx,
                     const ALGEBRA::EVector& v, int from=0, int to=-1);
*/
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
        REGEVENC::conv(cPtr[j].equalsTo, coeff(b,j));
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
        REGEVENC::conv(cPtr[j].equalsTo, coeff(b,j));
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
        REGEVENC::conv(cPtr[j].equalsTo, coeff(b,j));
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
    GlobalKey gpk("testContext", /*k*/3, /*m*/2, /*n*/5);
    MerlinRegev mer;
    PedersenContext ped;
    VerifierData vd(gpk, ped, mer);
    ProverData pd(vd);

    // Generate/verify the proofs by the second party (idx=1)
    int partyIdx = 1;

    // Key generation for the five parties
    std::vector<ALGEBRA::EVector> kgNoise(gpk.enn);
    std::vector<ALGEBRA::EVector> sk(gpk.enn);
    std::vector<ALGEBRA::EVector> pk(gpk.enn);
    for (int i=0; i<gpk.enn; i++) {
        std::tie(sk[i],pk[i]) = gpk.genKeys(&kgNoise[i]);
        gpk.addPK(pk[i]);
    }
    gpk.setKeyHash();

    // encryption
    std::vector<ALGEBRA::SVector> ptxt1(gpk.enn);
    std::vector<GlobalKey::CtxtPair> ctxt(gpk.enn);
    std::vector<ALGEBRA::EVector> encRnd(gpk.enn);
    std::vector<ALGEBRA::EVector> encNoise(gpk.enn);
    for (int i=0; i<gpk.enn; i++) {
        resize(ptxt1[i],gpk.enn);
        for (auto& p: ptxt1[i]) conv(p,i); //randomizeScalar(p);
        ctxt[i] = gpk.encrypt(ptxt1[i], encRnd[i], encNoise[i]);
    }

    // decryption at party #1
    ALGEBRA::SVector ptxt2;    resize(ptxt2, gpk.tee);
    ALGEBRA::EVector decNoise; resize(decNoise, gpk.tee);
    for (int i=0; i<gpk.tee; i++) { // decrypt 2nd entry in i'th ctxt
        ptxt2[i] = gpk.decrypt(sk[partyIdx], partyIdx, ctxt[i], &(decNoise[i]));
        if (ptxt2[i] != ptxt1[i][partyIdx])
            return false;
    }

    // Copy the first t ciphertexts into a k x t matrix and another t-vector
    EMatrix ctxtMat;
    resize(ctxtMat, gpk.kay, gpk.tee);
    EVector ctxtVec;
    resize(ctxtVec, gpk.tee);

    for (int i=0; i<gpk.tee; i++) {
        for (int j=0; j<gpk.kay; j++)
            ctxtMat[j][i] = ctxt[i].first[j];
        ctxtVec[i] = ctxt[i].second[partyIdx];
    }

    // prepare for proof, pad the secret key to exact norm and commit to it
    int origSize = sk[partyIdx].length(); 
    pad2exactNorm(sk[partyIdx], pd.sk1Padding, vd.B_sk);
    pd.sk1 = &(sk[partyIdx]);

    // Commit separately to the original key and the padding, each one wrt
    // both the G's and the Hs
    vd.sk1Com[0] = commit(sk[partyIdx], vd.sk1Idx, vd.Gs, pd.sk1Rnd[0]);
    vd.sk1Com[1] = commit(sk[partyIdx], vd.sk1Idx, vd.Hs, pd.sk1Rnd[1]);
    vd.sk1PadCom[0] = commit(sk[partyIdx], vd.sk1PadIdx, vd.Gs, pd.sk1PadRnd[0], origSize);
    vd.sk1PadCom[1] = commit(sk[partyIdx], vd.sk1PadIdx, vd.Hs, pd.sk1PadRnd[1], origSize);

    proveDecryption(pd, ptxt2, decNoise, ctxtMat, ctxtVec);
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
