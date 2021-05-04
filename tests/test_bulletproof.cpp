#include <iostream>
#include "tests.hpp" // define strings LWEVSS_TESTS::passed and LWEVSS_TESTS::failed
#include "bulletproof.hpp"

using namespace DLPROOFS;

bool test_linear() {
    for (size_t sz : {1,2,8,13}) { // different sizes
        // build a constraint: sum_i ai*bi = b = \sum_bi^2
        LinConstraint cnstrL;
        for (size_t i=0; i<sz; i++) {
            CRV25519::Scalar& x = cnstrL.terms[i+1].setInteger(i+1);
            cnstrL.equalsTo += x * x;
        }
        PtxtVec& xes = cnstrL.terms;
        LinPfTranscript pfL = proveLinear("blah", cnstrL, xes);
        if (!verifyLinear(cnstrL, pfL))
            return false;
    }
    // Test lower level with an offset
    LinConstraint cnstrL;
    PtxtVec witness;
    for (size_t i=0; i<5; i++) {
        CRV25519::Scalar& a = cnstrL.terms[i+1] = CRV25519::randomScalar();
        CRV25519::Scalar& w = witness[i+1] = CRV25519::randomScalar();
        cnstrL.equalsTo += a * w;
    }
    std::string tag("blah2");
    LinPfTranscript proof(tag);
    PedersenContext ped(tag);
    MerlinBPctx mer(tag);    // Make a Merlin state that includes the statement
    mer.processConstraint("constraint", cnstrL);

    FlatLinStmt st(ped, cnstrL, witness); // "Faltten" the statement and witness

    CRV25519::Scalar r = CRV25519::randomScalar();
    proof.C = commit(st.generators.data(), st.witness.data(), st.generators.size(), r);

    size_t n = st.generators.size();
    Scalar* const as = st.witness.data();   // these are the xes
    Scalar* const bs = st.statement.data(); // these are the constraints
    Point* const gs = st.generators.data(); // these are the generators

    // offset the witness
    Scalar offset[n];
    for (size_t i=0; i<n; i++) {
        offset[i].randomize();
        as[i] -= offset[i];
    }
    st.equalsTo -= innerProduct(offset, bs, n);

    MerlinBPctx mer2 = mer;  //backup for verification
    FlatLinStmt st2 = st; st2.witness.clear(); // a copy without the witness

    proveLinear(proof, r, mer, as, bs, gs, n);    // The actual proof
    if (!verifyLinear(proof, st2, mer2, offset))  // The actual verification
            return false;

    return true;
}

bool test_quadratic() {
    for (size_t sz : {1,2,8,13}) {
        PtxtVec xes, ys;
        QuadConstraint cnstrQ;
        for (size_t i=0; i<sz; i++) {
            CRV25519::Scalar& x = xes[i] = CRV25519::Scalar().setInteger(i+1);
            CRV25519::Scalar& y = ys[i] = CRV25519::Scalar().setInteger(i+2);
            cnstrQ.indexes.insert(cnstrQ.indexes.end(), i);
            cnstrQ.equalsTo += x * y;
        }
        QuadPfTranscript pfQ = proveQuadratic("blah", cnstrQ, xes, ys);
        if (!verifyQuadratic(cnstrQ, pfQ))
            return false;
    }
    // test lower level with an offset
    PtxtVec xs, ys;
    QuadConstraint cnstrQ;
    for (size_t i=0; i<5; i++) {
        CRV25519::Scalar& x = xs[i] = CRV25519::randomScalar();
        CRV25519::Scalar& y = ys[i] = CRV25519::randomScalar();
        cnstrQ.indexes.insert(cnstrQ.indexes.end(), i);
        cnstrQ.equalsTo += x * y;
    }
    std::string tag("blah2");
    QuadPfTranscript pf(tag);
    PedersenContext ped(tag);
    MerlinBPctx mer(tag);  // Make a Merlin state that includes the statement
    mer.processConstraint("constraint", cnstrQ);
    FlatQuadStmt st(ped, cnstrQ, xs, ys); // "Faltten" statement and witnesses

    size_t n = st.gs.size();
    Scalar* const as = st.wG.data(); // the a witnesses
    Scalar* const bs = st.wH.data(); // the b witnesses
    Point* const gs = st.gs.data();  // the G generators
    Point* const hs = st.hs.data();  // the H generators

    // Compute and push {"C": commitment to the xes}
    Scalar r = CRV25519::randomScalar();
    pf.C = DLPROOFS::commit2(gs, as, hs, bs, n, r); // commitment to the x'es and y's

    Scalar offsetG[n], offsetH[n];
    for (size_t i=0; i<n; i++) {
        offsetG[i].randomize();
        offsetH[i].randomize();
        as[i] -= offsetG[i];
        bs[i] -= offsetH[i];
    }
    st.equalsTo = innerProduct(as,bs,n);

    MerlinBPctx mer2 = mer; //backup for verification
    FlatQuadStmt st2 = st;  // a copy without the witness
    st2.wG.clear(); st2.wH.clear();

    proveQuadratic(pf, r, mer, gs, as, hs, bs, n);     // The actual proof
    if (!verifyQuadratic(pf,st2,mer2,offsetG,offsetH)) // The actual verification
        return false;

    return true;
}

bool test_norm() {
    for (size_t sz : {1,2,8,13}) {
        PtxtVec xes;
        std::set<size_t> indexes;
        for (size_t i=0; i<sz; i++) {
            CRV25519::Scalar& x = xes[i] = CRV25519::Scalar().setInteger(i+1);
            indexes.insert(indexes.end(), i);
        }
        QuadPfTranscript pfNS("blah");
        MerlinBPctx mer(pfNS.tag);
        Scalar normSq = proveNormSquared(pfNS, mer, xes);
        if (!verifyNormSquared(indexes,normSq,pfNS))
            return false;
    }
    return true;
}

int main(int, char**) {
    if (test_linear() && test_quadratic() && test_norm())
        std::cout << LWEVSS_TESTS::passed << std::endl;   
    else
        std::cout << LWEVSS_TESTS::failed << std::endl;
    return 0;         
}
