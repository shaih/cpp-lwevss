#include <iostream>
#include "tests.hpp" // define strings LWEVSS_TESTS::passed and LWEVSS_TESTS::failed
#include "bulletproof.hpp"

using namespace DLPROOFS;

bool test_linear() {
    for (size_t sz : {1,2,8,13}) {
        // build a constraint: sum_i ai*bi = b = \sum_bi^2
        DLPROOFS::LinConstraint cnstrL;
        for (size_t i=0; i<sz; i++) {
            CRV25519::Scalar& x = cnstrL.terms[i+1].setInteger(i+1);
            cnstrL.equalsTo += x * x;
        }
        DLPROOFS::PtxtVec& xes = cnstrL.terms;
        DLPROOFS::LinPfTranscript pfL = proveLinear("blah", cnstrL, xes);
        if (!verifyLinear(cnstrL, pfL))
            return false;
    }
    return true;
}

bool test_quadratic() {
    for (size_t sz : {1,2,8,13}) {
        DLPROOFS::PtxtVec xes, ys;
        DLPROOFS::QuadConstraint cnstrQ;
        for (size_t i=0; i<sz; i++) {
            CRV25519::Scalar& x = xes[i] = CRV25519::Scalar().setInteger(i+1);
            CRV25519::Scalar& y = ys[i] = CRV25519::Scalar().setInteger(i+2);
            cnstrQ.indexes.insert(cnstrQ.indexes.end(), i);
            cnstrQ.equalsTo += x * y;
        }
        DLPROOFS::QuadPfTranscript pfQ = proveQuadratic("blah", cnstrQ, xes, ys);
        if (!verifyQuadratic(cnstrQ, pfQ))
            return false;
    }
    return true;
}

bool test_norm() {
    for (size_t sz : {1,2,8,13}) {
        DLPROOFS::PtxtVec xes;
        std::set<size_t> indexes;
        for (size_t i=0; i<sz; i++) {
            CRV25519::Scalar& x = xes[i] = CRV25519::Scalar().setInteger(i+1);
            indexes.insert(indexes.end(), i);
        }
        QuadPfTranscript pfNS("blah");
        MerlinBPctx mer(pfNS.tag);
        Scalar normSq = DLPROOFS::proveNormSquared(pfNS, mer, xes);
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
