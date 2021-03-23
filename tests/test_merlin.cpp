#include <iostream>
#include "merlin.hpp"
#include "tests.hpp" // define strings LWEVSS_TESTS::passed and LWEVSS_TESTS::failed

using CRV25519::Scalar, CRV25519::Point, Merlin::MerlinBPctx;

static bool test() {
    Scalar r1 = CRV25519::randomScalar();
    Scalar one = Scalar().setInteger(1);
    Scalar ten = Scalar().setInteger(10);
    Point rp = CRV25519::randomPoint();

    DLPROOFS::LinConstraint cnstr;
    cnstr.addTerm(1, one);
    cnstr.addTerm(4, ten);
    cnstr.addTerm(9, r1+one);
    cnstr.equalsTo.setInteger(100);

    // generate twice, test that you get the same challenges,
    // but different blinding factors
    Scalar x1;
    Point p1;
    std::pair<Scalar,Scalar> sPair;
    {
        MerlinBPctx mer("blah");
        mer.processScalar("one", one);
        mer.processPoint("rp", rp);
        p1 = mer.newGenerator("p1");
        mer.processPoint("p1", p1);
        mer.processConstraint("cnstr", cnstr);
        sPair = mer.newBlindingFactors("pair", 1, &x1);
        x1 = mer.newChallenge("x1");
    }
    {
        MerlinBPctx mer("blah");
        mer.processScalar("one", one);
        mer.processPoint("rp", rp);
        if (mer.newGenerator("p1") != p1)
            return false;
        mer.processPoint("p1", p1);
        mer.processConstraint("cnstr", cnstr);
        if (mer.newBlindingFactors("pair", 1, &x1) == sPair)
            return false;
        if (mer.newChallenge("x1") != x1)
            return false;
    }
    return true;
}
int main(int, char**) {
    if (!test())
        std::cout << LWEVSS_TESTS::failed << std::endl;
    else
        std::cout << LWEVSS_TESTS::passed << std::endl;        
}
