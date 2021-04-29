#include <iostream>
#include "shamir.hpp"
#include "tests.hpp" // define strings LWEVSS_TESTS::passed and LWEVSS_TESTS::failed

using namespace TOOLS;
using namespace ALGEBRA;

// test computeKernel() - computing the parity-check matrix H
bool testKernel() {
    EvalSet es;
    for (int i=1; i<6; i++) es.insert(i);
    SharingParams params(es, 2);

    // a random degree-1 polynomial
    Scalar p0, p1;
    randomizeScalar(p0); randomizeScalar(p1);
    SPoly p;
    SetCoeff(p, 0, p1);
    SetCoeff(p, 0, p0);

    // evaluate at 0,1,...,5
    SVector shares;
    resize(shares, 6);
    for (int i=0; i<6; i++) {
        Scalar s;
        conv(s, i);
        shares[i] = eval(p, s);
    }

    // check that H * shares = 0
    SVector zero;
    resize(zero, params.H.NumRows());
    return (params.H * shares == zero);
}

bool testSharing() {
    // 2-of-5 sharing
    EvalSet es{1,2,3,4,5};
    SharingParams params(es, 2);

    // share a random scalar
    SVector shares;
    params.randomSharing(shares);

    // reconstruct the secret from shares 2,4
    EvalSet recSet{2,4};
    SVector sh2; resize(sh2, 2);
    sh2[0] = shares[2];
    sh2[1] = shares[4];
    return params.getSecret(sh2, recSet) == shares[0];
}

/*********************** TODO: Things to test: *********************
SharingParams(const EvalSet& ev, int t); 
void newSharing(SVector& v, const Scalar& s) const;
SVector lagrangeCoeffs(const EvalSet& recSet) const;
Scalar getSecret(const SVector& sharing, const EvalSet& recSet);
 *******************************************************************/

int main(int, char**) {
    NTL::ZZ_p::init(NTL::to_ZZ(17));
    if (testKernel() && testSharing())
        std::cout << LWEVSS_TESTS::passed << std::endl;
    else
        std::cout << LWEVSS_TESTS::failed << std::endl;
	return 0;
}
