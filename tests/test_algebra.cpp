#include <iostream>
#include "utils.hpp"
#include "algebra.hpp"
#include "regevEnc.hpp"
#include "utils.hpp"
#include "tests.hpp" // define strings LWEVSS_TESTS::passed and LWEVSS_TESTS::failed

using namespace ALGEBRA;

/********** TODO: Things to test: ***************
size_t log2roundUp(const BigInt& n);
BigInt toBigInt(long n);
BigInt scalar2bigInt(const Scalar& s);
void scalarBytes(unsigned char *buf, const Scalar& s, size_t bufSize);
void elementBytes(unsigned char *buf, const Element& e, size_t bufSize);
void scalarFromBytes(Scalar& s, const unsigned char *buf, size_t bufSize);
void elementFromBytes(Element& e, const unsigned char *buf, size_t bufSize);

Scalar innerProduct(const SVector& v1, const SVector& v2);
Element innerProduct(const EVector& v1, const EVector& v2);

template<class VecType, class ElemType>
VecType& push_back(VecType &v, const ElemType& s);

void conv(Element& e, const SVector& v);
void conv(SVector& v, const Element& e);
 ************************************************************************/

void chooseEvector(EVector& v) {
    resize(v, 6);
    SVector tmp;
    resize(tmp, REGEVENC::GlobalKey::ell);
    conv(tmp[0], BigInt(1000));
    conv(tmp[1], BigInt(-50));
    for (int i=0; i<v.length(); i++) {
        conv(v[i], tmp);
        tmp[0] = tmp[1] - tmp[0];
        tmp[1] *= -2;
    }
}

bool test_break2digits()
{
    EVector v, hi, lo;
    chooseEvector(v);
    breakTwoDigits(hi, lo, v, BigInt(1000));
    for (int i=0; i<v.length(); i++) {
        auto repLo = balanced(lo[i]);
        for (int j=0; j<scalarsPerElement(); j++) {
            if (NTL::abs(repLo[j])>500) return false;
            if (coeff(lo[i],j) + 1000*coeff(hi[i],j) != coeff(v[i],j))
                return false;
        }
    }
    return true;
}

bool test_vec2map() {
    EVector vE;
    SVector vS;
    chooseEvector(vE);
    resize(vS, vE.length());
    for (int i=0; i<vS.length(); i++)
        conv(vS[i], i);
    
    DLPROOFS::PtxtVec pv;
    addEVec2Map(pv, vE, /*offset=*/2);
    addSVec2Map(pv, vS);
//    std::cout << "vE="<<balanced(vE)<<std::endl;
//    std::cout << "vS="<<balanced(vS)<<std::endl;
//    prettyPrint(std::cout << "pv=", pv)<<std::endl;
    int expected[] = {0, 1, 2, 3, 4, 5, 1150, -200, -1350, 400, 1750, -800, -2550, 1600};
    for (auto it = pv.begin(); it != pv.end(); it++) {
        int n = expected[it->first];
        if (it->second != CRV25519::Scalar().setInteger(n))
            return false;
    }
    return true;
}

int main(int, char**) {
    BigInt p = REGEVENC::GlobalKey::P(); // just to ensure that init functions are called
    if (test_break2digits() && test_vec2map())
        std::cout << LWEVSS_TESTS::passed << std::endl;
    else
        std::cout << LWEVSS_TESTS::failed << std::endl;
	return 0;
}
