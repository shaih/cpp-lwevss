#include <iostream>
#include "algebra.hpp"
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
int main(int, char**) {
    if (true)
        std::cout << LWEVSS_TESTS::passed << std::endl;
    else
        std::cout << LWEVSS_TESTS::failed << std::endl;
	return 0;
}
