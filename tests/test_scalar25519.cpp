#include <iostream>
#include <memory>
#include "scalar25519.hpp"
#include "tests.hpp" // define strings LWEVSS_TESTS::passed and LWEVSS_TESTS::failed

using namespace CRV25519;

static bool testMod() {
    auto x = Scalar().setInteger(100);
    auto y = Scalar().setInteger(7);
    x %= y; // should be 2
    if (x != Scalar().setInteger(2)) {
        std::cout << "  100 % 7 should be = 2\n";
        return false;
    }
    
    x.setInteger(40);
    x %= y;
    if (x != Scalar().setInteger(-2)) {
        std::cout << "  40 % 7 should be = -2\n";
        return false;
    }
    
    x.setInteger(-100);
    x %= y;
    if (x != Scalar().setInteger(-2)) {
        std::cout << "  -100 % 7 should be = -2\n";
        return false;
    }
    
    x.setInteger(100);
    y.setInteger(-7);
    x %= y;
    if (x != Scalar().setInteger(2)) {
        std::cout << "  100 % -7 should be = 2\n";
        return false;
    }
    
    x.setInteger(-100);
    x %= y;
    if (x != Scalar().setInteger(-2)) {
        std::cout << "  -100 % -7 should be = -2\n";
        return false;
    }
    return true;
}

static bool test_Scalar() {
    Scalar zero = Scalar();
    Scalar one = Scalar().setInteger(1);
    Scalar two = one + one;
    if (two.bytes[0] != 2)
        return false;
    for (int i=1; i<crypto_core_ed25519_SCALARBYTES; i++) {
        if (two.bytes[i] != 0)
            return false;
    }
    auto myInt = Scalar().setInteger(0x123456789abcdef0);
    if (myInt.bytes[0]!=0xf0 || myInt.bytes[1]!=0xde || myInt.bytes[2]!=0xbc || myInt.bytes[3]!=0x9a
        || myInt.bytes[4]!=0x78 || myInt.bytes[5]!=0x56 || myInt.bytes[6]!=0x34 || myInt.bytes[7]!=0x12)
        return false;

    // subtracts a random value from itself
    auto r1 = randomScalar();
    if (r1 + r1 != r1 * two)
        return false;
    if (r1 + negationOf(r1) != zero)
        return false;
    if (r1 * inverseOf(r1) != one)
        return false;
    if (r1 / r1 != one)
        return false;
    if (one / r1 != inverseOf(r1))
        return false;

    return testMod();
}

int main(int, char**) {
    if (!test_Scalar())
        std::cout << LWEVSS_TESTS::failed << std::endl;
    else
        std::cout << LWEVSS_TESTS::passed << std::endl;        
}
