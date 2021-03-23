#include <iostream>
#include <memory>
#include "point25519.hpp"
#include "scalar25519.hpp"
#include "tests.hpp" // define strings LWEVSS_TESTS::passed and LWEVSS_TESTS::failed

using namespace CRV25519;
bool test_Point() {
    auto& basePoint = Point::base();
    auto& identityPoint = Point::identity();

    if (!basePoint.isValid())
        return false;
    /** Note: identityPoint.isValid() returns flase, since this is the zero element
        if (!identityPoint.isValid())
            return false;
    */
    Point p;
    if (p != Point::identity())
        return false;

    auto twoBase = basePoint + basePoint;
    auto two = Scalar().setInteger(2);

    if (twoBase != basePoint*two || twoBase != two*basePoint)
        return false;

    auto r = randomPoint();
    if (r-r != identityPoint) //Point myIdentity;
        return false;

    unsigned char buf[10] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
    auto r2 = hashToCurve(buf, sizeof buf);
    if (!r2.isValid())
        return false;

    auto s = randomScalar();
    auto r3 = basePoint * s;
    auto r4 = baseTimesScalar(s);
    if (!r3.isValid() || !r4.isValid() || r3 != r4)
        return false;

    // check r4 * s = base * s^2
    auto r5 = r4 * s;
    auto r6 = basePoint * (s*s);
    if (!r5.isValid() || !r6.isValid() || r5 != r6)
        return false;

    return true;
}

int main(int, char**) {
    if (!test_Point())
        std::cout << LWEVSS_TESTS::failed << std::endl;
    else
        std::cout << LWEVSS_TESTS::passed << std::endl;        
}
