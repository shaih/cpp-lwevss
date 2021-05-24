/* curve25519.cpp - a thin layer around libsodium low-level interfaces
 * 
 * Copyright (C) 2021, LWE-PVSS
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject
 * to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included
 * in all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
 * OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR
 * OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
 * ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 **/
#include <algorithm> // define std::min
#include <stdexcept>

#include <NTL/ZZ.h>
#include "scalar25519.hpp"
#include "point25519.hpp"

namespace CRV25519 {

size_t Point::counter = 0;
size_t Point::timer = 0;
Point Point::basePoint;
Point Point::identityPoint = Point::init(); // forcing a run of the init function

Point Point::init() {
    static bool firstTime = true; // ensure that init only happens once
    // FIXME: not thread safe
    if (!firstTime) // return a dummy point
        return Point();
    firstTime = false;

    int ret = sodium_init();
    if (ret != 0) {
        throw std::runtime_error("libsodium failed to initialize, #errno="+std::to_string(ret));
    }

    // initialize the point base
    Scalar one = Scalar().setInteger(1);
    ret = crypto_scalarmult_ed25519_base_noclamp(basePoint.bytes, one.bytes);
    if (ret != 0) {
        throw std::runtime_error("failed to initialize basePoint, #errno="+std::to_string(ret));
    }
    
    // The modulus of the main group: 2^{252} + 27742317777372353535851937790883648493
    // NTL::ZZ_p::init((NTL::to_ZZ(1L)<<252) + NTL::conv<NTL::ZZ>("27742317777372353535851937790883648493"));

    return basePoint - basePoint; // this will be assigned to the global identityPoint
}

// A helper function, naive implementation
Scalar innerProduct(const Scalar* a, const Scalar* b, size_t n) {
    Scalar ret;
    for (size_t i=0; i<n; i++) {
        ret += a[i] * b[i];
    }
    return ret;
}

// Computes *this modulo |other|. Both arguments are interpreted as
// signed integers in the range [-P/2,P/2), the result is set in the
// range [-|other|/2, |other|/2), then mapped to Z_P.
Scalar& Scalar::operator%=(const Scalar& other) {
    static NTL::ZZ P = (NTL::to_ZZ(1L)<<252) + NTL::conv<NTL::ZZ>("27742317777372353535851937790883648493");
    NTL::ZZ x = NTL::ZZFromBytes(bytes, crypto_core_ed25519_SCALARBYTES);
    NTL::ZZ y = NTL::ZZFromBytes(other.bytes, crypto_core_ed25519_SCALARBYTES);
    if (x >= P/2) x -= P; // map to the range [-P/2, P/2)
    if (y >= P/2) {
        y = abs(y-P); // map to the range [-P/2, P/2), then take absolute value
    }
    x %= y;        // in [0,y-1]
    if (x > y/2) {
        x = P+x-y; // map to [-y/2,y/2), then map to an element in Z_P
    }
    BytesFromZZ(bytes, x, crypto_core_ed25519_SCALARBYTES);
    return *this;
}


} /* end of namespace CRV25519 */
