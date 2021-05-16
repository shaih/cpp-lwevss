#ifndef _POINT_25519_HPP_
#define _POINT_25519_HPP_
/* point25519.hpp - a thin layer around libsodium low-level interfaces
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
#include <cstring>
#include <stdexcept>
extern "C" {
    #include <sodium.h>
}
#include "scalar25519.hpp"

namespace CRV25519 {

// A class that holds a point on the curve
class Point {
    static Point init(); // Initialize libsodium and the constants
    static Point identityPoint, basePoint;
public:
    static size_t counter; // used for profiling and performance measurements
    unsigned char bytes[crypto_core_ed25519_BYTES];

    Point(){ *this = identityPoint; }

    const unsigned char* dataBytes() const { return bytes; }

    // isValid returns true if a point is on the ed25519 curve, non-zero,
    // on the main subgroup, and of small order
    bool isValid() const {
        return crypto_core_ed25519_is_valid_point(bytes) == 1;
    }

    // returns true if two points are equal
    bool operator==(const Point& other) const {
        return sodium_memcmp(bytes, other.bytes, crypto_core_ed25519_BYTES) == 0;
    }
    bool operator!=(const Point& other) const { return !(*this == other); }

    Point& randomize() {
        crypto_core_ed25519_random(bytes);
        return *this;
    }

    // Compute the sum of two elliptic curve points, exception on failure
    Point& operator+=(const Point& other) {
        if (other==identity())
            return *this;
        if (*this == identity())
            *this = other;
        else {
            auto res = crypto_core_ed25519_add(bytes, bytes, other.bytes);
            if (res != 0) {
                throw std::runtime_error("failed to perform point addition, err#="+std::to_string(res));
            }
        }
        return *this;
    }
    Point operator+(const Point& other) const { return Point(*this).operator+=(other); }

    // Compute the difference of two elliptic curve points, exception on failure
    Point& operator-=(const Point& other) {
        if (other==identity())
            return *this;
        auto res = crypto_core_ed25519_sub(bytes, bytes, other.bytes);
        if (res != 0) {
            throw std::runtime_error("failed to perform point subtraction, err#="+std::to_string(res));
        }
        return *this;
    }
    Point operator-(const Point& other) const { return Point(*this).operator-=(other); }

    // Computes the product of a scalar with a point
    Point& operator*=(const Scalar& n) {
        if (*this==identity() || n.isZero())
            *this = identity();
        else {
            auto res = crypto_scalarmult_ed25519_noclamp(bytes, n.bytes, bytes);
            if (res != 0) {
                throw std::runtime_error("failed to perform scalar multiplication, err#="+std::to_string(res));
            }
            counter++; // count exponentiations
        }
        return *this;
    }
    Point operator*(const Scalar& s) const { return Point(*this).operator*=(s); }

    static const Point& identity() { return identityPoint; }
    static const Point& base() { return basePoint; }
};

// randomPoint is a factory method, returning a random group element
inline Point randomPoint() { return Point().randomize(); }

// I/O
inline std::ostream& operator<<(std::ostream& os, const Point& p) {
  os.write((const char*)p.dataBytes(), crypto_core_ed25519_BYTES);
  return os;
}
inline std::istream& operator>>(std::istream& is, Point& p) {
  is.read((char*)p.bytes, crypto_core_ed25519_BYTES);
  return is;
}

inline Point operator*(const Scalar& n, const Point& p) { return p*n; }

// Initialize a point to G*n from a scalar n, a factory method
inline Point baseTimesScalar(const Scalar& n) {
    Point pp;
    auto res = crypto_scalarmult_ed25519_base_noclamp(pp.bytes, n.bytes);
    if (res != 0) {
        throw std::runtime_error("failed to perform scalar multiplication by base, err#="+std::to_string(res));
    }
    return pp;
}

// Hash arbitrary byte array to the curve
inline Point hashToCurve(unsigned char* bytes, int len,
                         unsigned char* key=nullptr, int keylen=0) {
    unsigned char h[crypto_core_ed25519_UNIFORMBYTES];
    crypto_generichash(h, sizeof h, bytes, len, key, keylen);
    Point pp;
    crypto_core_ed25519_from_uniform(pp.bytes, h);
    return pp;
}
} /* end of namespace CRV25519 */
#endif // ifndef _POINT_25519_HPP_
