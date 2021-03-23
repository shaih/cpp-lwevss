#ifndef _SCALAR_25519_HPP_
#define _SCALAR_25519_HPP_
/* scalar25519.hpp - a thin layer around libsodium low-level interfaces
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
#include <memory>
#include <vector>
#include <cstring>
#include <stdexcept>
#include <iostream>
extern "C" {
    #include <sodium.h>
}

namespace CRV25519 {
// Default randomize object, different implementation will derive
// from it and override the default operator() method
class RandomScalar {
public:
    virtual void operator()(unsigned char* data) const {
        crypto_core_ed25519_scalar_random(data); 
    }
};

// A class that holds a scalar (modulo P = 2^{252}+ZZZ)
class Scalar {
public:
    unsigned char bytes[crypto_core_ed25519_SCALARBYTES];

    Scalar() { std::memset(bytes, 0, crypto_core_ed25519_SCALARBYTES); }
 
    const unsigned char* dataBytes() const { return bytes; }

    // returns true if two scalars are equal
    bool operator==(const Scalar& other) const {
        return sodium_memcmp(bytes, other.bytes, 32) == 0;
    }
    bool operator!=(const Scalar& other) const { return !(*this == other); }
    bool isZero() const { return Scalar()==*this; }

    // select a random scalar in the range [0, P), P is group order
    Scalar& randomize(const RandomScalar& r=RandomScalar()) {
        r(bytes);
        return *this;
    }

    // Computes the multiplicative inverse of a scalar mod P, where P
    // is the order of the main subgroup
    Scalar& invert() {
    	auto res = crypto_core_ed25519_scalar_invert(bytes, bytes);
        if (res != 0) {
            throw std::runtime_error("failed to perform scalar inversion, err#="+std::to_string(res));
        }
        return *this;
    }

    // Computes the additive inverse of a scalar mod P, where P
    // is the order of the main subgroup
    Scalar& negate() {
    	crypto_core_ed25519_scalar_negate(bytes, bytes);
        return *this;
    }

    // Add two scalars mod P
    Scalar& operator+=(const Scalar& other) {
        crypto_core_ed25519_scalar_add(bytes, bytes, other.bytes);
        return *this;
    }
    Scalar operator+(const Scalar& other) const {
        return Scalar(*this).operator+=(other);
    }

    // Subtract two scalars mod P
    Scalar& operator-=(const Scalar& other) {
        crypto_core_ed25519_scalar_sub(bytes, bytes, other.bytes);
        return *this;
    }
    Scalar operator-(const Scalar& other) const {
        return Scalar(*this).operator-=(other);
    }

    // Computes the product of two scalars mod P
    Scalar& operator*=(const Scalar& other) {
        crypto_core_ed25519_scalar_mul(bytes, bytes, other.bytes);
        return *this;
    }
    Scalar operator*(const Scalar& other) const {
        return Scalar(*this).operator*=(other);
    }

    // Computes *this modulo |other|. Both arguments are interpreted
    // as signed integers in the range [-P/2,P/2), the result is set
    // in the range [-|other|/2, |other|/2), then mapped to Z_P.
    // FIXME (SH): We really should not have this method, it is a hack to
    // avoid having to implement stuff myself, but it does not belong here
    Scalar& operator%=(const Scalar& other);

    // Convert a signed integer to a scalar (useful for tests and debugging)
    Scalar& setInteger(long n) {
        std::memset(bytes, 0, crypto_core_ed25519_SCALARBYTES); // reset to zero
        bool negated = (n < 0);
        if (negated) { // make it positive
            n = -n;
        }
        for (int i=0; i < sizeof(long); i++) {
            bytes[i] = (unsigned char)(n & 0xff);
            n >>= 8;
        }
        if (negated) {
            negate();
        }
        return *this;
    }
};

// A factory method, returning a random scalar in the
// range [0, P), where P is the order of the main subgroup
inline Scalar randomScalar(const RandomScalar& r=RandomScalar()) {
    return Scalar().randomize(r);
}

// I/O
inline std::ostream& operator<<(std::ostream& os, const Scalar& s) {
  os.write((const char*)s.dataBytes(), crypto_core_ed25519_SCALARBYTES);
  return os;
}
inline std::istream& operator>>(std::istream& is, Scalar& s) {
  is.read((char*)s.bytes, crypto_core_ed25519_SCALARBYTES);
  return is;
}

inline Scalar inverseOf(const Scalar& a) { return Scalar(a).invert(); }
inline Scalar negationOf(const Scalar& a) {return Scalar(a).negate(); }

// A helper function, currently a naive implementation
Scalar innerProduct(const Scalar* a, const Scalar* b, size_t n);

/****** A few usefule randomizing objects **********/

// Select a -1/0/1 scalar with Pr[0]=1/2 and Pr[+-1]=1/4. Note that there are
// faster ways of choosing many such scalars then repeated calls to this object.
// This implementation is NOT constant time.
class ZeroOneScalar: public RandomScalar {
public:
    void operator()(unsigned char* data) const override {
        unsigned int r = randombytes_random();
        // A random 32-bit word, we only use two bits of it
        if (r & 1 != 0) {
            data[0] = 1;
            if (r & 2 != 0)
                crypto_core_ed25519_scalar_negate(data, data);
        }
    }
};

// Select a scalar in the range [+-(2^n -1)], n<=251, almost uniformly
// except the probability of zero is twice as large (namely 2^{-n}).
// This implementation is constant time (maybe).
class BoundedSizeScalar: public RandomScalar {
public:
    int nBytes;
    unsigned char mask;

    BoundedSizeScalar() = delete;
    explicit BoundedSizeScalar(int n) {
        if (n<1 || n>251) {
            throw std::runtime_error("illeagal bitsize for BoundedSizeScalar: "+std::to_string(n));
        }
        // How many bytes to fit a number in [0, 2^n -1]
        nBytes = (7+n)/8; // = ceiling(n/8)

        // A mask to turn off excess bits at the top byte (if any)
        mask = ((unsigned char)0xff) >> ((8-n)&0x7);
    }

    void operator()(unsigned char* data) const override {
        unsigned char bufs[2][crypto_core_ed25519_SCALARBYTES];
        std::memset(bufs, 0, sizeof bufs);
        randombytes_buf(bufs[0], nBytes); // fill 1st buffer with random bytes
        bufs[0][nBytes -1] &= mask;       // zero out excess bits at the top
        crypto_core_ed25519_scalar_negate(bufs[1], bufs[0]); // negate 2nd buf

        // Copy one of the two buffers
        int bit = randombytes_random() & 1;
        std::memcpy(data, bufs[bit], crypto_core_ed25519_SCALARBYTES);
    }
};
} /* end of namespace CRV25519 */
#endif // ifndef _SCALAR_25519_HPP_
