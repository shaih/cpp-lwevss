#ifndef _UTILS_HPP_
#define _UTILS_HPP_
/* utils.hpp - Utility functions (only sum-of-four squares for now)
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
#include <iostream>
#include <set>
#include "algebra.hpp"

namespace ALGEBRA {
typedef std::array<BigInt, 2> TwoSqrts;
typedef std::array<BigInt, 4> FourSqrts;

// Decomposes a prime, p=1 mod 4, to a sum of two squares
TwoSqrts decomposeProbablePrime(BigInt p);

// Decomposes a nonegative integer into a sum of four squares
FourSqrts decompose4(BigInt n);

inline int ceilDiv(int a, int b) { return (a+b-1)/b;}

// Compute the norm of v as a bigInt (no modular reduction)
BigInt normSquaredBI(BIVector& vv);
BigInt normSquaredBigInt(const SVector& v);
BigInt normSquaredBigInt(const EVector& v);
BigInt normSquaredBigInt(const Element* v, size_t len);
BigInt lInftyNorm(const EVector& v);

inline std::set<int> interval(int from, int to) {
    std::set<int> intSet;
    for (int i=from; i<to; i++) intSet.insert(intSet.end(), i);
    return intSet;
}
} // end of namespace ALGEBRA

inline std::ostream& operator<<(std::ostream& st, const std::set<int>& intSet){
    st << '{';
    for (auto i: intSet) st << i << ' ';
    return st << '}';
}
inline std::ostream& operator<<(std::ostream& st, const std::set<size_t>& intSet){
    st << '{';
    for (auto i: intSet) st << i << ' ';
    return st << '}';
}
#endif // ifndef _UTILS_HPP_