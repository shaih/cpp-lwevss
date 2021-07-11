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
#include <chrono>
#include "constraints.hpp"
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

inline void conv(CRV25519::Scalar& to, const ALGEBRA::BigInt& from) {
    ALGEBRA::bigIntBytes(to.bytes, from, sizeof(to.bytes));
}
inline void conv(CRV25519::Scalar& to, const ALGEBRA::Scalar& from) {
    ALGEBRA::scalarBytes(to.bytes, from, sizeof(to.bytes));
}
inline void conv(ALGEBRA::Scalar& to, const CRV25519::Scalar& from) {
    ALGEBRA::scalarFromBytes(to, from.bytes, sizeof(from.bytes));
}

inline ALGEBRA::BigInt balanced(const CRV25519::Scalar& s) {
    ALGEBRA::Scalar as;
    ALGEBRA::conv(as,s);
    return ALGEBRA::balanced(as);
}

inline std::ostream& prettyPrint(std::ostream& st, const DLPROOFS::PtxtVec& v) {
    st << "[";
    for (auto& x : v) {
        st << x.first << "->" << balanced(x.second) << ", ";
    }
    return (st << "]");
}
inline std::ostream& prettyPrint(std::ostream& st, const DLPROOFS::LinConstraint& c) {
    prettyPrint(st<<"{", c.terms) << ", " << balanced(c.equalsTo) << "}";
    return st;
}
inline std::ostream& prettyPrint(std::ostream& st, const DLPROOFS::QuadConstraint& c) {
    st<<"{[";
    for (auto i : c.indexes) { st << i<< " "; }
    st << "], " << balanced(c.equalsTo) << "}";
    return st;
}

inline void addEVec2Map(DLPROOFS::PtxtVec& mymap, const EVector& v, size_t offset=0) {
    std::pair<size_t, CRV25519::Scalar> tmp;
    tmp.first = offset + v.length()*scalarsPerElement() -1;
    auto it = mymap.end();
    for (long i=v.length()-1; i>=0; --i)
        for (long j=scalarsPerElement()-1; j>=0; --j) {
            it = mymap.insert(it, tmp);
            conv(it->second, coeff(v[i],j));
            tmp.first--;
        }
}
inline void addSVec2Map(DLPROOFS::PtxtVec& mymap, const SVector& v, size_t offset=0) {
    std::pair<size_t, CRV25519::Scalar> tmp;
    tmp.first = offset +v.length() -1;
    auto it = mymap.end();
    for (long i=v.length()-1; i>=0; --i) {
        it = mymap.insert(it, tmp);
        conv(it->second, v[i]);
        tmp.first--;
    }
}

inline void addRange2Set(std::set<size_t>& myset, size_t from, size_t len) {
    auto range = interval(from, from+len);
    myset.insert(range.begin(), range.end());
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