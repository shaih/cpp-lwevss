#ifndef _ALGEBRA_HPP_
#define _ALGEBRA_HPP_
/* algebra.hpp - an NTL-compatibility thin layer
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
#include <NTL/ZZ.h>
#include <NTL/mat_ZZ_pE.h>

/* This header provides copmatibility with NTL, inside the ALGEBRA namespace.
 * Modules that use it should use the names that it provides rather than
 * directly use NTL. Specifically it provides the following names:
 * - BigInt  -> NTL:ZZ
 * - Scalar  -> NTL::ZZ_p
 * - Element -> NTL::ZZ_pE (element in GF(p^e))
 * - BIVector-> NTL::vec_ZZ
 * - SVector -> NTL::vec_ZZ_p
 * - EVector -> NTL::vec_ZZ_pE
 * - SMatrix -> NTL::mat_ZZ_p
 * - EMatrix -> NTL::mat_ZZ_pE
 *
 * The users can assume a function conv(x,y) that converts between these
 * types as apropriate. Everything else is provided explicitly in this header.
 */
namespace ALGEBRA {
// in liue of "using X as Y", bring the relevant NTL types to this namespace
typedef NTL::ZZ BigInt;
typedef NTL::ZZ_p Scalar;
typedef NTL::ZZ_pE Element;
typedef NTL::vec_ZZ BIVector;
typedef NTL::vec_ZZ_p SVector;
typedef NTL::mat_ZZ_p SMatrix;
typedef NTL::vec_ZZ_pE EVector;
typedef NTL::mat_ZZ_pE EMatrix;

inline const Scalar& zeroScalar() { return NTL::ZZ_p::zero(); }
inline Scalar& randomizeScalar(Scalar& s) { NTL::random(s); return s; }
inline Element& randomizeElement(Element& e) { NTL::random(e); return e; }
inline long randBitsize(size_t n) {return NTL::RandomBits_long(n);}
inline BigInt& randBitsize(BigInt& bi, size_t n) {
    NTL::RandomBits(bi, n);
    return bi;
}
inline size_t randomBit() {return randBitsize(1);}

inline BIVector& resize(BIVector& vec, size_t n) {vec.SetLength(n); return vec;}
inline SVector& resize(SVector& vec, size_t n) {vec.SetLength(n); return vec;}
inline EVector& resize(EVector& vec, size_t n) {vec.SetLength(n); return vec;}
inline SMatrix& resize(SMatrix& mat, size_t n, size_t m) {
    mat.SetDims(n,m); return mat;
}
inline EMatrix& resize(EMatrix& mat, size_t n, size_t m) {
    mat.SetDims(n,m); return mat;
}

// returns the smallest ell such that 2^{ell} >= n
inline size_t log2roundUp(const BigInt& n) {
    if (NTL::IsZero(n)) return 0;
    return NTL::NumBits(n-1);
}

// some conversions
inline BigInt toBigInt(long n) {return NTL::conv<NTL::ZZ>(n);}
inline BigInt scalar2bigInt(const Scalar& s) {return NTL::conv<NTL::ZZ>(s);}
inline void scalarBytes(unsigned char *buf, const Scalar& s, size_t bufSize){
    NTL::BytesFromZZ(buf, NTL::rep(s), bufSize);
}
inline void elementBytes(unsigned char *buf, const Element& e, size_t bufSize){
    const SVector& v = NTL::rep(e).rep; // the underlying representation as vec_ZZ_p
    size_t len = 32;
    for (size_t i=0; i<v.length() && bufSize>0; i++) {
        if (len > bufSize)
            len = bufSize;
        NTL::BytesFromZZ(buf, NTL::rep(v[i]), len); // gen the next few bytes
        bufSize -= len;
        buf += len;
    }
}

inline void scalarFromBytes(Scalar& s, const unsigned char *buf, size_t bufSize){
    NTL::ZZ n;
    NTL::ZZFromBytes(n, buf, bufSize);
    NTL::conv(s,n);
}
inline void elementFromBytes(Element& e, const unsigned char *buf, size_t bufSize){
    NTL::ZZ_pX& px = (NTL::ZZ_pX&)NTL::rep(e).rep; // underlying representation as ZZ_pX
    // dirty: discards const-ness
    size_t len = 32;
    for (size_t i=0; i<NTL::ZZ_pE::degree() && bufSize>0; i++) {
        if (len > bufSize)
            len = bufSize;
        NTL::ZZ n;
        NTL::ZZFromBytes(n, buf, bufSize);
        NTL::conv(px.rep[i], n);
        bufSize -= len;
        buf += len;
    }
    px.normalize();
}

// Other utilities
inline Scalar innerProduct(const SVector& v1, const SVector& v2) {
    Scalar s;
    NTL::InnerProduct(s,v1,v2);
    return s;
}
inline Element innerProduct(const EVector& v1, const EVector& v2) {
    Element e;
    NTL::InnerProduct(e,v1,v2);
    return e;
}

template<class VecType, class ElemType>
VecType& push_back(VecType &v, const ElemType& s) {
    v.append(s);
    return v;
}

// convert between an element and a vector of scalars
inline void conv(Element& e, const SVector& v) {
    NTL::ZZ_pX& px = (NTL::ZZ_pX&) rep(e); // dirty: discards const-ness
    size_t n = std::min(NTL::ZZ_pE::degree(), v.length());
    for (size_t i=0; i<n; i++) {
        NTL::SetCoeff(px, i, v[i]);
    }
}
inline void conv(SVector& v, const Element& e) {
    resize(v, NTL::ZZ_pE::degree());
    for (size_t i=0; i<v.length(); i++) {
        v[i] = NTL::coeff(rep(e), i);
    }
}

typedef NTL::RandomStreamPush PRGbackupClass; // backup/restore of PRG state
inline void initRandomness(const std::string& st) {
    NTL::SetSeed((unsigned char*)st.data(), st.length());
}

// Debugging helpers
inline std::ostream& printScalar(std::ostream& st, const Scalar& sc) {
    BigInt szz;
    conv(szz,sc);
    if (szz > NTL::ZZ_p::modulus()/2)
        st <<  (szz - NTL::ZZ_p::modulus());
    else
        st << szz;
    return st;
}
inline std::ostream& printSvec(std::ostream& st, const SVector& sv) {
    st << "[";
    for (size_t i=0; i<sv.length()-1; i++)
        printScalar(st, sv[i]) << " ";
    return (printScalar(st, sv[sv.length()-1]) << "]");
}
inline std::ostream& printElement(std::ostream& st, const Element& el) {
    const NTL::ZZ_pX& ex = rep(el);
    size_t ell = NTL::ZZ_pE::degree();
    st << "[";
    for (size_t i=0; i<ell-1; i++)
        printScalar(st, NTL::coeff(ex, i)) << " ";
    return (printScalar(st, NTL::coeff(ex, ell-1)) << "]");
}
inline std::ostream& printEvec(std::ostream& st, const EVector& ev) {
    st << "[";
    for (size_t i=0; i<ev.length()-1; i++)
        printElement(st, ev[i]) << " ";
    return (printElement(st, ev[ev.length()-1]) << "]");
}


} // end of namespace ALGEBRA
#endif // ifndef _ALGEBRA_HPP_
