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
#include <NTL/mat_ZZ.h>
#include <NTL/mat_ZZ_pE.h>
#include <NTL/RR.h>

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
typedef NTL::ZZ_pX SPoly;
typedef NTL::ZZ_pE Element;
typedef NTL::vec_ZZ BIVector;
typedef NTL::vec_ZZ_p SVector;
typedef NTL::mat_ZZ_p SMatrix;
typedef NTL::vec_ZZ_pE EVector;
typedef NTL::mat_ZZ_pE EMatrix;

inline int bytesPerScalar() { return (NumBits(NTL::ZZ_p::modulus())+7)/8; }
inline int scalarsPerElement() { return NTL::ZZ_pE::degree(); }

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

inline BigInt square(const BigInt& x) {return NTL::sqr(x);}
inline BigInt sqrt(const BigInt& x) {return NTL::SqrRoot(x);}

// returns the smallest ell such that 2^{ell} >= n
inline size_t log2roundUp(const BigInt& n) {
    if (NTL::IsZero(n)) return 0;
    return NTL::NumBits(n-1);
}

// some conversions
inline BigInt toBigInt(long n) {
    NTL::ZZ num(NTL::INIT_SIZE,4);
    conv(num, n);
    return num;
}
inline BigInt scalar2bigInt(const Scalar& s) {return NTL::conv<NTL::ZZ>(s);}
inline const Scalar& coeff(const Element& e, size_t idx) {
    return NTL::coeff(NTL::rep(e), idx);
}

inline void bigIntBytes(unsigned char *buf, const BigInt& bi, size_t bufSize){
    NTL::BytesFromZZ(buf, bi, bufSize);
}
inline void scalarBytes(unsigned char *buf, const Scalar& s, size_t bufSize){
    bigIntBytes(buf, NTL::rep(s), bufSize);
}
inline void elementBytes(unsigned char *buf, const Element& e, size_t bufSize){
    const SVector& v = NTL::rep(e).rep; // the underlying representation as vec_ZZ_p
    size_t len = bytesPerScalar(); // =32
    for (size_t i=0; i<v.length() && bufSize>0; i++) {
        if (len > bufSize)
            len = bufSize;
        NTL::BytesFromZZ(buf, NTL::rep(v[i]), len); // gen the next few bytes
        bufSize -= len;
        buf += len;
    }
    if (bufSize > 0) // zero-out the rest of the buffer
        memset(buf, 0, bufSize);
}

inline void scalarFromBytes(Scalar& s, const unsigned char *buf, size_t bufSize){
    NTL::ZZ n(NTL::INIT_SIZE,4);
    NTL::ZZFromBytes(n, buf, bufSize);
    NTL::conv(s,n);
}
inline void elementFromBytes(Element& e, const unsigned char *buf, size_t bufSize){
    NTL::ZZ_pX px;
    size_t len = bytesPerScalar();
    for (size_t i=0; i<scalarsPerElement() && bufSize>0; i++) {
        if (len > bufSize)
            len = bufSize;
        NTL::ZZ n(NTL::INIT_SIZE,4);
        NTL::ZZFromBytes(n, buf, len);
        SetCoeff(px, i, NTL::conv<NTL::ZZ_p>(n));
        bufSize -= len;
        buf += len;
    }
    conv(e,px);
}

// Other utilities
inline Scalar innerProduct(const SVector& v1, const SVector& v2) {
    Scalar s;
    NTL::InnerProduct(s,v1,v2);
    return s;
}
inline Element innerProduct(const EVector& v1, const SVector& v2) {
    Element e;
    int len = std::min(v1.length(), v2.length());
    for (int i=0; i<len; i++)
        e += v1[i]*v2[i];
    return e;
}
inline Element innerProduct(const SVector& v1, const EVector& v2) {
    return innerProduct(v2,v1);
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
    size_t n = std::min(scalarsPerElement(), (int)v.length());
    for (size_t i=0; i<n; i++) {
        NTL::SetCoeff(px, i, v[i]);
    }
}
inline void conv(SVector& v, const Element& e) {
    resize(v, scalarsPerElement());
    for (size_t i=0; i<v.length(); i++) {
        v[i] = NTL::coeff(rep(e), i);
    }
}
inline void conv(BIVector& to, const EVector& from) {
    resize(to, scalarsPerElement() *from.length());
    int idx = 0;
    for (int i=0; i<from.length(); i++) for (int j=0; j<scalarsPerElement(); j++) {
        conv(to[idx++], ALGEBRA::coeff(from[i], j));
    }
}

// Implemet a version of BigInt-by-double multiplication
inline BigInt multDbl(double x, const BigInt& y) {
    NTL::RR ry = NTL::to_RR(y);
    ry *= x;
    return NTL::to_ZZ(ry);
}
inline BigInt multDbl(const BigInt& y, double x) {
    return multDbl(x,y);
}
inline double log2BI(const BigInt& x) {
    return NTL::conv<double>(NTL::log(NTL::to_RR(x))/0.69314718056);
}

typedef NTL::RandomStreamPush PRGbackupClass; // backup/restore of PRG state
inline void initRandomness(const std::string& st) {
    NTL::SetSeed((unsigned char*)st.data(), st.length());
}

// Break a vector v over GF(p^ell) (with coefficients in [+-P/2]) into
// two "digit" vectors hi,lo, where lo = (v mod radix) \in [+-radix/2]
// and hi = (v-lo)/radix.
void breakTwoDigits(EVector& hi, EVector& lo, const EVector& v, const BigInt& radix);

inline BigInt balanced(const Scalar& s) {
    static auto Pover2 = NTL::ZZ_p::modulus()/2;
    if (rep(s) > Pover2)
        return rep(s)-NTL::ZZ_p::modulus();
    else
        return rep(s);
}
inline BIVector balanced(const SVector& sv) {
    BIVector bv; resize(bv, sv.length());
    for (int i=0; i<sv.length(); i++)
        bv[i] = balanced(sv[i]);
    return bv;
}
inline BIVector balanced(const Element& e) {
    SVector sv; conv(sv, e);
    return balanced(sv);
}
inline NTL::Vec<BIVector> balanced(const EVector& ev) {
    NTL::Vec<BIVector> vbv;
    vbv.SetLength(ev.length());
    for (int i=0; i<ev.length(); i++)
        vbv[i] = balanced(ev[i]);
    return vbv;
}
inline NTL::mat_ZZ balanced(const SMatrix& sm) {
    static auto Pover2 = NTL::ZZ_p::modulus()/2;
    NTL::mat_ZZ mat;
    conv(mat, sm);
    for (int i=0; i<mat.NumRows(); i++) for (int j=0; j<mat.NumCols(); j++) {
        if (mat[i][j]>Pover2)
            mat[i][j] -= NTL::ZZ_p::modulus();
    }
    return mat;
}
inline NTL::Mat<BIVector> balanced(const EMatrix& emat) {
    NTL::Mat<BIVector> mbv;
    mbv.SetDims(emat.NumRows(), emat.NumCols());
    for (int i=0; i<mbv.NumRows(); i++) for (int j=0; j<mbv.NumCols(); j++) {
        mbv[i][j] = balanced(emat[i][j]);
    }
    return mbv;
}



inline std::ostream& printScalar(std::ostream& st, const Scalar& sc) {
    BigInt szz(NTL::INIT_SIZE,4);
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
    size_t ell = scalarsPerElement();
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
