/* regevProofs.cpp - A 0/+-1 matrix
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
#include <stdexcept>
#include "algebra.hpp"
//#include "regevEnc.hpp" // brings in NTL compatibility
#include "ternaryMatrix.hpp"
extern "C" {
    #include <sodium.h>
}

namespace ALGEBRA {

// fill with random 0/+-1 values, Pr[0]=1/2, Pr[+-1]=1/4
TernaryMatrix& TernaryMatrix::random() {
    size_t nBytes = NumRows() * ((NumCols()+3)/4);
    unsigned char bytes[nBytes];
    randombytes_buf(bytes, nBytes); // fill buffer with random bytes
    return setFromBytes(bytes, NumRows(), NumCols());
}

    // Set the value from the give nbits, assumes that sizeof(bits)>=n*ceil(m/4)
    // If the given bits are random then Pr[0]=1/2, Pr[+-1]=1/4
TernaryMatrix& TernaryMatrix::setFromBytes(unsigned char* bytes)
{
    const size_t bytesInRow = (NumCols()+3)/4;
    size_t rowByteIdx = 0; // index in bytes[]
    for (auto &r : rows) {
        for (size_t i=0; i<bytesInRow; i++) { // four 2-bit values from each byte
            unsigned char theByte = bytes[rowByteIdx+i];
            // for each pair of bits, if both are one then set both to zero
            unsigned char mask1 = theByte ^ ((theByte & 0xaa)>>1);
            unsigned char mask2 = (mask1<<1)| 0x55; //theByte ^ ((theByte & 0x55)<<1);
            r.rep[i] = theByte & mask1 & mask2;
        }
        rowByteIdx += bytesInRow;
    }
    return *this;
}

template<class VecType, class ElementType>
void leftVecMult(VecType& result, const VecType& v, const TernaryMatrix& mat)
{
    if (v.length() != mat.NumRows()) {
        throw std::runtime_error("TernaryMatrix::leftVecMult: v*M dimension mismatch");
    }
    resize(result, mat.NumCols());
    for (size_t j=0; j<result.length(); j++)
        clear(result[j]);

    VecType minusV = -v;
    const ElementType& zero = ElementType::zero();
    for (size_t i=0; i<v.length(); i++) {
        const ElementType* vals[] = {&minusV[i], &zero, &v[i] };
        for (size_t j=0; j<result.length(); j++) {
            int m_ij = mat[i][j];          // a -1/0/1 value
            result[j] += *(vals[m_ij +1]); // 0/1/2 index into vals
        }
    }
}
void leftVecMult(SVector& result, const SVector& v, const TernaryMatrix& mat) {
    leftVecMult<SVector,Scalar>(result, v, mat);
}
void leftVecMult(EVector& result, const EVector& v, const TernaryMatrix& mat) {
    leftVecMult<EVector,Element>(result, v, mat);
}

template<class VecType, class ElementType>
void rightVecMult(VecType& result, const TernaryMatrix& mat, const VecType& v)
{
    if (v.length() != mat.NumCols()) {
        throw std::runtime_error("TernaryMatrix::rightVecMult: M*v dimension mismatch");
    }
    resize(result, mat.NumRows());
    for (size_t j=0; j<result.length(); j++)
        clear(result[j]);

    VecType minusV = -v;
    const ElementType& zero = ElementType::zero();
    for (size_t i=0; i<v.length(); i++) {
        const ElementType* vals[] = { &minusV[i], &zero, &v[i] };
        for (size_t j=0; j<result.length(); j++) {
            int m_ji = mat[j][i];          // a -1/0/1 value
            result[j] += *(vals[m_ji +1]); // 0/1/2 index into vals
        }
    }
}
void rightVecMult(SVector& result, const TernaryMatrix& mat, const SVector& v) {
    rightVecMult<SVector,Scalar>(result, mat, v);
}
void rightVecMult(EVector& result, const TernaryMatrix& mat, const EVector& v) {
    rightVecMult<EVector,Element>(result, mat, v);
}

template<class MatType>
void leftMatMult(MatType& result, const MatType& mat1, const TernaryMatrix& mat2)
{
    if (mat1.NumCols() != mat2.NumRows()) {
        throw std::runtime_error("TernaryMatrix::leftMatMult: M1*M2 dimension mismatch");
    }
    resize(result, mat1.NumRows(), mat2.NumCols());
    for (size_t i=0; i<result.NumRows(); i++)
        leftVecMult(result[i], mat1[i], mat2); // vec-by-mat multiplication
}
void leftMatMult(SMatrix& result, const SMatrix& mat1, const TernaryMatrix& mat2) {
    leftMatMult<SMatrix>(result, mat1, mat2);
}
void leftMatMult(EMatrix& result, const EMatrix& mat1, const TernaryMatrix& mat2) {
    leftMatMult<EMatrix>(result, mat1, mat2);
}

template<class MatType, class VecType>
void rightMatMult(MatType& result, const TernaryMatrix& mat1, const MatType& mat2)
{
    if (mat1.NumCols() != mat2.NumRows()) {
        throw std::runtime_error("TernaryMatrix::rightMatMult: M1*M2 dimension mismatch");
    }
    resize(result, mat1.NumRows(), mat2.NumCols());
    VecType inTmp, outTmp;
    resize(inTmp, mat2.NumRows());
    for (size_t j=0; j<result.NumCols(); j++) {
        for (size_t i=0; i<inTmp.length(); i++)  // copy column into a vector
            inTmp[i] = mat2[i][j];
        rightVecMult(outTmp, mat1, inTmp);       // mat-by-vec multiplication
        for (size_t i=0; i<outTmp.length(); i++) // copy result into a column
            result[i][j] = outTmp[i];
    }
}
void rightMatMult(SMatrix& result, const TernaryMatrix& mat1, const SMatrix& mat2) {
    rightMatMult<SMatrix,SVector>(result, mat1, mat2);
}
void rightMatMult(EMatrix& result, const TernaryMatrix& mat1, const EMatrix& mat2) {
    rightMatMult<EMatrix,EVector>(result, mat1, mat2);
}


size_t TernaryEMatrix::degree; // e = degree of GF(p^e)
Element TernaryEMatrix::X;     // The ring element whose representation is X
void TernaryEMatrix::init() {
    TernaryEMatrix::degree = NTL::deg(NTL::ZZ_pE::modulus());
    NTL::ZZ_pX px;
    NTL::SetCoeff(px,1);         // Set the coeff of X^1 to 1
    conv(TernaryEMatrix::X, px); // convert X to an element of GP(p^e)
}

// Accessing an element as matrix(i,j), note that this returns a "copy"
// of the stored element, not a reference to it. So while x=matrix(i,j)
// works, matrix(i,j) = x does not.
Element TernaryEMatrix::operator()(size_t i, size_t j) {
    Element e;
    SVector v;
    v.SetLength(degree);
    for (size_t n=0; n < Ms.size(); n++) {
        v[n] = Ms[n][i][j];
    }
    conv(e, v); // build from coefficients
    return e;
}

// randomize or set from bytes. Fill with 0/+-1 representated values,
// for every coefficient we have Pr[0]=1/2, Pr[+-1]=1/4
TernaryEMatrix& TernaryEMatrix::random() {
    const size_t nBytes = degree * NumRows() * ((NumCols()+3)/4);
    unsigned char bytes[nBytes];
    randombytes_buf(bytes, nBytes); // fill buffer with random bytes
    return setFromBytes(bytes, NumRows(), NumCols());
}

// Set the value from the give nbits, assumes that sizeof(bits)>=ceil(n*m/4)
// If the given bits are random then Pr[0]=1/2, Pr[+-1]=1/4
TernaryEMatrix& TernaryEMatrix::setFromBytes(unsigned char* bytes) {
    const size_t bytesPerMat = NumRows() * ((NumCols()+3)/4);
    for (size_t i=0; i< Ms.size(); i++)
        Ms[i].setFromBytes(bytes + (i*bytesPerMat));
    return *this;
}

/*EVector& operator+=(EVector& ev, const SVector& sv) {
    if (ev.length() != sv.length()) {
        throw std::runtime_error("EVector += SVector: size mismatch");
    }
    for (size_t i=0; i<ev.length(); i++)
        ev[i] += sv[i];
    return ev;
}*/

void leftVecMult(EVector& result, const EVector& ev, const TernaryEMatrix& mat) {
    if (mat.Ms.size() != mat.degree || mat.degree <= 0) {
        throw std::runtime_error("TernaryEMatrix::leftVecMult: uninitialized matrix");
    }
    leftVecMult<EVector,Element>(result, ev, mat.Ms[mat.degree -1]);
    for (int i=mat.degree-2; i>=0; --i) {
        EVector tmp;
        leftVecMult<EVector,Element>(tmp, ev, mat.Ms[i]);
        result *= mat.X;
        result += tmp;
    }
}
void rightVecMult(EVector& result, const TernaryEMatrix& mat, const EVector& ev) {
    if (mat.Ms.size() != mat.degree || mat.degree <= 0) {
        throw std::runtime_error("TernaryEMatrix::rightVecMult: uninitialized matrix");
    }
    rightVecMult<EVector,Element>(result, mat.Ms[mat.degree -1], ev);
    for (int i=mat.degree-2; i>=0; --i) {
        EVector tmp;
        rightVecMult<EVector,Element>(tmp, mat.Ms[i], ev);
        result *= mat.X;
        result += tmp;
    }
}
void leftMatMult(EMatrix& result, const EMatrix& mat1, const TernaryEMatrix& mat2) {
    if (mat2.Ms.size() != mat2.degree || mat2.degree <= 0) {
        throw std::runtime_error("TernaryEMatrix::leftMatMult: uninitialized matrix");
    }
    leftMatMult<EMatrix>(result, mat1, mat2.Ms[mat2.degree -1]);
    for (int i=mat2.degree-2; i>=0; --i) {
        EMatrix tmp;
        leftMatMult<EMatrix>(tmp, mat1, mat2.Ms[i]);
        result *= mat2.X;
        result += tmp;
    }
}
void rightMatMult(EMatrix& result, const TernaryEMatrix& mat1, const EMatrix& mat2) {
    if (mat1.Ms.size() != mat1.degree || mat1.degree <= 0) {
        throw std::runtime_error("TernaryEMatrix::rightMatMult: uninitialized matrix");
    }
    rightMatMult<EMatrix,EVector>(result, mat1.Ms[mat1.degree -1], mat2);
    for (int i=mat1.degree-2; i>=0; --i) {
        EMatrix tmp;
        rightMatMult<EMatrix,EVector>(tmp, mat1.Ms[i], mat2);
        result *= mat1.X;
        result += tmp;
    }
}

} // end of namespace REGEVENC

