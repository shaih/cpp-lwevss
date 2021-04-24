#ifndef _TERNARY_MATRIX_HPP_
#define _TERNARY_MATRIX_HPP_
/* ternaryMatrix.hpp - A 0/+-1 matrix
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
#include <string>
#include <stdexcept>
#include "regevEnc.hpp" // brings in NTL compatibility

namespace ALGEBRA {

// TernaryMatrix is an integer matrix over -1/0/1.
// Each row of an n-by-m matrix M is represented by a binary vector
// of length 2m. Every two bits x,y in this vector represent a trenary
// number with (00)-> 0, (01)-> 1, (10)-> -1.
//
// This class offers a rather limited functionality, all you can do is
// access individual elements, or multiply by one of SVector, EVector,
// SMatrix, or EMatrix.

struct TernaryMatrix {
    struct TrenaryRow { // a single -1/0/1 row
        size_t len;
        std::vector<unsigned char> rep; // internal representation
        TrenaryRow(): len(0) {}

        size_t size() const { return len; }
        void resize(size_t m) {
            len = m;
            rep.resize((m+3)/4);
        }
        int operator[](size_t i) const {
            size_t j = i & 0x03; // index two bits in a byte
            int theByte = rep[i/4] >> (2*j);
            return (theByte&1) - ((theByte>>1)&1);
            // subtract one bit from the other, get a -1/0/1 value
        }
        int at(size_t i) const {
            if (i>=len) {
                std::string what = "TrenaryRow::range_check ["
                    +std::to_string(i)+"] but len="+std::to_string(len);
                throw std::out_of_range(what);
            }
            return (*this)[i];
        }
    };
    std::vector<TrenaryRow> rows; // representation: an array of rows

    size_t NumRows() const {return rows.size();}
    size_t NumCols() const {
        if (NumRows()==0) return 0;
        return rows[0].size();
    }

    TernaryMatrix& resize(size_t n, size_t m) {
        rows.resize(n);
        for (auto& row : rows) row.resize(m);
        return *this;
    }

    // read-only access to individual rows
    const TrenaryRow& operator[](size_t i) const { return rows[i]; }
    const TrenaryRow& at(size_t i) const { return rows.at(i); }

    // fill with random 0/+-1 values, Pr[0]=1/2, Pr[+-1]=1/4
    TernaryMatrix& random();
    TernaryMatrix& random(size_t n, size_t m) {
        resize(n,m);
        return random();
    }

    // Set the value from the give nbits, assumes that sizeof(bits)>=ceil(n*m/4)
    // If the given bits are random then Pr[0]=1/2, Pr[+-1]=1/4
    TernaryMatrix& setFromBytes(unsigned char* bytes);
    TernaryMatrix& setFromBytes(unsigned char* bytes, size_t n, size_t m) {
        resize(n,m);
        return setFromBytes(bytes);
    }
};
inline void resize(TernaryMatrix& mat, size_t n, size_t m) { // compatibility
    mat.resize(n,m);
}
inline TernaryMatrix randomTernaryMatrix(size_t n, size_t m) { // factory
    TernaryMatrix tMat;
    return tMat.random(n,m);
}

void leftVecMult(SVector& result, const SVector& v, const TernaryMatrix& mat);
void rightVecMult(SVector& result, const TernaryMatrix& mat, const SVector& v);
void leftMatMult(SMatrix& result, const SMatrix& mat1, const TernaryMatrix& mat2);
void rightMatMult(SMatrix& result, const TernaryMatrix& mat1, const SMatrix& mat2);

void leftVecMult(EVector& result, const EVector& v, const TernaryMatrix& mat);
void rightVecMult(EVector& result, const TernaryMatrix& mat, const EVector& v);
void leftMatMult(EMatrix& result, const EMatrix& mat1, const TernaryMatrix& mat2);
void rightMatMult(EMatrix& result, const TernaryMatrix& mat1, const EMatrix& mat2);

inline SVector operator*(const SVector& v, const TernaryMatrix& mat) {
    SVector res;
    leftVecMult(res, v, mat);
    return res;
}
inline SVector operator*(const TernaryMatrix& mat, const SVector& v) {
    SVector res;
    rightVecMult(res, mat, v);
    return res;
}
inline SMatrix operator*(const SMatrix& mat1, const TernaryMatrix& mat2) {
    SMatrix res;
    leftMatMult(res, mat1, mat2);
    return res;
}
inline SMatrix operator*(const TernaryMatrix& mat1, const SMatrix& mat2) {
    SMatrix res;
    rightMatMult(res, mat1, mat2);
    return res;
}

// TernaryEMatrix is an matrix M over GF(q^e), with power-basis
// representation M = M0 + M1*X + ... + M_{e-1} X^{e-1}, where
// each Mi is a TernaryMatrix.
struct TernaryEMatrix {
    static size_t degree; // e = degree of GF(p^e)
    static Element X;     // The ring element whose representation is X
    static void init();
    // Set the degree and element X, must be called after
    // NTL::ZZ_pE is initialized

    std::vector<TernaryMatrix> Ms; // the internal representation

    size_t NumRows() const {return (Ms.empty()? 0 : Ms[0].NumRows());}
    size_t NumCols() const {return (Ms.empty()? 0 : Ms[0].NumCols());}
    TernaryEMatrix& resize(size_t n, size_t m) {
        Ms.resize(degree);
        for (size_t i=0; i<degree; i++)
            Ms[i].resize(n,m);
        return *this;
    }

    // Element access

    // Accessing an element as matrix(i,j), note that this returns
    // a "copy" of the stored element, not a reference to it.
    // So while x = matrix(i,j) works, matrix(i,j) = x does not.
    Element operator()(size_t i, size_t j);

    // A stupid C++ trick so that we can write matrix[i][j]
    struct IndexProxy {
        TernaryEMatrix& mat; // point to the matrix
        size_t i;            // row index
        IndexProxy(TernaryEMatrix& _m, size_t _i): mat(_m), i(_i){}
        Element operator[](size_t j) { return mat(i,j); }
    };
    IndexProxy operator[](size_t i) { return IndexProxy(*this, i); }

    // randomize or set from bytes. Fill with 0/+-1 representated values,
    // for every coefficient we have Pr[0]=1/2, Pr[+-1]=1/4
    TernaryEMatrix& random();
    TernaryEMatrix& random(size_t n, size_t m) {
        resize(n,m);
        return random();
    }

    // Set the value from the give nbits, assumes that sizeof(bits)>=ceil(n*m/4)
    // If the given bits are random then Pr[0]=1/2, Pr[+-1]=1/4
    TernaryEMatrix& setFromBytes(unsigned char* bytes);
    TernaryEMatrix& setFromBytes(unsigned char* bytes, size_t n, size_t m) {
        resize(n,m);
        return setFromBytes(bytes);
    }
};

void leftVecMult(EVector& result, const EVector& v, const TernaryEMatrix& mat);
void rightVecMult(EVector& result, const TernaryEMatrix& mat, const EVector& v);
void leftMatMult(EMatrix& result, const EMatrix& mat1, const TernaryEMatrix& mat2);
void rightMatMult(EMatrix& result, const TernaryEMatrix& mat1, const EMatrix& mat2);

inline EVector operator*(const EVector& v, const TernaryEMatrix& mat) {
    EVector res;
    leftVecMult(res, v, mat);
    return res;
}
inline EVector operator*(const TernaryEMatrix& mat, const EVector& v) {
    EVector res;
    rightVecMult(res, mat, v);
    return res;
}
inline EMatrix operator*(const EMatrix& mat1, const TernaryEMatrix& mat2) {
    EMatrix res;
    leftMatMult(res, mat1, mat2);
    return res;
}
inline EMatrix operator*(const TernaryEMatrix& mat1, const EMatrix& mat2) {
    EMatrix res;
    rightMatMult(res, mat1, mat2);
    return res;
}

} // end of namespace REGEVENC
#endif // #ifndef _TERNARY_MATRIX_HPP_
