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

namespace REGEVENC {

// Each row of the n-by-m matrix M over 0/+-1 is represented by a binary
// vector of length 2m. Every two bits x,y in this vector represent a
// trenary number with (00)-> 0, (01)-> 1, (10)-> -1.
//
// This class offers a rather limited functionality, all you can do
// is access individual elements ot multiply by RegevEnc::Vector or
// RegevEnc::Matrix

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

void leftVecMult(Vector& result, const Vector& v, const TernaryMatrix& mat);
void rightVecMult(Vector& result, const TernaryMatrix& mat, const Vector& v);
void leftMatMult(Matrix& result, const Matrix& mat1, const TernaryMatrix& mat2);
void rightMatMult(Matrix& result, const TernaryMatrix& mat1, const Matrix& mat2);

inline Vector operator*(const Vector& v, const TernaryMatrix& mat) {
    Vector res;
    leftVecMult(res, v, mat);
    return res;
}
inline Vector operator*(const TernaryMatrix& mat, const Vector& v) {
    Vector res;
    rightVecMult(res, mat, v);
    return res;
}
inline Matrix operator*(const Matrix& mat1, const TernaryMatrix& mat2) {
    Matrix res;
    leftMatMult(res, mat1, mat2);
    return res;
}
inline Matrix operator*(const TernaryMatrix& mat1, const Matrix& mat2) {
    Matrix res;
    rightMatMult(res, mat1, mat2);
    return res;
}

} // end of namespace REGEVENC
#endif // #ifndef _TERNARY_MATRIX_HPP_
