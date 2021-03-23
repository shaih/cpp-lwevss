/* naive.cpp - Naive implementation of multi-exponentiation and related ops
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
#include "scalar25519.hpp"
#include "point25519.hpp"
#include "pedersen.hpp"

namespace DLPROOFS {
using CRV25519::Scalar, CRV25519::Point;

// compute \sum_i Gi*xi, naive implementation
Point multiExp(const Point* Gs, size_t n, const Scalar* xes) {
    Point c = Point::identity();
    for (size_t i=0; i<n; i++)
        c += Gs[i]*xes[i];
    return c;
}

// set gi *= x for all i
void multiBaseOneExp(Point* Gs, size_t n, const Scalar& x) {
    for (size_t i=0; i<n; i++)
        Gs[i] *= x;
}

// with Gs=(Gs1|Gs2), set GS1 += x*GS2
void foldGenerators(Point* Gs, size_t n, const Scalar& x, size_t nOver2) {
    // Exponentiate the 2nd half of the Gs
    multiBaseOneExp(Gs+nOver2, n-nOver2, x);

    // Add to the 1st half
    for (size_t j=0; j<n-nOver2; j++) {
        Gs[j] += Gs[j+nOver2];
    }
}

// compute \sum_i Gi*zi, where the zi's are the subset products of the
// xi's, modifies the generators in Gs and returns the result in Gs[0]
void expSubsetProduct(Point* Gs, size_t n, const Scalar* xes) {
    size_t logn = log2roundUp(n);     // this is the number of xes
    size_t nOver2 = 1UL << (logn-1);
    for (size_t i=0; i<logn; i++) {
        foldGenerators(Gs, n, xes[i], nOver2); // Set Gs1 += Gs2 * x
        n = nOver2;
        nOver2 /= 2;
    }
}

} // end of namespace DLPROOFS
