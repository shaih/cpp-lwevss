/* shamir.cpp - Shamir secret sharing
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
#include <cassert>
#include "shamir.hpp"
#include "regevProofs.hpp"

using namespace ALGEBRA;

namespace TOOLS {

// compute the parity-check matrix H
void SharingParams::computeKernel() {
    int nHcols = n()+1; // number of columns in H

    // Set the generating matrix G, and then H is its kernel. The columns
    // of G span the space of valid sharings at the evaluation points
    // (0, i_1, i_2, ..., i_n): The j'th column is the evaluation of
    // the polynomial p(X)=X^j at all these points.
    SMatrix G;
    resize(G, nHcols, t());

    // The first columns of G is an all-1 column
    for (int i=0; i<nHcols; i++)
        conv(G[i][0], 1);

    // The j'th column euqals the j-1'st one times the evaluation points
    for (int j=1; j<t(); j++) {
        int i=1; // row i=0 need not change
        for (auto ep: evalPoints) { // ep is an int evaluation point
            G[i][j] = G[i][j-1] * ep;
            i++;
        }
    }
    kernel(H,G); // compute H
#ifdef DEBUG
    assert(*evalPoints.begin()>0);
    assert(H.NumRows()==nHcols-t() && H.NumCols()==nHcols);
#endif
}

// Compute random secret-sharings, the secret itself is returned in
// the 1st entry of the vector v, followed by the shares in all the
// evaluation points (in order).
void SharingParams::newSharing(SVector& v, const Scalar& s) const {
    // Choose a random polynomial with s as the free term
    SPoly p;
    for (int i=t()-1; i>0; --i) {
        Scalar r;
        randomizeScalar(r);
        SetCoeff(p, i, r);
    }
    SetCoeff(p, 0, s); // the free term is s

    // Evaluare p in all the evaluation points
    SVector evPoints;
    resize(evPoints, n()+1);
    int i=1; // start from 1 since evPoints[0] = 0
    for (auto ep: evalPoints) // ep is an int evaluation points
        conv(evPoints[i++], ep);
    
    // Multi-evaluation
    eval(v, p, evPoints);
};

// Compute the lagrange coefficients for a size-t reconstruction set
// (i.e. a t-subset of evalPoints). For a set {x_1, x_2, ..., x_t},
// this function returns a t-vector of scalars {s_1,s_2, ..., s_t}
// where s_i = \prod_{j\ne i} x_j/(x_j-x_i).
SVector SharingParams::lagrangeCoeffs(const EvalSet& recSet) const {
    SVector v; resize(v, recSet.size());
    int i = 0;
    for (auto xi: recSet) { // go over the evaluation points
        Scalar numer, denom;
		conv(numer, 1);     // initialize both to 1
		conv(denom, 1);     // initialize both to 1
		for (auto xj: recSet) { // go over the evaluation points
			if (xi != xj) {
                numer *= xj;
                denom *= (xj-xi);
            }
		}
        v[i++] = numer / denom;
	}
    return v;
}

// Recover the secret from its sharing at the given reconstruction set
Scalar SharingParams::getSecret(const SVector& sharing, const EvalSet& recSet) {
    SVector coeffs = lagrangeCoeffs(recSet);
    return innerProduct(coeffs, sharing);
}

} // end of namespace TOOLS
