#ifndef _SHAMIR_HPP_
#define _SHAMIR_HPP_
/* shamir.hpp - Shamir secret sharing
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
#include <set>

#include "algebra.hpp"

namespace TOOLS {
using ALGEBRA::Scalar, ALGEBRA::SVector, ALGEBRA::SMatrix;

typedef std::set<int> EvalSet; // the set of evaluation points

// Holds parameters related to t-of-n secret sharing where the secret
// is at evaluation point 0 and the n evaluation points are specified
// in the constror
struct SharingParams {
    int thr; // the threshold (= polynomial degree plus one)
    EvalSet evalPoints;  // The set of n evaluation points

    SMatrix H;  // The parity-check matrix H
    // Considering a vector x representing the evluations at all the
    // points (0, i_1, i_2, ..., i_n) in order, where the i_j's are
    // specified by the set evalPoints, this is a valid sharing of
    // x[0] iff it satisfies H*x=0 

    int t() const { return thr; }
    int n() const { return evalPoints.size(); }

    void computeKernel(); // compute the parity-check matrix H

    SharingParams() = default;
    SharingParams(const EvalSet& ev, int t): evalPoints(ev), thr(t)
    { computeKernel(); }

    // Compute random secret-sharings, the secret itself is returned in
    // the 1st entry of the vector v, followed by the shares in all the
    // evaluation points (in order).
    void newSharing(SVector& v, const Scalar& s) const; // random sharing of s
    void randomSharing(SVector& v) const{ // random sharing of a random scalar
        Scalar s;
        ALGEBRA::randomizeScalar(s);
        newSharing(v, s);
    }

    // Compute the lagrange coefficients for a size-t reconstruction
    // set (i.e. a t-subset of evalPoints).
    SVector lagrangeCoeffs(const EvalSet& recSet) const;

    // Recover the secret from its sharing at the given reconstruction set
    Scalar getSecret(const SVector& sharing, const EvalSet& recSet);
};

} // end of namespace TOOLS
#endif // #ifndef _SHAMIR_HPP_
