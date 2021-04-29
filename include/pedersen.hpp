#ifndef _PEDERSEN_HPP_
#define _PEDERSEN_HPP_
/* ceddersen.hpp - Pedersen commitments
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
#include <cstring>
#include <vector>

// The only lines in this file that are specific to our scalar space being
// modulo the group order of Curve 25519 are this include and the typedefs
// of scalar and point below. Hopefully this will make it easier to extend
// the scope of this code also to other groups, should we want to do it in
// the future.
#include "scalar25519.hpp"

/* Pedersen vector-commitments are defined relative to some generators.
 * In our application we have the "base" generator and in addition two
 * vectors of "G" and "H" generators. Specifically, each context object
 * has some string tag (to specify the context for it), and an optional
 * key. The generators are then computed as
 * 
 *   G_i = hashToCurve(tag+"G"+str(i), key)
 *   H_i = hashToCurve(tag+"H"+str(i), key)
 * 
 * A plaintext to be committed to is a vector in Z_P^{\leq N}, specified
 * by a map { j_1->a_1, j_2->a_2, ... j_n->a_n } where the j_i's are
 * (disjoint, sorted) indexesand the a's are scalars.
 * A "G-commitment"/"H-commitment" to this plaintext is a point
 * 
 *   C_G = r*base + \sum_i a_{j_i}*G_{j_i}
 *   C_H = r*base + \sum_i b_{j_i}*H_{j_i}
 * 
 * and we also consider double-commitments to two such plaintext vectors,
 * which is just a sum of a G-commitment and an H-commitment:
 * 
 *   C = base*r + \sum_i a_{j_i}*G_{j_i} + \sum_i b_{j_i}*H_{j_i}
 * 
 * where both range over the same set of indexes.
 * 
 * We also use commitments with yet another generator F, where we have
 *   C_G = r*base + alpha*F + \sum_i a_{j_i}*G_{j_i}
 *   C = r*base + alpha*F + \sum_i a_{j_i}*G_{j_i} + \sum_i b_{j_i}*H_{j_i}
 * These commitments are used in a context where the verifier supplies F,
 * after seeing some "F free" commitments.
 **/
#include <map>
#include "scalar25519.hpp"
#include "point25519.hpp"

namespace DLPROOFS { // FIXME: what namespace should we use here?
using CRV25519::Scalar, CRV25519::Point, CRV25519::hashToCurve;

// Some utility functions

inline size_t next2power(size_t v) {
    v--;
    for (size_t i=1; i<sizeof(size_t)*8; i *= 2)
        v |= v >> i;
    return v+1;
}

// returns the smallest ell such that 2^{ell} >= n
inline size_t log2roundUp(size_t n) {
    for (size_t ell=0; ell<sizeof(size_t)*8; ell++) {
        if ((1UL << ell) >= n)
            return ell;
    }
    return sizeof(size_t)*8;
}

// compute \sum_i Gi*xi (code in pedersen.cpp)
Point multiExp(const Point* Gs, size_t n, const Scalar* xes);

// set gi *= x for all i
void multiBaseOneExp(Point* Gs, size_t n, const Scalar& x);

// with Gs=(Gs1|Gs2), set Gs1 += Gs2 * x
void foldGenerators(Point* Gs, size_t n, const Scalar& x, size_t nOver2);

// compute \sum_i Gi*zi, where the zi's are the subset products of the
// xi's, modifies the generators in Gs and returns the result in Gs[0]
void expSubsetProduct(Point* Gs, size_t n, const Scalar* xes);

// Functions for commitment/de-commitment

inline Point commit(const Point* Gs, const Scalar* xes, size_t n, const Scalar& r,
    const Point& F=Point::identity(), const Scalar& alpha=Scalar()) {
    return Point::base()*r + F*alpha + multiExp(Gs, n, xes);
}
inline bool verifyCom(const Point& c, const Point* Gs, const Scalar* xes, size_t n,
    const Scalar& r, const Point& F=Point::identity(), const Scalar& alpha=Scalar()) {
    return (commit(Gs, xes, n, r, F, alpha)==c);
}

inline Point commit2(const Point* Gs, const Scalar* xes,
        const Point* Hs, const Scalar* ys, size_t n, const Scalar& r,
        const Point& F=Point::identity(), const Scalar& alpha=Scalar()) {
    return Point::base()*r + F*alpha + multiExp(Gs, n, xes) + multiExp(Hs, n, ys);
}
inline bool verifyCom2(const Point& c, const Point* Gs, const Scalar* xes,
        const Point* Hs, const Scalar* ys, size_t n, const Scalar& r,
        const Point& F=Point::identity(), const Scalar& alpha=Scalar()) {
    return (commit2(Gs, xes, Hs, ys, n, r, F, alpha)==c);
}

// A Pedersen context defines the generators to use
struct PedersenContext {
    std::string tag;
    //std::vector<unsigned char> key;
    explicit PedersenContext(const std::string& t=std::string()): tag(t) {};

    const Point getG(int i) { // returns G_i
        std::string label = tag+"G"+std::to_string(i);
        return hashToCurve((unsigned char*)label.data(), label.size());
    }
    const Point getH(int i) { // returns H_i
        std::string label = tag+"H"+std::to_string(i);
        return hashToCurve((unsigned char*)label.data(), label.size());
    }
};

} // end of namespace DLPROOFS
#endif // ifndef _PEDERSEN_HPP_
