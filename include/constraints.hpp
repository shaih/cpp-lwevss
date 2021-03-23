#ifndef _CONSTRAINTS_HPP_
#define _CONSTRAINTS_HPP_
/* constraints.hpp - manipulating constraints over Scalars
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
#include <map>
#include <vector>
#include <string>
#include <stdexcept>

// Hopefully there are only two lines in this file that are specific
// to our scalar space being modulo the group order of Curve 25519,
// namely this include and the "using scalar" below. If ever we want to
// extend the context to other types of scalars, then maybe it can be
// done by having an abstract scalar type with specific implementations.
#include "scalar25519.hpp"

/* We manipulate two type sof constraints:
 *
 * 1. Linear constraints of the form
 * 
 *    sum_{i=1}^n x_{j_i} * a_{j_i} = b (mod P)
 * 
 * where the j_i's are the indexes, the x'es are the variables, and
 * the a's and b are the public coefficients. Such constraints are
 * represented by the scalar b and a map
 * 
 *   [ j_1->a_{j_1}, j_2->a_{j_2}, ..., j_n->a_{j_n} ]
 * 
 * with the (sorted, unique) indexes j_i in the range [1,N].
 * 
 * 2. Quadratic constraints of the form
 *
 *    sum_{i=1}^n x_{j_i} * y_{j_i} = b (mod P)
 * 
 * where the j_i's are the indexes and the x'es and y's are variables.
 * These constraints are represented by the scalar b and by the set
 * { j_1,...,j_n } of (sorted, unique) indexes j_i in the range [1,N].
 *
 *
 * For a linear constraint we will have an associated Pedersen vector
 * commitment
 * 
 *   C = base*r + \sum_{i=1}^n x_{j_i} * G_{j_i}.
 * 
 * For an inner-product constraint we will have two associated Pedersen
 * vector commitments
 * 
 *   C1 = base*r1 + \sum_{i=1}^n x_{j_i}*G_{j_i}
 *   C2 = base*r2 + \sum_{i=1}^n y_{j_i}*H_{j_i}
 *
 * (where we have the same set of indexes j_i for the x'es and y's.
 * These commitments are defined with respect to a public "canonical"
 * list of generators G_1,...,G_N, H_1,...,H_N.
 * 
 * The main way to manipulate these constraints is by aggregating them,
 * where linear constraints are aggregated by taking a random linear
 * combination of them and quadratic constraints on disjoint variables
 * are aggregated by concatenating them.
 * 
 * Once we have only one constraint of each type we can "move" all the
 * variables that appear in both to the quadratic constraint, resulting
 * in constraints that are almost disjoint on their sets of variables.
 * This transformation introduces one additional variable that appears
 * in both output constraints, hence only "almost disjoint".
 * 
 * Another transformation that we use is taking a quadratic constraint
 *   CNSTR = [ sum_{i=1}^n x_{j_i}*y_{j_i} = b (mod P) ],
 * and producing another constraint with the same indexes but different
 * variables and different scalar
 *   CNSTR' = [ sum_{i=1}^n x'_{j_i}*y'_{j_i} = b' (mod P) ].
 * This transformation has the property that knowledge of x',y' variables
 * satisfying CNSTR' implies also knowldge of x,y variables satisfying the
 * original CNSTR, which in addition satisfy x_{j_i}=y_{j_i} for all i.
 */

namespace DLPROOFS { // FIXME: what namespace should we use here?

using CRV25519::Scalar;
typedef std::map<size_t,Scalar> PtxtVec;

class LinConstraint {
public:
    PtxtVec terms;   // the j -> a terms
    Scalar equalsTo; // the b coefficient

    // Add a term idx->s to a constraint.
    // If this constraint already has a term idx->s' then s will be added
    // to s', resultin gin idx->(s+s'). Otherwise idx->s will be inserted
    // to the constraint. Returns true if a term idx->s' existed before,
    // false if inserted anew.
    LinConstraint& addTerm(size_t idx, const Scalar& s);

    bool operator==(const LinConstraint& other) {
        if (equalsTo != other.equalsTo)
            return false;
        return (terms == other.terms);
    }
    bool operator!=(const LinConstraint& other) { return !(*this==other);}

    // Merges multiple constraints by taking a linear combination of them
    // The resulting constraint is \sum_i constraints[i]*coeffs[i], where
    // addition semantics is as in the addTerm method above.
    void merge(const std::vector<LinConstraint>& constraints, const std::vector<Scalar>& coeffs);

    //void merge2(const std::vector<Constraint>& constraints, const std::vector<Scalar>& coeffs);
    /** used to debug and test the merge method **/

    void debugPrint() const;
};

class QuadConstraint {
public:
    std::set<size_t> indexes; // the j_i indexes
    Scalar equalsTo;          // the b coefficient

    // Add index to a quadratic constraint (throws if already there)
    QuadConstraint& addIdx(size_t idx) {
        auto ret = indexes.insert(idx);
        if (!ret.second) { // index was already there
            throw std::runtime_error("QuadConstraint::addIdx: index "+std::to_string(idx)+" already exists");
        }
        return *this;
    }

    bool operator==(const QuadConstraint& other) {
        return (equalsTo == other.equalsTo && indexes == other.indexes);
    }
    bool operator!=(const QuadConstraint& other) { return !(*this==other);}

    // Merge two quadratic constraints, throws if they are not disjoint
    QuadConstraint& operator+=(const QuadConstraint& other);

    // Transforms a constraint to enforce also x_{j_i}=y_{j_i}
    void enforceXeqY(const Scalar& coeff);

    void debugPrint() const;
};

inline int largestKey(const LinConstraint& c) {
    return (c.terms.empty()? -1 : c.terms.rbegin()->first);
}
inline int largestKey(const QuadConstraint& c) {
    return (c.indexes.empty()? -1 : *(c.indexes.rbegin()));
}

// Remove from the linear constraint all variables that also appear in
// the quadratic constraint. This function intoruces one more variable
// that was not in the original constraints, which will appear in both
// the new constraints. Returns the index of the new variable.
size_t makeAlmostDisjoint(LinConstraint& lin, QuadConstraint& quad, const Scalar& s);

} /* end of namespace DLPROOFS */
#endif // ifndef _CONSTRAINTS_HPP_
