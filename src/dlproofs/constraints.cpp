/* constraints.cpp - manipulating constraints over Scalars
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
#include <vector>
#include <queue> // for std::priority_queue
#include "constraints.hpp"

namespace DLPROOFS {

CRV25519::Scalar dbgSum;

// A class for comparing iterators from different constraints, to be
// used with std::priority_queue
class CompIter {
public:
    size_t cIdx; // index of current constraint in the constraints vector
    std::map<size_t, Scalar>::const_iterator it; // current item in constraint
};
// We compare them in reverse order, sine the std::priority_queue::top
// reutrns the largest element and we want the smallest
bool operator<(const CompIter& a, const CompIter& b) { //compare keys
    return a.it->first > b.it->first;
}
bool operator>(const CompIter& a, const CompIter& b) {return b<a;}
bool operator<=(const CompIter& a, const CompIter& b) {return !(b<a);}
bool operator>=(const CompIter& a, const CompIter& b) {return !(a<b);}
bool operator==(const CompIter& a, const CompIter& b) { //compare keys
    return a.it->first == b.it->first;
}
bool operator!=(const CompIter& a, const CompIter& b) {return !(a==b);}

Scalar innerProduct(const PtxtVec& v1, const PtxtVec& v2) {
    Scalar sum;
    auto it1 = v1.begin();
    auto it2 = v2.begin();
    while (it1 != v1.end() && it2 != v2.end()) {
        if (it1->first < it2->first) ++it1;
        else if (it2->first < it1->first) ++it2;
        else { // found an element that appears in both
            sum += it1->second * it2->second;
            ++it1; ++it2;
        }
    }
    return sum;
}

// Merges multiple constraints by taking a linear combination of them.
// The resulting constraint is \sum_i constraints[i]*coeffs[i], where
// addition semantics is as in the addTerm method. That is, for each
// constraint c \in constraints, we either insert a multiple of c if it
// is not already there, or add that multiple to what's already there.
//
// NOTE: This implementation is a textbook example of premature optimization,
// it is 20% faster than the trivial immplementation from the merge2
// function (below, commented out).  The result is <10ms faster, out
// of a process that's liekly to take seconds/minutes/hours.
void LinConstraint::merge(const std::vector<LinConstraint>& constraints,
                                const std::vector<Scalar>& coeffs) {
    if (constraints.size() != coeffs.size())
        throw std::runtime_error("LinConstraint::merge argument size mismatch");

    terms.clear();
    equalsTo = Scalar(); // initialize to zero

    // This implementation relies on the constraints being sorted by
    // index in increasing order
    //
    // We go over the terms in order of their indexes, so we only push
    // each term to the resulting list once, after we are done preparing
    // it. For that purpose we use a priority list, sorted by the index.

    std::priority_queue<CompIter> current;
      // To hold the "current" items, one from each constraint

    // Initialize current with iterators pointing to 1st item from
    // each constraint.
    for (size_t i=0; i<constraints.size(); i++) {
        if (constraints[i].terms.size() > 0 && !coeffs[i].isZero())
            current.push( CompIter{i, constraints[i].terms.begin()} );
    }
    if (current.empty()) // empty constraints, nothing to do
        return;

    std::pair<size_t, Scalar> curTerm; // the scalar is initialized to zero
    curTerm.first = current.top().it->first;
    while (!current.empty()) {
        // process the next term from any of the constraints
        size_t cIdx = current.top().cIdx;
        auto& nextTerm = *current.top().it; // the one with smallest index

        // If are still working on the same term, just add to it. Else
        // (if we moved on to a new index), insert to the list the term
        // that we prepared before, and start working on the new term.
        // 
        if (nextTerm.first == curTerm.first) {
            // add next.scalar * coeff to the scalar in curTerm
            Scalar tmp = nextTerm.second;
            tmp *= coeffs[cIdx];
            curTerm.second += tmp;
        }
        else {
            if (!curTerm.second.isZero()) {
                terms.insert(terms.end(), curTerm);
                // insert completed term to end of constraint
            }
            curTerm = nextTerm;    // start working on new term
            curTerm.second *= coeffs[cIdx];
        }
        // remove the top from the list, replace it by the next iterator
        // from the corresponding constraint
        CompIter toPush = current.top(); // make a copy before popping
        current.pop();
        toPush.it++; // advance the iterator
        if (toPush.it != constraints[cIdx].terms.end())
            current.push(toPush);
    }
    // insert the last term that we worked on at the end
    terms.insert(terms.end(), curTerm);

    // Set the b term (equalsTo) to the same linear combination of
    // the b terms in the merged constraints
    for (size_t i=0; i<constraints.size(); i++) {
        if (constraints[i].terms.size() > 0 && !coeffs[i].isZero()) {
            Scalar tmp = constraints[i].equalsTo;
            tmp *= coeffs[i];
            this->equalsTo += tmp;
        }
    }
}

void QuadConstraint::merge(const std::vector<QuadConstraint>& constraints,
                           const std::vector<Scalar>& coeffs)
{
    if (constraints.size() != coeffs.size())
        throw std::runtime_error("QuadConstraint::merge argument mismatch");

    indexes.clear();
    equalsTo = Scalar(); // init to zero
    for (size_t i=0; i<constraints.size(); i++) {
        const Scalar& coeff = coeffs[i];
        const QuadConstraint& cnstr = constraints[i];
        // Add the terms from constraints[i] to *this
        indexes.insert(cnstr.indexes.begin(), cnstr.indexes.end());
        equalsTo += cnstr.equalsTo * coeff * coeff;
    }
}

// Remove from c1 all the keys that appear also in c2
static void setDifference(LinConstraint& c1, const QuadConstraint& c2)
{
    auto it1 = c1.terms.begin();
    auto it2 = c2.indexes.begin();
    while (it1 != c1.terms.end() && it2 != c2.indexes.end()) {
        // if they both point to the same key, remove key from c1
        if (it1->first < *it2) ++it1;
        else if (*it2 < it1->first) ++it2;
        else { // found an element that appears in both
            it1 = c1.terms.erase(it1);
            // NOTE: Hopefull that's not a memory leak, does map.erase
            //       deallocates the memory of the erased pair?
            ++it2; // advance the other iterator
        }
    }
}

// Split the src map into the intersection with teh sliptBy set and
// the set-difference between them. Return an index one larger than
// the max index in src and splitBy
size_t splitPtxtVec(PtxtVec& intersection, PtxtVec& setDiff,
                const PtxtVec& src, const std::set<size_t>& splitBy)
{
    intersection.clear();
    setDiff.clear();
    // edge cases, if one or both of src,splitBy are empty
    if (src.empty()) {
        if (splitBy.empty()) return 1;
        else return 1 + *(splitBy.rbegin()); // largest element +1
    }
    if (splitBy.empty()) {
        setDiff = src;
        return 1 + src.rbegin()->first;
    }
    // general case, iterate over src and splitBy
    auto it1 = src.begin();
    auto it2 = splitBy.begin();
    while (it1 != src.end() && it2 != splitBy.end()) {
        // Elements in src but not splitBy go to setDiff
        if (it1->first < *it2) {
            setDiff.insert(setDiff.end(), *it1);
            ++it1;
        }
        else if (*it2 < it1->first) // ignore things not in src
            ++it2;
        else { // found an element that appears in both
            intersection.insert(intersection.end(), *it1);
            ++it1; ++it2; // advance both iterators
        }
    }
    // put the remaining of src (if any) in setDiff
    if (it1 != src.end())
        setDiff.insert(it1, src.end());

    return std::max(src.rbegin()->first, *(splitBy.rbegin())) +1;
}

// Removes from the linear constraint all variables that also appear in
// the quadratic constraint. This function intoruces one more variable
// that was not in the original constraints, which will appear in both
// the new constraints. Returns the index of the new variable.
size_t makeAlmostDisjoint(LinConstraint& lin, QuadConstraint& quad, const Scalar& s)
{
    // Set the b term (equalsTo) in quad to qual.equalsTo - s*lin.equalsTo
    // and zero out that term in lin
    Scalar tmp = lin.equalsTo;
    tmp *= s;
    quad.equalsTo -= tmp;
    lin.equalsTo.setInteger(0); // set to zero

    // remove from lin the terms that also appear in quad
    setDifference(lin, quad);

    // add to both a term with a new index and scalar=1
    size_t newKey = std::max(largestKey(lin), largestKey(quad)) +1;
    quad.indexes.insert(quad.indexes.end(), newKey); // insert at the end
    lin.terms.insert(lin.terms.end(), std::make_pair(newKey, Scalar().setInteger(1)));
    return newKey;
}

LinConstraint& LinConstraint::addTerm(size_t idx, const Scalar& s) {
    Scalar& inMap = terms[idx]; // insert if not already there
    inMap += s;
    return *this;
}

// Merge two quadratic constraints, throws if they are not disjoint
QuadConstraint& QuadConstraint::operator+=(const QuadConstraint& other) {
    if (other.indexes.empty()) return *this; // nothing to do
    if (indexes.empty()) {
        *this = other;
        return *this;
    }
    // check that the sets are disjoint
    if (*indexes.begin()<=*other.indexes.rbegin()
        && *indexes.rbegin()>=*other.indexes.begin()) {
        auto it1 = indexes.begin();
        auto it2 = other.indexes.begin();
        while (it1 != indexes.end() && it2 != indexes.end()) {
            if (*it1 < *it2)      ++it1;
            else if (*it2 < *it1) ++it2;
            else // found a common element
                throw std::runtime_error("QuadConstraint::operator+=: common index "+std::to_string(*it1)+" found");
        }
    }
    // add other to this
    indexes.insert(other.indexes.begin(), other.indexes.end());
    equalsTo += other.equalsTo;
    return *this;
}

/***************************************************************/
#if 0
void LinConstraint::merge2(const std::vector<LinConstraint>& constraints, const std::vector<Scalar>& coeffs)
{
    if (constraints.size() != coeffs.size())
        throw std::runtime_error("LinConstraint::merge argument mismatch");

    terms.clear();
    equalsTo = Scalar(); // init to zero

    for (size_t i=0; i<constraints.size(); i++) {
        const Scalar& coeff = coeffs[i];
        // Add multiples of the terms from constraints[i] to *this
        for (auto& c : constraints[i].terms) { // c is a pair (idx, scalar)
            Scalar& x = terms[c.first]; // find or insert a new term
            Scalar tmp = c.second;      // add c.second * coeff to x
            tmp *= coeff;
            x += tmp;
        }
        // add the b term from constraints[i] (time coeff) to *this
        Scalar tmp = constraints[i].equalsTo;
        tmp *= coeff;
        equalsTo += tmp;
    }
    // remove terms with scalar=0
    std::vector<int> toRemove;
    for (auto& t : terms) {
        if (t.second.isZero()) {
            toRemove.push_back(t.first);
        }
    }
    for (auto i : toRemove)
        terms.erase(i);
}
#endif

// Check sum_i constr[i]*witness[i]=cnstr.equalsTo, and that the indexes match
bool checkConstraint(const LinConstraint& cnstr, const PtxtVec& witness)
{
    Scalar sum;
    auto it1 = cnstr.terms.begin();
    auto it2 = witness.begin();
    while (it1 != cnstr.terms.end() && it2 != witness.end()) {
        if (it1->first != it2->first) // mismatched indexes
            return false;
        sum += it1->second * it2->second;
        ++it1; ++it2;
    }
    if (it1 != cnstr.terms.end() || it2 != witness.end())
        return false;
    return (sum == cnstr.equalsTo);
}
// Check sum_i constr[i]*witness[i]=cnstr.equalsTo, but allow the
// witness to have more variables that just what's in the constraint
bool checkConstraintLoose(const LinConstraint& cnstr, const PtxtVec& witness)
{
    Scalar sum;
    auto it1 = cnstr.terms.begin();
    while (it1 != cnstr.terms.end()) {
        if (it1->second != CRV25519::Scalar()) { // if not zero
            auto it2 = witness.find(it1->first); // find the corresponding variable
            if (it2 == witness.end())            // no matching witness variable
                return false;
            sum += it1->second * it2->second;
        }
        ++it1;
    }
    if (sum != cnstr.equalsTo) dbgSum = sum;
    return (sum == cnstr.equalsTo);
}

// Check that sum_i x[i]*y[i] = cnstr.equalsTo, and that the indexes match
bool checkConstraint(const QuadConstraint& cnstr, const PtxtVec& xs, const PtxtVec& ys)
{
    Scalar sum;
    auto it = cnstr.indexes.begin();
    auto xit = xs.begin();
    auto yit = ys.begin();
    while (it != cnstr.indexes.end() && xit != xs.end() && yit != ys.end()) {
        if (*it != xit->first || *it != yit->first) // mismatched indexes
            return false;
        sum += xit->second * yit->second;
        ++it; ++xit; ++yit;
    }
    if (it != cnstr.indexes.end() || xit != xs.end() || yit != ys.end())
        return false;
    return (sum == cnstr.equalsTo);
}
// Check that sum_i x[i]*y[i] = cnstr.equalsTo, but allow the
// witness to have more variables that just what's in the constraint
bool checkConstraintLoose(const QuadConstraint& cnstr,
                          const PtxtVec& xs, const PtxtVec& ys)
{
    Scalar sum;
    auto it = cnstr.indexes.begin();
    while (it != cnstr.indexes.end()) {
        auto xit = xs.find(*it); // find the corresponding x and y
        auto yit = ys.find(*it);
        if (xit==xs.end() || yit==ys.end()) // x or y not found
            return false;
        sum += xit->second * yit->second;
        ++it;
    }
    if (sum != cnstr.equalsTo) dbgSum = sum;
    return (sum == cnstr.equalsTo);
}

void LinConstraint::debugPrint() const {
    std::cout << "{[\n";
    for (auto& t : terms) {
        std::cout << "  " << t.first << "->" << (size_t)t.second.bytes[0] << "...\n";
    }
    std::cout << "], " << (size_t)equalsTo.bytes[0] << "... }\n";
}
void QuadConstraint::debugPrint() const {
    std::cout << "{[";
    for (auto i : indexes) {
        std::cout << " " << i;
    }
    std::cout << " ], " << (size_t)equalsTo.bytes[0] << " " << (size_t)equalsTo.bytes[1] << "... }\n";
}

} // end of namespace DLPROOFS
