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
        throw std::runtime_error("LinConstraint::merge argument mismatch");

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
    if (s != Scalar()) { // if s != 0
        Scalar& inMap = terms[idx]; // insert if not already there
        inMap += s;
        if (inMap.isZero()) // zeroed out, remove it
            terms.erase(idx);
    }
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
        // if they both point to the same key, remove key from c1
        if (it1->first != it2->first) // mismatched indexes
            return false;
        sum += it1->second * it2->second;
        ++it1; ++it2;
    }
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
        // if they both point to the same key, remove key from c1
        if (*it != xit->first || *it != yit->first) // mismatched indexes
            return false;
        sum += xit->second * yit->second;
        ++it; ++xit; ++yit;
    }
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
