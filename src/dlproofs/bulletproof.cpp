/* bulletproof.cpp - implementation of Bulletproof-like proofs
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
#include <algorithm>
#include <string>
#include <iostream>
#include <stdexcept>
#include <cassert>

#include "scalar25519.hpp"
#include "point25519.hpp"
#include "constraints.hpp"
#include "pedersen.hpp"
#include "merlin.hpp"
#include "bulletproof.hpp"

namespace DLPROOFS {
using CRV25519::Scalar, CRV25519::Point, Merlin::MerlinBPctx;

#define DEBUGGING
#ifdef DEBUGGING
std::vector<Scalar> dbg_x, dbg_xInv;
Point FF;
#endif

// Flatten a linear statement, writing explicitly the generators and
// public exponents (and optionally the witness) in simple vectors.
FlatLinStmt::FlatLinStmt(const std::string& label,
               const LinConstraint& cnstr, const PtxtVec& xes) {
    // Check that the indexes match, and pack everything in simple
    // arrays that are easier to loop over
    size_t n = cnstr.terms.size();
    size_t n2 = xes.size();
    if (n<1 || n > 1UL<<20) { // size between 1 and 1 million
        throw std::runtime_error("FlatLinStmt: proof size must be between 1 and 2^20");
    }
    if (n2>0 && n2!=n) {
        throw std::runtime_error("FlatLinStmt: unequal size of witness and constraints");
    }
    // Allocate memory
    witness.reserve(n2);
    statement.reserve(n); 
    generators.reserve(n);

    // Record/copy all the points/scalars
    PedersenContext ped(label);
    auto it1 = xes.begin();
    auto it2 = cnstr.terms.begin();
    while (it2 != cnstr.terms.end()) {
        size_t idx = it2->first;
        if (n2>0) {
            if (it1->first != idx)
                throw std::runtime_error("proveLinear: witness and constraint keys not equal");
            witness.push_back(it1->second);
            it1++;
        }
        statement.push_back(it2->second);
        generators.push_back(ped.getG(idx));
        ++it2;
    }
    equalsTo = cnstr.equalsTo;
#ifdef DEBUGGING
    if (n2 > 0) assert(equalsTo ==
                CRV25519::innerProduct(witness.data(), statement.data(), n));
#endif
}

// Flatten a quadratic statement, writing explicitly the generators
// (and optionally the witnesses) in simple vectors.
FlatQuadStmt::FlatQuadStmt(const std::string& label,
        const QuadConstraint& cnstr, const PtxtVec& xes, const PtxtVec& ys) {
    size_t n = cnstr.indexes.size();
    size_t n2 = xes.size();
    if (n<1 || n > 1UL<<20) { // size between 1 and 1 million
        throw std::runtime_error("FlatQuadStmt: proof size must be between 1 and 2^20");
    }
    if (ys.size() != n2 || (n2>0 && n2 != n)) {
        throw std::runtime_error("FlatQuadStmt: witnesses,constraints must bf of unequal size, found "
            +std::to_string(n)+","+std::to_string(n2)+","+std::to_string(ys.size()));
    }
    gs.reserve(n);
    hs.reserve(n);
    PedersenContext ped(label);
    auto it1 = xes.begin();
    auto it2 = ys.begin();
    for (auto idx : cnstr.indexes) { // compute the i'th generators
        gs.push_back(ped.getG(idx));
        hs.push_back(ped.getH(idx));
        if (n2>0) { // witness is provided, store it as well
            if (it1->first != idx || it2->first != idx)
                throw std::runtime_error("FlatQuadStmt: witness and constraint keys not equal");
            wG.push_back(it1->second);
            wH.push_back(it2->second);
            ++it1; ++it2;
        }
    }
    equalsTo = cnstr.equalsTo;
#ifdef DEBUGGING
    if (n2>0)
        assert(equalsTo==CRV25519::innerProduct(wG.data(), wH.data(), n2));
#endif
}

/*******************************************************************/
/******************** Linear proofs/verification *******************/
/*******************************************************************/

// The lower-level prover function. This function modifies in place the lists
// of points and scalars in the FlatLinStmt while generating the proof
void proveLinear(LinPfTranscript& proof, FlatLinStmt& st, MerlinBPctx& mer) {
    size_t n = st.generators.size();
    Scalar* const as = st.witness.data();   // these are the xes   
    Scalar* const bs = st.statement.data(); // these are the constraints
    Point* const gs = st.generators.data(); // these are the generators

    // Compute and push {"C": commitment to the xes}
    Scalar r = CRV25519::randomScalar();
    proof.C = DLPROOFS::commit(gs, as, n, r); // commitment to the xes=as
    mer.processPoint("C", proof.C);

    // Get the generator F
    Point F = mer.newGenerator("F");
#ifdef DEBUGGING
    FF = F;
    Point CC = proof.C + F * st.equalsTo;
    assert( verifyCom(CC, gs, as, n, r, F, st.equalsTo) );
    size_t ii = 0;
    dbg_x.clear();
    dbg_xInv.clear();
#endif

    // Main body of proof, keep halving until n==1
    size_t nOver2 = next2power(n)/2;
    while (n > 1) {
        std::string label = std::to_string(n);

        // Compute L, R
        auto [s,t] = mer.newBlindingFactors(label, n, as);
        proof.Ls.push_back(Point::base()*s + multiExp(gs+nOver2, n-nOver2, as)
                            + F * innerProduct(bs+nOver2, as, n-nOver2));
        proof.Rs.push_back(Point::base()*t + multiExp(gs, n-nOver2, as+nOver2)
                            + F * innerProduct(bs, as+nOver2, n-nOver2));
        Point& L = proof.Ls[proof.Ls.size()-1];
        Point& R = proof.Rs[proof.Rs.size()-1];

        // Compute the challenge x for this level
        mer.processPoint(label+"L", L);
        mer.processPoint("R", R);
        Scalar x = mer.newChallenge("x");

        // Update the first half of the a's, b's, and g's
        Scalar xInv = inverseOf(x);

        for (size_t i=0; i<n-nOver2; i++) {
            as[i] += as[i+nOver2] * xInv;
            bs[i] += bs[i+nOver2] * x;
        }
        foldGenerators(gs, n, x, nOver2);

        // update r
        r += s*x + t*xInv;
        n = nOver2;
        nOver2 /= 2;
#ifdef DEBUGGING
        dbg_x.push_back(x);
        dbg_xInv.push_back(xInv);
        CC += L*x + R*xInv;
        Scalar ab = CRV25519::innerProduct(as, bs, n);
        assert( verifyCom(CC, gs, as, n, r, F, ab) );
#endif
    }

    // base step for n==1

    // final blinding factors and the point S
    auto [s,t] = mer.newBlindingFactors("base", 1, as);
    proof.S = gs[0]*s + F*(s*bs[0]) + Point::base()*t;
    mer.processPoint("S", proof.S);

    // final challenge x
    Scalar x = mer.newChallenge("x");

    // prover sends two scalars a' = s + a0*x, r' = t + r*x
    proof.a = s + as[0]*x;
    proof.r = t + r * x;
#ifdef DEBUGGING
    dbg_x.push_back(x);
    assert( proof.S + CC*x == Point::base()*proof.r + FF*(proof.a*bs[0]) + gs[0]*proof.a );
#endif
}

// The lower-level verifier function. Modifies in place the lists of
// points and scalars in the FlatLinStmt while generating the proof
bool verifyLinear(LinPfTranscript& proof, FlatLinStmt& st, MerlinBPctx& mer) {
    size_t n = st.generators.size();
    size_t original_n = n;
    Scalar* const bs = st.statement.data(); // these are the constraints
    Point* const gs = st.generators.data(); // these are the generators
#ifdef DEBUGGING
    Point gs2[n];
    for (size_t i=0; i<n; i++) gs2[i]=gs[i];
#endif

    // Include the commitment to the witness
    mer.processPoint("C", proof.C);

    // Get the generator F
    Point F = mer.newGenerator("F");
    Point C = proof.C + F*st.equalsTo;
#ifdef DEBUGGING
    Point CC = C;
    assert(FF == F);
#endif

    size_t logN = log2roundUp(n);
    if (proof.Ls.size() != logN || proof.Rs.size() != logN) {
        throw std::runtime_error("verifyLinear: proof must contain log n L's and R's");
    }
    Scalar xes[logN], xInvs[logN]; // hold the x'es and their inverse

    // Main body of proof, keep halving until n==1
    size_t nOver2 = next2power(n)/2;
    size_t ii = 0; // level in the proof
    while (n > 1) {
        std::string label = std::to_string(n);
        Point& L = proof.Ls[ii];
        Point& R = proof.Rs[ii];

        // Get the challenge x for this level
        mer.processPoint(label+"L", L);
        mer.processPoint("R", R);
        Scalar& x = xes[ii] = mer.newChallenge("x");
        Scalar& xInv = xInvs[ii] = inverseOf(x); // xi^{-1}
#ifdef DEBUGGING
        assert(xes[ii] == dbg_x.at(ii));
        assert(xInvs[ii] == dbg_xInv.at(ii));
        CC += L*x + R*xInv;
#endif

        // We will later need to compute the multi-exponentiation
        //    \sum_i Li*xi^{-1} + Ri*xi,
        // so we store the xi's and their inverses in teh challenges
        // array in the order that matches the L's and R's in the proof.

        // Update the first half of the bs
        for (size_t i=0; i<n-nOver2; i++) {
            bs[i] += bs[i+nOver2] * x;
#ifdef DEBUGGING
            gs2[i] += gs2[i+nOver2] * x;
#endif
        }
        n = nOver2;
        nOver2 /= 2;
        ++ii;
    }

    // base step for n==1
    C += multiExp(proof.Ls.data(), proof.Ls.size(), xes)
       + multiExp(proof.Rs.data(), proof.Rs.size(), xInvs);

    expSubsetProduct(gs, original_n, xes);

    // include the point S in the Merlin transcript
    mer.processPoint("S", proof.S);

    // final challenge x
    Scalar x = mer.newChallenge("x");
#ifdef DEBUGGING
    assert(x == dbg_x[dbg_x.size()-1]);
    assert(gs[0]==gs2[0]);
    assert(C==CC);
#endif
    return ( proof.S + C*x == Point::base()*proof.r + F*(proof.a*bs[0]) + gs[0]*proof.a );
}

/*******************************************************************/
/****************** Quadratic proofs/verification ******************/
/*******************************************************************/

// Quadratic proofs: quadratic constraints have the form
//           cnstr = (sum_{i=1}^n x_{j_i} * y_{j_i} = b)
// where b is a public scalar and the x_{ij}'s and y_{ij}'s are the
// witnesses. Returns a NIZK proof of knowledge of scalars that satisfy
// this constraint.
//
// Specificaly it writes to its output a vector V of elements such that:
// + V[0] =r1*base +\sum_i x_{j_i}*G_{j_i} +\sum_i y_{j_i}*H_{j_i} is
//   Pedresen commitment to the x'es y's
// + from cnstr and V[0] anyone can compute
//   - the generator F = hashtoCurve(cnstr,V[0])
//   - commitment C = r*base +b*F +\sum_i x_{j_i}*G_{j_i} +y_{j_i}*H_{j_i}
// + The rest of V is a quadratic Bulletproof, a ZKPOK for r,x_{j_i},y_{j_i}
//   that match the commitment C and satisfy the quadratic constraint.

// The lower-level prover function. This function modifies in place the lists
// of points and scalars in the FlatQuadStmt while generating the proof
void proveQuadratic(QuadPfTranscript& pf, FlatQuadStmt& st, MerlinBPctx& mer)
{
    size_t n = st.gs.size();
    Scalar* const as = st.wG.data(); // the a sitnesses
    Scalar* const bs = st.wH.data(); // the b sitnesses
    Point* const gs = st.gs.data();  // the G generators
    Point* const hs = st.hs.data();  // the H generators

    // Compute and push {"C": commitment to the xes}
    Scalar r = CRV25519::randomScalar();
    pf.C = DLPROOFS::commit2(gs, as, hs, bs, n, r); // commitment to the x'es and y's
    mer.processPoint("C", pf.C);

    // Get the generator F
    Point F = mer.newGenerator("F");
#ifdef DEBUGGING
    FF = F;
    Point CC = pf.C + F * st.equalsTo;
    assert( verifyCom2(CC, gs, as, hs, bs, n, r, F, st.equalsTo) );
    size_t ii = 0;
    dbg_x.clear();
    dbg_xInv.clear();
#endif

    // Main body of proof, keep halving until n==1
    size_t nOver2 = next2power(n)/2;
    while (n > 1) {
        std::string label = std::to_string(n);

        // Compute L, R
        auto [s,t] = mer.newBlindingFactors(label, n, as);
        pf.Ls.push_back(Point::base()*s
            +multiExp(gs+nOver2,n-nOver2,as) +multiExp(hs,n-nOver2,bs+nOver2)
            + F * innerProduct(as, bs+nOver2, n-nOver2)
        );
        pf.Rs.push_back(Point::base()*t
            +multiExp(gs,n-nOver2,as+nOver2) +multiExp(hs+nOver2,n-nOver2,bs)
            + F * innerProduct(as+nOver2, bs, n-nOver2)
        );
        Point& L = pf.Ls[pf.Ls.size()-1];
        Point& R = pf.Rs[pf.Rs.size()-1];

        // Compute the challenge x for this level
        mer.processPoint(label+"L", L);
        mer.processPoint("R", R);
        Scalar x = mer.newChallenge("x");
        Scalar xInv = inverseOf(x);
#ifdef DEBUGGING
        dbg_x.push_back(x);
        dbg_xInv.push_back(xInv);
#endif

        for (size_t i=0; i<n-nOver2; i++) {
            as[i] += as[i+nOver2] * xInv;
            bs[i] += bs[i+nOver2] * x;
        }
        foldGenerators(gs, n, x, nOver2);
        foldGenerators(hs, n, xInv, nOver2);

        // update r
        r += s*x + t*xInv;
        n = nOver2;
        nOver2 /= 2;
#ifdef DEBUGGING
        CC += L*x + R*xInv;
        Scalar ab = CRV25519::innerProduct(as, bs, n);
        assert( verifyCom2(CC, gs, as, hs, bs, n, r, F, ab) );
#endif
    }
    // base step for n==1

    // final blinding factors and the pointr S1,S2
    auto [s,t] = mer.newBlindingFactors("baseST", 1, as, bs);
    auto [u,v] = mer.newBlindingFactors("UV", 0, nullptr,nullptr);

    pf.S1 = Point::base()*u +gs[0]*s +hs[0]*t +F*((as[0]*t)+(bs[0]*s));
    pf.S2 = Point::base()*v +F*(s*t);

    // final challenge x
    mer.processPoint("S1", pf.S1);
    mer.processPoint("S2", pf.S2);
    Scalar x = mer.newChallenge("x");

    // prover sends three scalars a'=a0+sx, b'=b0+tx, r'=r+ux+vx^2
    pf.a = as[0] +s*x;
    pf.b = bs[0] +t*x;
    pf.r = r + (u +v*x)*x;

#ifdef DEBUGGING
    dbg_x.push_back(x);
    assert( CC +(pf.S1 +pf.S2*x)*x ==
            Point::base()*pf.r +gs[0]*pf.a +hs[0]*pf.b +FF*(pf.a*pf.b));
#endif
}

// The lower-level verifier function. This function modifies in place the
// list of points in the FlatQuadStmt while verifying the proof
bool verifyQuadratic(QuadPfTranscript& pf, FlatQuadStmt& st, MerlinBPctx& mer)
{
    size_t n = st.gs.size();
    size_t original_n = n;
    Point* const gs = st.gs.data();
    Point* const hs = st.hs.data();
#ifdef DEBUGGING
    Point gs2[n], hs2[n];
    for (size_t i=0; i<n; i++) { gs2[i]=gs[i]; hs2[i]=hs[i]; }
#endif

    // Include the commitment to the witness
    mer.processPoint("C", pf.C);

    // Get the generator F
    Point F = mer.newGenerator("F");
    Point C = pf.C + F*st.equalsTo;
#ifdef DEBUGGING
    Point CC = C;
    assert(FF == F);
#endif

    size_t logN = log2roundUp(n);
    if (pf.Ls.size() != logN || pf.Rs.size() != logN) {
        throw std::runtime_error("verifyQuadratic: proof must contain log n L's and R's");
    }
    Scalar xes[logN], xInvs[logN]; // hold the x'es and their inverse

    // Main body of proof, keep halving until n==1
    size_t nOver2 = next2power(n)/2;
    size_t ii = 0; // level in the proof
    while (n > 1) {
        std::string label = std::to_string(n);

        // Get the challenge x for this level
        Point& L = pf.Ls[ii];
        Point& R = pf.Rs[ii];
        mer.processPoint(label+"L", L);
        mer.processPoint("R", R);
        Scalar& x = xes[ii] = mer.newChallenge("x");
        Scalar& xInv = xInvs[ii] = inverseOf(x); // xi^{-1}
#ifdef DEBUGGING
        assert(xes[ii] == dbg_x.at(ii));
        assert(xInvs[ii] == dbg_xInv.at(ii));
        CC += L*x + R*xInv;
        foldGenerators(gs2, n, x, nOver2);
        foldGenerators(hs2, n, xInv, nOver2);
#endif
        n = nOver2;
        nOver2 /= 2;
        ++ii;
    }

    // base step for n==1
    C += multiExp(pf.Ls.data(), pf.Ls.size(), xes)
       + multiExp(pf.Rs.data(), pf.Rs.size(), xInvs);

    expSubsetProduct(gs, original_n, xes);
    expSubsetProduct(hs, original_n, xInvs);

    // final challenge x
    mer.processPoint("S1", pf.S1);
    mer.processPoint("S2", pf.S2);
    Scalar x = mer.newChallenge("x");
#ifdef DEBUGGING
    assert(x == dbg_x[dbg_x.size()-1]);
    assert(gs[0]==gs2[0] && hs[0]==hs2[0]);
    assert(C==CC);
#endif
    return (C +(pf.S1 +pf.S2*x)*x ==
            Point::base()*pf.r +gs[0]*pf.a +hs[0]*pf.b +F*(pf.a*pf.b) );
}

#ifdef DEBUGGING
Scalar dbgX, modifiedNorm;
#endif

// Norm proofs are similar to quadratic, but for the case of xs=ys. It gets
// the vector, computes its norm, and convert to a quadratic proos using some
// more challenges from the verifier. Returns the norm-squared and a proof.
std::pair<Scalar,QuadPfTranscript>
proveNormSquared(const std::string& tag, PtxtVec& vec) {
    QuadPfTranscript pf(tag);
    MerlinBPctx mer(tag);  // Make a Merlin state that includes the statement

    // initiate a QuadConstraint object
    QuadConstraint cnstr;
    for (auto& elem: vec) { // elem = {idx:scalar}
        cnstr.indexes.insert(cnstr.indexes.end(), elem.first);
        cnstr.equalsTo += (elem.second * elem.second);
    }
    FlatQuadStmt st(tag, cnstr, vec, vec); // "Faltten" statement and witnesses

    // get a random challenge and use it to modify the quadratic constraints
    mer.processConstraint("normSquared", cnstr);
    const Scalar x = mer.newChallenge("x");
    Scalar x2i = x;

    // set as+=(x,x^2,x^3,...), bs-=(x,x^2,x^3,...), qualsTo-=sum_i x^{2i}
    for (size_t i=0; i<vec.size(); i++) {
        st.wG[i] += x2i;
        st.wH[i] -= x2i;
        st.equalsTo -= (x2i*x2i);
        x2i *= x;
    }
#ifdef DEBUGGING
    dbgX = x;
    modifiedNorm = st.equalsTo;
#endif
    proveQuadratic(pf, st, mer);         // The actual proof
    return std::make_pair(cnstr.equalsTo, pf);
}
bool verifyNormSquared(const std::set<size_t>& indexes,
                       const Scalar& normSq, QuadPfTranscript& pf) {
    MerlinBPctx mer(pf.tag); // Make a Merlin state that includes the statement

    // initiate a QuadConstraint object
    QuadConstraint cnstr{indexes, normSq};
    FlatQuadStmt st(pf.tag, cnstr);   // "Faltten" the statement

    // get a random challenge and use it to modify the quadratic constraints
    mer.processConstraint("normSquared", cnstr);
    Scalar x2 = mer.newChallenge("x");
#ifdef DEBUGGING
    assert(dbgX == x2);
#endif
    x2 *= x2; // x^2
    Scalar xto2i = x2;

    // set st.qualsTo -= sum_i x^{2i}
    for (size_t i=0; i<indexes.size(); i++) {
        st.equalsTo -= xto2i;
        xto2i *= x2;
    }
#ifdef DEBUGGING
    assert(modifiedNorm == st.equalsTo);
#endif
    return verifyQuadratic(pf, st, mer);  // The actual verification
}


// I/O
std::ostream& operator<<(std::ostream& os, const LinPfTranscript& tr) {
    os << tr.tag;
    os << tr.C;
    os << tr.Ls.size();
    for (auto& X: tr.Ls) os << X;
    os << tr.Rs.size();
    for (auto& X: tr.Rs) os << X;
    os << tr.S;
    os << tr.a << tr.r;
    return os;
}
std::istream& operator>>(std::istream& is, LinPfTranscript& tr) {
    size_t n;
    is >> tr.tag;
    is >> tr.C;
    is >> n;
    tr.Ls.resize(n);
    for (auto& X: tr.Ls) is >> X;
    is >> n;
    tr.Rs.resize(n);
    for (auto& X: tr.Rs) is >> X;
    is >> tr.S;
    is >> tr.a >> tr.r;
    return is;
}

std::ostream& operator<<(std::ostream& os, const QuadPfTranscript& tr) {
    os << tr.tag;
    os << tr.C;
    os << tr.Ls.size();
    for (auto& X: tr.Ls) os << X;
    os << tr.Rs.size();
    for (auto& X: tr.Rs) os << X;
    os << tr.S1;
    os << tr.S2;
    os << tr.a;
    os << tr.b;
    os << tr.r;
    return os;
}
std::istream& operator>>(std::istream& is, QuadPfTranscript& tr) {
    size_t n;
    is >> tr.tag;
    is >> tr.C;
    is >> n;
    tr.Ls.resize(n);
    for (auto& X: tr.Ls) is >> X;
    is >> n;
    tr.Rs.resize(n);
    for (auto& X: tr.Rs) is >> X;
    is >> tr.S1;
    is >> tr.S2;
    is >> tr.a;
    is >> tr.b;
    is >> tr.r;
    return is;
}

} // namespace DLPROOFS
