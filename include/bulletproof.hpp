#ifndef _BOOLETPROOF_HPP_
#define _BOOLETPROOF_HPP_
/* bulletproof.hpp - implementation of Bulletproof-like proofs
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
#include <vector>

#include "scalar25519.hpp"
#include "point25519.hpp"
#include "constraints.hpp"
#include "pedersen.hpp"
#include "merlin.hpp"

namespace DLPROOFS {
using CRV25519::Scalar, CRV25519::Point, Merlin::MerlinBPctx;

// Linear proofs: input are constraint cnstr=(sum_{i=1}^n a_{j_i}*X_{j_i}=b),
// and scalars xes = ( x_{j_i} ) that satisfy it, namely
//             sum_{i=1}^n a_{j_i} * x_{j_i} = b.
// Returns a NIZK proof of knowledge of scalars that satisfy this constraint.
//
// Specificaly it writes to its output a vector V of elements such that:
// + V[0] = r*base + \sum_i x_{j_i}*G_{j_i} is Pedresen commitment to the x'es
// + from cnstr and V[0] anyone can compute
//   - the generator F = hashtoCurve(cnstr,V[0])
//   - a modified commitment C = r*base + b*F + \sum_i x_{j_i}*G_{j_i}
// + The rest of V is a linear Bulletproof, a ZKPOK for (r and) x_{j_i}'s
//   that match the commitment C and satisfy the linear constraint.

// "Flatten" the representation of the statement (+optional witness),
// replacing the maps and structures with just three vectors, one for
// the constraints, one for the generators, and an optional one for
// the witness.
struct FlatLinStmt {
    std::vector<Point> generators;
    std::vector<Scalar> statement;
    Scalar equalsTo;
    std::vector<Scalar> witness;

    FlatLinStmt() = default;
    FlatLinStmt(const PedersenContext& ped,
                const LinConstraint& cnstr, const PtxtVec& xes=PtxtVec());
};

// The transcript of a linear bulletproof-like proof
struct LinPfTranscript {
    std::string tag;
    Point C;      // commitment to witness
    std::vector<Point> Ls,Rs; // holds the L's and R's
    Point S;      // the last proof element
    Scalar a, r;  // the last two scalars

    explicit LinPfTranscript(const std::string& t): tag(t) {}
};

// The lower-level routines. These functions modify in place the lists
// of points and scalars in the FlatLinStmt while processing the proof
void proveLinear(LinPfTranscript& proof, Scalar r, MerlinBPctx& mer,
        Scalar* const as, Scalar* const bs, Point* const gs, size_t n);
bool verifyLinear(LinPfTranscript& pf, FlatLinStmt& st,
                  MerlinBPctx& m, Scalar* wOffsets=nullptr);
    // If the optional wOffsets is specified, then proof.C is a
    // commitment to witness+wOffset rather than to the witness itself.

inline LinPfTranscript proveLinear(const std::string& tag, 
                    const LinConstraint& cnstr, const PtxtVec& xes) {
    LinPfTranscript proof(tag);
    MerlinBPctx mer(tag);  // Make a Merlin state that includes the statement
    PedersenContext ped(tag);
    mer.processConstraint("constraint", cnstr); 

    FlatLinStmt st(ped, cnstr, xes); // "Faltten" the statement and witness
 
    // Compute and push {"C": commitment to the xes}
    Scalar r = CRV25519::randomScalar();
    proof.C = DLPROOFS::commit(st.generators.data(), st.witness.data(), st.generators.size(), r); // commitment to the xes=as

    size_t n = st.generators.size();
    Scalar* const as = st.witness.data();   // these are the xes   
    Scalar* const bs = st.statement.data(); // these are the constraints
    Point* const gs = st.generators.data(); // these are the generators

    proveLinear(proof, r, mer, as, bs, gs, n); // The actual proof
    return proof;
}

inline bool verifyLinear(const LinConstraint& cnstr, LinPfTranscript& proof) {
    MerlinBPctx mer(proof.tag); // Make a Merlin state that includes the statement
    PedersenContext ped(proof.tag);
    mer.processConstraint("constraint", cnstr); 

    FlatLinStmt st(ped, cnstr);   // "Faltten" the statement
    return verifyLinear(proof, st, mer);  // The actual verification
}

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

// "Flatten" the representation of the statement (+optional witness),
// replacing the maps and structures with simple vectors.
struct FlatQuadStmt {
    std::vector<Point> gs, hs;
    Scalar equalsTo;
    std::vector<Scalar> wG, wH;

    FlatQuadStmt() = default;
    FlatQuadStmt(const PedersenContext& ped, const QuadConstraint& cnstr,
            const PtxtVec& xes=PtxtVec(), const PtxtVec& ys=PtxtVec());
};
// The transcript of a quadratic bulletproof-like proof
struct QuadPfTranscript {
    std::string tag;
    Point C ;        // commitments to witnesses
    std::vector<Point> Ls,Rs; // holds the L's and R's
    Point S1,S2;     // the last proof elements
    Scalar a, b, r;  // the last three scalars

    explicit QuadPfTranscript(const std::string& t): tag(t) {}
};

// The lower-level routines. These functions modify in place the lists
// of points and scalars in the FlatQuadStmt while processing the proof
void proveQuadratic(QuadPfTranscript& pf, Scalar r, MerlinBPctx& m, 
                    Point* gs, Scalar* as, Point* hs, Scalar* bs, size_t n);
bool verifyQuadratic(QuadPfTranscript& pf, FlatQuadStmt& st, MerlinBPctx& m,
                     Scalar* uOffsets=nullptr, Scalar* vOffsets=nullptr);
    // If the optional uOffsets, vOffsets are specified, then proof.C is
    // a commitment to u+uOffset, v+vOffset rather than to u,v themselves.

inline QuadPfTranscript proveQuadratic(const std::string& tag,
        const QuadConstraint& cnstr, const PtxtVec& xs, const PtxtVec& ys) {
    QuadPfTranscript pf(tag);
    MerlinBPctx mer(tag);  // Make a Merlin state that includes the statement
    PedersenContext ped(tag);
    mer.processConstraint("constraint", cnstr); 
    FlatQuadStmt st(ped, cnstr, xs, ys); // "Faltten" statement and witnesses

    size_t n = st.gs.size();
    Scalar* const as = st.wG.data(); // the a witnesses
    Scalar* const bs = st.wH.data(); // the b witnesses
    Point* const gs = st.gs.data();  // the G generators
    Point* const hs = st.hs.data();  // the H generators

    // Compute and push {"C": commitment to the xes}
    Scalar r = CRV25519::randomScalar();
    pf.C = DLPROOFS::commit2(gs, as, hs, bs, n, r); // commitment to the x'es and y's

    proveQuadratic(pf, r, mer, gs, as, hs, bs, n);  // The actual proof
    return pf;
}

inline bool verifyQuadratic(const QuadConstraint& cnstr, QuadPfTranscript& pf) {
    MerlinBPctx mer(pf.tag); // Make a Merlin state that includes the statement
    mer.processConstraint("constraint", cnstr);
    PedersenContext ped(pf.tag);
    FlatQuadStmt st(ped, cnstr);   // "Faltten" the statement
    return verifyQuadratic(pf, st, mer);  // The actual verification
}

// Norm proofs are similar to quadratic, but for the case of xs=ys. It gets
// the vector, computes its norm, and convert to a quadratic proos using some
// more challenges from the verifier. Returns the norm-squared and a proof.
Scalar proveNormSquared(QuadPfTranscript& pf, MerlinBPctx& mer, PtxtVec& vec);
bool verifyNormSquared(const std::set<size_t>& indexes,
                       const Scalar& normS, QuadPfTranscript& pf);

// I/O
std::ostream& operator<<(std::ostream& os, const LinPfTranscript& tr);
std::istream& operator>>(std::istream& is, LinPfTranscript& tr);

} // namespace DLPROOFS
#endif // ifndef _BOOLETPROOF_HPP_
