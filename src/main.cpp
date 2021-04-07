/* main.cpp - a "main" file, just a debugging tool
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
 
// This file is just a convenience, a handy tool that lets us run
// small porgrams without having to use the awkward ctest syntax.
#include <random>
#include <chrono> 
using namespace std::chrono; 

#include <NTL/version.h>
#include "regevEnc.hpp"

using namespace REGEVENC;

int main(int, char**) {
    // std::cout << "- Found GMP version "<<__GNU_MP__ <<std::endl;
    std::cout << "- Found NTL version "<<NTL_VERSION <<std::endl;
    // std::cout << "- Found Sodium version "<<SODIUM_VERSION_STRING<<std::endl;

    GlobalKey gpk("testContext", /*k*/10, /*m*/8, /*n*/5);
 
    //auto start = high_resolution_clock::now();
    ALGEBRA::EVector noise1;
    auto [sk1,pk1] = gpk.genKeys(&noise1);
    auto [sk2,pk2] = gpk.genKeys();
    size_t i1 = gpk.addPK(pk1);
    size_t i2 = gpk.addPK(pk2);
    for (size_t i=2; i<gpk.enn; i++) // add many more pk's, to use in encryption
        gpk.addPK(pk2);
    //auto duration = duration_cast<seconds>(high_resolution_clock::now() - start);
    //std::cout <<"Time for "<<gpk.enn<<" keygen: "<<duration.count()<< " seconds" << std::endl;

    // encryption
    ALGEBRA::SVector ptxt(NTL::INIT_SIZE, gpk.enn);
    for (auto& p: ptxt)
        NTL::random(p);

    //start = high_resolution_clock::now();
    ALGEBRA::EVector r, e;
    auto ctxt = gpk.encrypt(ptxt, r, e);
    //duration = duration_cast<seconds>(high_resolution_clock::now() - start);
    //std::cout << "Time for encryption of "
    //    <<gpk.enn<<" ptxts: "<<duration.count()<< " seconds" << std::endl;

    //start = high_resolution_clock::now();
    ALGEBRA::Element decNoise1;
    auto ptxt1 = gpk.decrypt(sk1, i1, ctxt, &decNoise1);
    auto ptxt2 = gpk.decrypt(sk2, i2, ctxt);
    //std::cout << "Time for 2 decryptions: "
    //  << ((duration_cast<milliseconds>(high_resolution_clock::now() - start)).count()/1000.0)
    //  << " seconds" << std::endl;

    if (ptxt1 == ptxt[0] && ptxt2 == ptxt[1]) {
        std::cout << "Yay, decryption succeeded\n";
    } else {
        std::cout << "Boo, decryption failed\n";
    }
    return 0;
}

#if 0
#include <vector>
#include <iostream>
#include "bulletproof.hpp"

int main(int, char**) {
    constexpr size_t pfSize = 13;

    // build a constraint: sum_i ai*bi = b = \sum_bi^2
    DLPROOFS::LinConstraint cnstrL;
    for (size_t i=0; i<pfSize; i++) {
        CRV25519::Scalar& x = cnstrL.terms[i+1].setInteger(i+1);
        cnstrL.equalsTo += x * x;
    }
    DLPROOFS::PtxtVec& xes = cnstrL.terms;
    DLPROOFS::LinPfTranscript pfL = proveLinear("blah", cnstrL, xes);
    std::cout << "linear: "<<verifyLinear(cnstrL, pfL) <<std::endl;

    DLPROOFS::QuadConstraint cnstrQ;
    for (auto& x : xes) {
        cnstrQ.indexes.insert(cnstrQ.indexes.end(), x.first);
        cnstrQ.equalsTo += x.second * x.second;
    }    
    DLPROOFS::PtxtVec& ys = cnstrL.terms;
    DLPROOFS::QuadPfTranscript pfQ = proveQuadratic("blah", cnstrQ, xes, ys);
    std::cout << "quadratic: "<<verifyQuadratic(cnstrQ, pfQ) <<std::endl;

    std::set<size_t> indexes;
    for (auto& elem: xes) // elem = {idx:scalar}
        indexes.insert(indexes.end(), elem.first);

    auto [normSq, prNS] = DLPROOFS::proveNormSquared("blah", xes);
    std::cout << "norm: "<<verifyNormSquared(indexes,normSq,prNS)<<std::endl;

    return 0;
}
#endif
