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


#if 0
#include <random>
#include <chrono> 
using namespace std::chrono; 

#include <NTL/version.h>
#include "regevEnc.hpp"

//using namespace REGEVENC;

int main(int, char**) {
    std::cout << "Hello, world!\n";
    // std::cout << "- Found GMP version "<<__GNU_MP__ <<std::endl;
    std::cout << "- Found NTL version "<<NTL_VERSION <<std::endl;
    // std::cout << "- Found Sodium version "<<SODIUM_VERSION_STRING<<std::endl;

    REGEVENC::GlobalKey gpk("testPkey",/*kay*/9450,/*emm*/27339,/*enn*/1024,/*rho*/106);
//    REGEVENC::GlobalKey gpk("testPkey",/*kay*/2,/*emm*/3,/*enn*/2,/*rho*/2);

    // key generation
    auto start = high_resolution_clock::now();
    auto [sk0,noise0,pk0] = gpk.genKeys();
    int i0 = gpk.addPK(pk0);
    auto duration = duration_cast<seconds>(high_resolution_clock::now() - start);
    std::cout << "Time for keygen: "<<duration.count()<< " seconds" << std::endl << std::fflush;

    for (int i=1; i<gpk.enn; i++) // add many more pk's, to use in encryption
        gpk.addPK(pk0);

    // encryption
    REGEVENC::Vector ptxt(NTL::INIT_SIZE, gpk.enn);
    for (auto& p: ptxt)
        NTL::random(p);

    start = high_resolution_clock::now();
    auto ctxt = gpk.encrypt(ptxt);
    duration = duration_cast<seconds>(high_resolution_clock::now() - start);
    std::cout << "Time for encryption of "
        <<gpk.enn<<" ptxts: "<<duration.count()<< " seconds" << std::endl << std::fflush;

    start = high_resolution_clock::now();
    auto [ptxt0, decNoise0] = gpk.decrypt(sk0, i0, ctxt);
    std::cout << "Time for decryption: "
      << ((duration_cast<milliseconds>(high_resolution_clock::now() - start)).count()/1000.0)
      << " seconds" << std::endl;

    if (ptxt0 == ptxt[0]) {
        std::cout << "Yay, decryption succeeded\n";
    } else {
        std::cout << "Boo, decryption failed\n";
    }
    return 0;
}
#endif
