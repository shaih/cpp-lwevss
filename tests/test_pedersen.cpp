#include <iostream>
#include "pedersen.hpp"
#include "tests.hpp" // define strings LWEVSS_TESTS::passed and LWEVSS_TESTS::failed

using namespace DLPROOFS;
using CRV25519::Scalar, CRV25519::Point;

bool testUtils() {
    if (next2power(0) != 0 || next2power(1) != 1 ||  next2power(2) != 2
        || next2power(3) != 4 || next2power(4) != 4 || next2power(17) != 32
        || next2power(0x7edcba9876543210) != 0x8000000000000000)
        return false;
    //std::cout << "next2power passed\n";

    if (log2roundUp(1) != 0 || log2roundUp(2) != 1 ||  log2roundUp(3) != 2
        || log2roundUp(127) != 7 || log2roundUp(128) != 7 || log2roundUp(129) != 8)
        return false;
    //std::cout << "log2roundUp passed\n";
    return true;
}

bool testMultiExp() {
    constexpr size_t nGs = 5;
    std::vector<Point> Gs(nGs, Point::base()); // a vector of generators
    for (size_t i=0; i<nGs; i++)
        Gs[i] *= Scalar().setInteger(i+1); // G[i] = B*(i+1)
    std::vector<Scalar> exps(nGs);  // a vector of random scalars
    for (auto& x : exps) x.randomize();
    // compute \sum_i G[i] * exps[i];
    Point res = multiExp(Gs.data(), nGs, exps.data());

    // check the result
    Scalar theExp; // compute the overall exponent
    for (size_t i=0; i<nGs; i++)
        theExp += exps[i] * Scalar().setInteger(i+1);
    
    // Check that you got the same result
    return Point::base() * theExp == res;
}

bool testOneExp() {
    constexpr size_t nGs = 5;
    std::vector<Point> Gs(nGs, Point::base()); // a vector of generators
    for (size_t i=0; i<nGs; i++) {
        Gs[i] *= Scalar().setInteger(i+1); // G[i] = B*(i+1)
    }
    Scalar exp = CRV25519::randomScalar();

    // compute G[i] *=  exp
    multiBaseOneExp(Gs.data(), nGs, exp);

    // check the result
    for (size_t i=0; i<nGs; i++) {
        auto theExp = exp * Scalar().setInteger(i+1);
        if (Gs[i] != Point::base() * theExp)
            return false;
    }    
    // Check that you got the same result
    return true;
}

bool testFoldGen() {
    constexpr size_t nGs = 6;
    const size_t nOver2 = next2power(nGs)/2; // =4

    std::vector<Point> Gs(nGs, Point::base()); // a vector of generators
    for (size_t i=0; i<nGs; i++) {
        Gs[i] *= Scalar().setInteger(i+1); // G[i] = B*(i+1)
    }
    Scalar exp = CRV25519::randomScalar();

    foldGenerators(Gs.data(), nGs, exp, nOver2);

    // check the result
    for (size_t i=0; i< nGs-nOver2; i++) {
        auto theExp = Scalar().setInteger(i+1)
                    + exp * Scalar().setInteger(i+1 +nOver2);
        if (Gs[i] != Point::base() * theExp)
            return false;
    }
    for (size_t i = nGs-nOver2; i < nOver2; i++)
        if (Gs[i] != Point::base() * Scalar().setInteger(i+1))
            return false;

    return true;
}

bool testExpSubProd() {
    // Check the result
    std::vector<Scalar> exps(3);  // random scalars (3=log(n) rounded up)
    for (auto& x : exps) x.randomize();
    std::vector<Scalar> prods(8); // to store the subset products
    prods[0] = Scalar().setInteger(1);
    prods[1] = exps[2];
    prods[2] = exps[1];
    prods[3] = exps[1] * exps[2];
    prods[4] = exps[0];
    prods[5] = exps[0] * exps[2];
    prods[6] = exps[0] * exps[1];
    prods[7] = exps[0] * exps[1] * exps[2];

    std::vector<Scalar> prods8(8);
    subsetProduct(prods8.data(), 6, exps.data(), 3, prods[0]);
    for (int i=0; i<6; i++) {
        if (prods8[i] != prods[i])
            return false;
    }
    subsetProduct(prods8.data(), 8, exps.data(), 3, prods[0]);
    for (int i=0; i<8; i++) {
        if (prods8[i] != prods[i])
            return false;
    }

    // check for both length-8 and length-6 vectors
    std::vector<Point> Gs(8, Point::base()); // a vector of generators
    for (size_t i=0; i<Gs.size(); i++) {
        Gs[i] *= Scalar().setInteger(i+1); // G[i] = B*(i+1)
    }

    Point p5 = expSubsetProduct(Gs.data(), 5, exps.data(), prods[0]);
    if (p5 != multiExp(Gs.data(), 5, prods.data()))
        return false;

    Scalar r = CRV25519::randomScalar();
    std::vector<Scalar> offsets(8);
    for (size_t i=0; i<8; i++) offsets[i].setInteger(i);

    Point p6 = expSubsetProduct(Gs.data(), 6, exps.data(), r,
                offsets.data());
    if (p6 != multiExp(Gs.data(),6,prods.data())*r +multiExp(Gs.data(),6,offsets.data()))
        return false;

    Point p8 = expSubsetProduct(Gs.data(), 8, exps.data(), r, offsets.data());
    if (p8 != multiExp(Gs.data(),8,prods.data())*r +multiExp(Gs.data(),8,offsets.data()))
        return false;

    return true;
}
/*
Point commit(const Point* Gs, const Scalar* xes, size_t n, const Scalar& r,
    const Point& F=Point::identity(), const Scalar& alpha=Scalar());
bool verifyCom(const Point& c, const Point* Gs, const Scalar* xes, size_t n,
    const Scalar& r, const Point& F=Point::identity(), const Scalar& alpha=Scalar());
Point commit2(const Point* Gs, const Scalar* xes,
        const Point* Hs, const Scalar* ys, size_t n, const Scalar& r,
        const Point& F=Point::identity(), const Scalar& alpha=Scalar());
bool verifyCom2(const Point& c, const Point* Gs, const Scalar* xes,
        const Point* Hs, const Scalar* ys, size_t n, const Scalar& r,
        const Point& F=Point::identity(), const Scalar& alpha=Scalar());

const Point PedersenContext::getG(int i);
const Point PedersenContext::getH(int i);
*/

int main(int, char**) {
    if (!testUtils() || !testMultiExp() || !testFoldGen())
        std::cout << LWEVSS_TESTS::failed << std::endl;
    else
        std::cout << LWEVSS_TESTS::passed << std::endl;        
}
