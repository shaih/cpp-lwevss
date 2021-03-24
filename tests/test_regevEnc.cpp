#include <iostream>
#include <NTL/ZZ.h>

#include "tests.hpp" // define strings LWEVSS_TESTS::passed and LWEVSS_TESTS::failed
#include "regevEnc.hpp"

using namespace REGEVENC;
using namespace std;

#if 0
// Check that indeed pk = sk * A + noise, and |noise|_{infty} <2^{sigma}
static bool verifyKeyPair(Matrix& crs, Matrix& sk, Matrix& noise, Matrix& pk) {
    if (pk != sk * crs + noise) 
        return false;

    BigInt noiseBound = NTL::to_ZZ(1UL) << REGEVENC::sigma;
    for (size_t i=0; i<noise.NumRows(); i++) for (size_t j=0; j<noise.NumCols(); j++) {
        BigInt ezz = NTL::conv<NTL::ZZ>(noise[i][j]);
        if (2*ezz >= GlobalKey::P()) // map ezz to [-P/2, p/2)
            ezz -= GlobalKey::P();
        if (ezz < 0)    // compute abs(e)
            ezz = -ezz;
        if (ezz >= noiseBound) {
            std::cout << "|noise|_{infty} not bounded by 2^{sigma}";
            return false;
        }
    }
    return true;
}
#endif

static bool test_Regev() {
    GlobalKey gpk("testContext", /*k*/10, /*m*/100, /*n*/5, /*rho*/70);
    Matrix noise1;
    auto [sk1,pk1] = gpk.genKeys(&noise1);
    auto [sk2,pk2] = gpk.genKeys();
    size_t i1 = gpk.addPK(pk1);
    size_t i2 = gpk.addPK(pk2);
    for (size_t i=2; i<gpk.enn; i++) // add many more pk's, to use in encryption
        gpk.addPK(pk2);

    // encryption
    REGEVENC::Vector ptxt(NTL::INIT_SIZE, gpk.enn);
    for (auto& p: ptxt)
        NTL::random(p);

    auto ctxt = gpk.encrypt(ptxt);

    Vector decNoise1;
    auto ptxt1 = gpk.decrypt(sk1, i1, ctxt, &decNoise1);
    auto ptxt2 = gpk.decrypt(sk2, i2, ctxt);

    if (ptxt1 != ptxt[0] || ptxt2 != ptxt[1]) {
        return false;
    }
    return true;
}

int main(int, char**) {
    if (!test_Regev())
        std::cout << LWEVSS_TESTS::failed << std::endl;
    else
        std::cout << LWEVSS_TESTS::passed << std::endl;        
}
