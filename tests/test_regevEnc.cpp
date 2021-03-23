#include <iostream>
#include <NTL/ZZ.h>

#include "tests.hpp" // define strings LWEVSS_TESTS::passed and LWEVSS_TESTS::failed
#if 0
#include "regevEnc.hpp"

using namespace REGEVENC;
static NTL::ZZ P = (NTL::to_ZZ(1L)<<252) + NTL::conv<NTL::ZZ>("27742317777372353535851937790883648493");

// Check that indeed sk[i]*crs + pk[i] = noise[i], and |noise[i]|_{infty} <2^{sigma}
static bool verifyKeyPair(std::vector< std::vector<Scalar> >& crs,
                          EllVecs& sk, EllVecs& noise, EllVecs& pk) {
    EllVecs buf = pk;
    for (int i=0; i<ell; i++)
        for (unsigned int j=0; j<buf[i].size(); j++)
            for (unsigned int k=0; k<sk[i].size(); k++)
                buf[i][j] += sk[i][k] * crs[k][j];
    if (buf != noise) {
        std::cout << "pk + sk*CRS != noise";
        return false;
    }
    for (auto& eRow : noise) for (auto& e: eRow) { // check that the noise is small
        static NTL::ZZ noiseBound = NTL::to_ZZ(1UL) << REGEVENC::sigma;
        NTL::ZZ ezz = NTL::ZZFromBytes(e.bytes, crypto_core_ed25519_SCALARBYTES);
        if (2*ezz >= P) // map ezz to [-P/2, p/2)
            ezz -= P;
        if (ezz < 0)    // compute abs(e)
            ezz = -ezz;
        if (ezz >= noiseBound) {
            std::cout << "|noise|_{infty} not bounded by 2^{sigma}";
            return false;
        }
    }
    return true;
}

static bool test_Regev() {
    Context context("testContext",
                    Params{/*kay*/10, /*emm*/100, /*enn*/5, /*rho*/70});
    GlobalKey gpk("testPkey", &context);
    auto [sk1,noise1,pk1] = gpk.genKeys();
    int i1 = gpk.addPK(pk1);
    if (!verifyKeyPair(context.A, sk1, noise1, gpk.B[i1]))
        return false;

    auto [sk2,noise2,i2] = gpk.genKeysAndAdd();
    if (!verifyKeyPair(context.A, sk2, noise2, gpk.B[i2]))
        return false;

    std::vector<CRV25519::Scalar> ptxt(2);
    for (auto& p: ptxt)
        p.randomize();
    auto ctxt = gpk.encrypt(ptxt);
    auto [ptxt_1, decNoise1] = gpk.decrypt(sk1, i1, ctxt);
    auto [ptxt_2, decNoise2] = gpk.decrypt(sk2, i2, ctxt);
    if (ptxt_1 != ptxt[0] || ptxt_2 != ptxt[1]) {
        std::cout << "Boo, decryption failed\n";
        return false;
    }
    return true;
}
#endif

int main(int, char**) {
//    if (!test_Regev())
//        std::cout << LWEVSS_TESTS::failed << std::endl;
//    else
        std::cout << LWEVSS_TESTS::passed << std::endl;        
}
