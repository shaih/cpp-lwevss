#include <iostream>
#include "ternaryMatrix.hpp"
#include "tests.hpp" // define strings LWEVSS_TESTS::passed and LWEVSS_TESTS::failed

using namespace REGEVENC;
bool basicTests() {
    // {12,f7,59,f6} = [00 01 00 10   11 11 01 11   01 01 10 01   11 11 01 10]
    // The bits that are actually stored should be 
    // {12,04,59,06} = [00 01 00 10   00 00 01 00   01 01 10 01   00 00 01 10]
    // yealds, e.g., 4-by-4 matrix [-1,0,1,0][0,1,0,0][1,-1,1,1][-1,1,0,0]
    //          or a 2-by-5 matrix [0,1,0,-1,0][1,1,-1,1,-1]
    unsigned char buf[] = {0x12, 0xf7, 0x59, 0xf6};
    unsigned char rep[] = {0x12, 0x04, 0x59, 0x06};
    int res1[4][4] = {{-1,0,1,0},{0,1,0,0},{1,-1,1,1},{-1,1,0,0}};
    int res2[2][5] = {{-1,0,1,0,0},{1,-1,1,1,-1}};
    TernaryMatrix M;
    M.setFromBytes(buf,4,4);
    // check internal storage
    for (size_t i=0; i<4; i++) {
        if (M.rows[i].rep[0] != rep[i]) {
            printf("M[4,4], input byte %x, expected %x but found %x\n",
                    buf[i], rep[i], M.rows[i].rep[0]);
            return false;
        }
    }
    // check matrix content
    if (M.NumRows()!=4 || M.NumCols()!=4) {
        printf("expected 4x4 matrix but found %dx%d", (int)M.NumRows(), (int)M.NumCols());
        return false;
    }
    for (int i=0; i<4; i++) for (int j=0; j<4; j++)
        if (M[i][j] != res1[i][j]) {
            printf("M[4,4], expected M[%d][%d]=%x but found %x\n",
                    i, j, res1[i][j], M[i][j]);
            return false;
        }

    resize(M,2,5);
    M.setFromBytes(buf);
    // check internal storage
    for (size_t i=0; i<2; i++) for (size_t j=0; j<2; j++) {
        if (M.rows[i].rep[j] != rep[2*i +j]) {
            printf("M[2,5], input byte %x, expected %x but found %x\n",
                    buf[i], rep[i], M.rows[i].rep[0]);
            return false;
        }
    }
    // check matrix content
    if (M.NumRows()!=2 || M.NumCols()!=5) {
        printf("expected 2x5 matrix but found %dx%d", (int)M.NumRows(), (int)M.NumCols());
        return false;
    }
    for (int i=0; i<2; i++) for (int j=0; j<5; j++)
        if (M[i][j] != res2[i][j]) {
            printf("M[2,5], expected M[%d][%d]=%x but found %x\n",
                    i, j, res1[i][j], M[i][j]);
            return false;
        }

    bool thrown = false;
    try { // this should throw
        auto i = M.at(0).at(5);
    } catch (std::out_of_range e) {
        thrown = true;
    //    std::cout << e.what() << std::endl;
    }
    if (!thrown) return false;
    thrown = false;
    try { // this should throw
        auto i = M.at(2).at(0);
    } catch (std::out_of_range e) {
        thrown = true;
    //    std::cout << e.what() << std::endl;
    }
    if (!thrown) return false;
    return true;
}


bool testMatMul() {
    Vector v1, v2;
    Matrix M;
    TernaryMatrix T1, T2;

    // resize and fill with random entries
    random(v1,5);
    random(v2,6);
    random(M,3,4);
    T1.random(4,5);
    T2.random(6,3);

    // Copy T1,T2 to standard matrices
    Matrix MT1, MT2;
    resize(MT1, T1.NumRows(), T1.NumCols()); 
    for (auto i=0; i<T1.NumRows(); i++) for (auto j=0; j<T1.NumCols(); j++)
        conv(MT1[i][j], T1[i][j]);

    resize(MT2, T2.NumRows(), T2.NumCols()); 
    for (auto i=0; i<T2.NumRows(); i++) for (auto j=0; j<T2.NumCols(); j++)
        conv(MT2[i][j], T2[i][j]);

    Vector vRes1 = T1 * v1;
    if (vRes1 != MT1 * v1) {
        std::cout << "T1 * v1 failed\n";
        return false;
    }
    Vector vRes2 = v2 * T2;
    if (vRes2 != v2 * MT2) {
        std::cout << "v2 * T2 failed\n";
        return false;
    }
    Matrix MRes1 = M * T1;
    if (MRes1 != M * MT1) {
        std::cout << "M * T1 failed\n";
        return false;
    }
    Matrix MRes2 = T2 * M;
    if (MRes2 != MT2 * M) {
        std::cout << "T2 * M failed\n";
        return false;
    }

    return true;
}


int main(int, char**) {
    NTL::ZZ_p::init((NTL::conv<NTL::ZZ>(1L)<<252)
                    + NTL::conv<NTL::ZZ>("27742317777372353535851937790883648493"));
    // NTL::ZZ_p::init(NTL::conv<NTL::ZZ>(17));
    if (!basicTests() || !testMatMul())
        std::cout << LWEVSS_TESTS::failed << std::endl;
    else
        std::cout << LWEVSS_TESTS::passed << std::endl;        
}
