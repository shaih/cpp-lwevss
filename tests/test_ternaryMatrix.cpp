#include <sstream>
#include <iostream>
#include "ternaryMatrix.hpp"
#include "tests.hpp" // define strings LWEVSS_TESTS::passed and LWEVSS_TESTS::failed

using namespace ALGEBRA;
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

// Testsing TernaryEMatrix, GF(p^4)
bool basicTests2() {
    // {12,f7,59,f6} = [00 01 00 10   11 11 01 11   01 01 10 01   11 11 01 10]
    // {a3,83,e1,02} = [10 10 00 11   10 00 00 11   11 10 00 01   00 00 00 10]
    // {25,1d,12,78} = [00 10 01 01   00 01 11 01   00 01 00 10   01 11 10 00]
    // {66,9b,c3,92} = [01 10 01 10   10 01 10 11   11 00 00 11   10 01 00 10]
    // The bits that are actually stored should be 
    // {12,04,59,06} = [00 01 00 10   00 00 01 00   01 01 10 01   00 00 01 10]
    // {a0,80,21,02} = [10 10 00 00   10 00 00 00   00 10 00 01   00 00 00 10]
    // {25,11,12,48} = [00 10 01 01   00 01 00 01   00 01 00 10   01 00 10 00]
    // {66,98,00,92} = [01 10 01 10   10 01 10 00   00 00 00 00   10 01 00 10]
    // yealds, e.g., 4-by-4 matrix [-1,0,1,0] [0,1,0,0] [1,-1,1,1][-1,1,0,0]
    //                             [0,0,-1,-1][0,0,0,-1][1,0,-1,0][-1,0,0,0]
    //                             [1,1,-1,0] [1,0,1,0] [-1,0,1,0][0,-1,0,1]
    //                             [-1,1,-1,1][0,-1,1,-1][0,0,0,0][-1,0,1,-1]
    // = [[-1+X^2-X^3 X^2+X^3 1-X-X^2-X^3 -X+X^3]
    //    [X^2  1-X^3  X^2+X^3  -X-X^3]
    //    [1+X-X^2  -1  1-X+X^2  1    ]
    //    [-1-X-X^3  1-X^2  X^3  X^2-X^3]
    //   ]
    unsigned char buf[] = {0x12, 0xf7, 0x59, 0xf6,
                           0xa3, 0x83, 0xe1, 0x02,
                           0x25, 0x1d, 0x12, 0x78,
                           0x66, 0x9b, 0xc3, 0x92};

    TernaryEMatrix M;
    M.setFromBytes(buf,4,4);
    if (M.NumRows()!=4 || M.NumCols()!=4) {
            printf("basicTests2: expected a 4x4 matrix but found %dx%d", (int)M.NumRows(), (int)M.NumCols());
        return false;
    }

    EMatrix expected;
    resize(expected, 4, 4);
    std::stringstream("[16 0 1 16]") >> expected[0][0]; // -1+X^2-X^3
    std::stringstream("[0 0 1 1]")   >> expected[0][1]; // X^2+X^3
    std::stringstream("[1 16 16 16]")>> expected[0][2]; // 1-X-X^2-X^3
    std::stringstream("[0 16 0 1]")  >> expected[0][3]; // -X+X^3

    std::stringstream("[0 0 1]")     >> expected[1][0]; // X^2
    std::stringstream("[1 0 0 16]")  >> expected[1][1]; // 1-X^3
    std::stringstream("[0 0 1 1]")   >> expected[1][2]; // X^2+X^3
    std::stringstream("[0 16 0 16]") >> expected[1][3]; // -X-X^3

    std::stringstream("[1 1 16]") >> expected[2][0]; // 1+X-X^2
    std::stringstream("[16]")     >> expected[2][1]; // -1
    std::stringstream("[1 16 1]") >> expected[2][2]; // 1-X+X^2
    std::stringstream("[1]")      >> expected[2][3]; // 1

    std::stringstream("[16 16 0 16]")>> expected[3][0]; // -1-X-X^3
    std::stringstream("[1 0 16]")    >> expected[3][1]; // 1-X^2
    std::stringstream("[0 0 0 1]")   >> expected[3][2]; // X^3
    std::stringstream("[0 0 1 16]")  >> expected[3][3]; // X^2-X^3
    for (int i=0; i<4; i++) for (int j=0; j<4; j++) {
        if (expected[i][j] != M(i,j)) {
            std::cout << "basicTests2 expected M["<<i<<"]["<<j<<"]="
                <<(expected[i][j])<<"but found "<< M(i,j)<<std::endl;
            return false;
        }
    }
    return true;
}


bool testMatMul() {
    SVector v1, v2;
    SMatrix M;
    TernaryMatrix T1, T2;

    // resize and fill with random entries
    random(v1,5);
    random(v2,6);
    random(M,3,4);
    T1.random(4,5);
    T2.random(6,3);

    // Copy T1,T2 to standard matrices
    SMatrix MT1, MT2;
    resize(MT1, T1.NumRows(), T1.NumCols()); 
    for (auto i=0; i<T1.NumRows(); i++) for (auto j=0; j<T1.NumCols(); j++)
        conv(MT1[i][j], T1[i][j]);

    resize(MT2, T2.NumRows(), T2.NumCols()); 
    for (auto i=0; i<T2.NumRows(); i++) for (auto j=0; j<T2.NumCols(); j++)
        conv(MT2[i][j], T2[i][j]);

    SVector vRes1 = T1 * v1;
    if (vRes1 != MT1 * v1) {
        std::cout << "T1 * v1 failed\n";
        return false;
    }
    SVector vRes2 = v2 * T2;
    if (vRes2 != v2 * MT2) {
        std::cout << "v2 * T2 failed\n";
        return false;
    }
    SMatrix MRes1 = M * T1;
    if (MRes1 != M * MT1) {
        std::cout << "M * T1 failed\n";
        return false;
    }
    SMatrix MRes2 = T2 * M;
    if (MRes2 != MT2 * M) {
        std::cout << "T2 * M failed\n";
        return false;
    }

    return true;
}

// testing matmul with TTernaryEMatrix
bool testMatMul2() {
    EVector v1, v2;
    EMatrix M;
    TernaryEMatrix T1, T2;

    // resize and fill with random entries
    random(v1,5);
    random(v2,6);
    random(M,3,4);
    T1.random(4,5);
    T2.random(6,3);

    // Copy T1,T2 to standard matrices
    EMatrix MT1, MT2;
    resize(MT1, T1.NumRows(), T1.NumCols()); 
    for (auto i=0; i<T1.NumRows(); i++) for (auto j=0; j<T1.NumCols(); j++)
        conv(MT1[i][j], T1[i][j]);

    resize(MT2, T2.NumRows(), T2.NumCols()); 
    for (auto i=0; i<T2.NumRows(); i++) for (auto j=0; j<T2.NumCols(); j++)
        conv(MT2[i][j], T2[i][j]);

    EVector vRes1 = T1 * v1;
    if (vRes1 != MT1 * v1) {
        std::cout << "T1 * v1 failed\n";
        return false;
    }
    EVector vRes2 = v2 * T2;
    if (vRes2 != v2 * MT2) {
        std::cout << "v2 * T2 failed\n";
        return false;
    }
    EMatrix MRes1 = M * T1;
    if (MRes1 != M * MT1) {
        std::cout << "M * T1 failed\n";
        return false;
    }
    EMatrix MRes2 = T2 * M;
    if (MRes2 != MT2 * M) {
        std::cout << "T2 * M failed\n";
        return false;
    }
    return true;
}

int main(int, char**) {
    //NTL::ZZ_p::init((NTL::conv<NTL::ZZ>(1L)<<252)
    //                + NTL::conv<NTL::ZZ>("27742317777372353535851937790883648493"));
    NTL::ZZ_p::init(NTL::conv<NTL::ZZ>(17));
    NTL::ZZ_pX px; // set to X^4 +1
    NTL::SetCoeff(px, 0);
    NTL::SetCoeff(px, 4);
    NTL::ZZ_pE::init(px);
    TernaryEMatrix::init();

    if (!basicTests() || !testMatMul() || !basicTests2() ||!testMatMul2())
        std::cout << LWEVSS_TESTS::failed << std::endl;
    else
        std::cout << LWEVSS_TESTS::passed << std::endl;        
}
