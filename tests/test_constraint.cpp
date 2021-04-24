#include <iostream>
#include <memory>
#include <stdexcept>
#include "constraints.hpp"
#include "tests.hpp" // define strings LWEVSS_TESTS::passed and LWEVSS_TESTS::failed

using namespace DLPROOFS;

static bool test_Constraints()
{
    // merge constraints
    std::vector<LinConstraint> cs(3);
    cs[0].addTerm(1, Scalar().setInteger(1)
    ).addTerm(2, Scalar().setInteger(-2)
    ).addTerm(3, Scalar().setInteger(3));
    cs[0].equalsTo.setInteger(2);

    cs[1].addTerm(2, Scalar().setInteger(1)
    ).addTerm(3, Scalar().setInteger(2)
    ).addTerm(5, Scalar().setInteger(-3));
    cs[1].equalsTo.setInteger(3);

    cs[2].addTerm(3, Scalar().setInteger(1)
    ).addTerm(4, Scalar().setInteger(2)
    ).addTerm(5, Scalar().setInteger(3));
    cs[2].equalsTo.setInteger(1);

    std::vector<Scalar> coefs(3);
    coefs[0].setInteger(1);
    coefs[1].setInteger(2);
    coefs[2].setInteger(3);

    LinConstraint c1, c2;

    c1.merge(cs, coefs);
    // This supposed to yeild {[1->1, 3->10, 4->6, 5->3], 11}

    c2.addTerm(1, Scalar().setInteger(1)
    ).addTerm(4, Scalar().setInteger(6)
    ).addTerm(3, Scalar().setInteger(4)
    ).addTerm(5, Scalar().setInteger(3)
    ).addTerm(3, Scalar().setInteger(6)); // added both 3->4 nad 3->6
    c2.equalsTo.setInteger(11);
    if (c1 != c2)
        return false;
    
    PtxtVec xs{ // satisfying the contraint c1
        {1,Scalar().setInteger(1)},
        {3,Scalar().setInteger(1)},
        {4,Scalar().setInteger(1)},
        {5,Scalar().setInteger(-2)}
    };
    if (!checkConstraint(c1, xs))
        return false;

    PtxtVec ys{ // not satisfying the contraint c1
        {1,Scalar().setInteger(2)},
        {3,Scalar().setInteger(1)},
        {4,Scalar().setInteger(2)},
        {5,Scalar().setInteger(2)}
    };
    if (checkConstraint(c1, ys))
        return false;

    PtxtVec zs{ // index mismatch
        {1,Scalar().setInteger(1)},
        {3,Scalar().setInteger(1)},
        {4,Scalar().setInteger(1)},
        {5,Scalar().setInteger(-2)},
        {6,Scalar().setInteger(-2)}
    };
    if (checkConstraint(c1, zs))
        return false;

    // check also the loose variant
    if (!checkConstraintLoose(c1, zs))
        return false;
    zs.erase(5);
    if (checkConstraintLoose(c1, zs))
        return false;

    QuadConstraint q1;
    q1.addIdx(2).addIdx(3).addIdx(5).addIdx(8);
    bool thrown = false;
    try { // this should throw
        q1.addIdx(3);
    } catch (std::runtime_error e) {
        thrown = true;
    }
    if (!thrown) return false;
    q1.equalsTo.setInteger(660);
    // q1 = {{2, 3, 5, 8}, 660}

    // set c1 = {[2->1, 4->2, 5->3, 6->4, 7->5, 8->6], 8}
    c1.terms.clear();
    c1.addTerm(2, Scalar().setInteger(1)
    ).addTerm(4, Scalar().setInteger(2)
    ).addTerm(5, Scalar().setInteger(3)
    ).addTerm(6, Scalar().setInteger(4)
    ).addTerm(7, Scalar().setInteger(5)
    ).addTerm(8, Scalar().setInteger(7));
    c1.equalsTo.setInteger(8);

    makeAlmostDisjoint(c1, q1, Scalar().setInteger(5));
    // Supposed to remove indexes 2,5,8 from c1, add index 9 (9->1) to both,
    // and set c1.equaltsTo=0, q1.equalsTo=660-5*8=620. So we should have
    // c1 = {[4->2, 6->4, 7->5, 9->1], 0}
    // q1 = {{2, 3, 5, 8, 9}, 620}

    c2.terms.clear();
    c2.addTerm(4, Scalar().setInteger(2)
    ).addTerm(6, Scalar().setInteger(4)
    ).addTerm(7, Scalar().setInteger(5)
    ).addTerm(9, Scalar().setInteger(1));
    c2.equalsTo.setInteger(0);
    if (c1 != c2) {
        std::cout << "c1="; c1.debugPrint();
        return false;
    }
    QuadConstraint q2;
    q2.addIdx(2).addIdx(3).addIdx(5).addIdx(8).addIdx(9);
    q2.equalsTo.setInteger(620);
    if (q1 != q2) {
        std::cout << "q1="; q1.debugPrint();
        return false;
    }

    q1.indexes.clear();
    q1.addIdx(4).addIdx(1).addIdx(3).addIdx(5);
    q1.equalsTo.setInteger(1); // <xs,ys> = <(1,1,1,-2),(2,1,2,2)> = 1

    if (!checkConstraint(q1, xs, ys))
        return false;
    if (checkConstraint(q1, zs, ys))
        return false;
    q1.equalsTo.setInteger(2);
    if (checkConstraint(q1, xs, ys))
        return false;

    // Check also the loose variants
    q1.equalsTo.setInteger(1);
    xs[2] = Scalar().setInteger(2);
    if (!checkConstraintLoose(q1, xs, ys))
        return false;
    ys.erase(1);
    if (checkConstraintLoose(q1, xs, ys))
        return false;

    return true;
}

int main(int, char**) {
    if (!test_Constraints())
        std::cout << LWEVSS_TESTS::failed << std::endl;
    else
        std::cout << LWEVSS_TESTS::passed << std::endl;        
}
