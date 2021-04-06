#include <iostream>
#include "utils.hpp"
#include "tests.hpp" // define strings LWEVSS_TESTS::passed and LWEVSS_TESTS::failed

using namespace ALGEBRA;

bool test_decomposeProbablePrime()
{
	auto v = decomposeProbablePrime(NTL::to_ZZ(37)); // 37-1 is a square
	if ((sqr(v[0]) + sqr(v[1])) != 37)
		return false;

	v = decomposeProbablePrime(NTL::to_ZZ(12049)); // 12049-1 is not a square
	if ((sqr(v[0]) + sqr(v[1])) != 12049)
		return false;

	// a ~350-bit prime
	NTL::ZZ big = NTL::conv<NTL::ZZ>("24684249032065892333066123534168930441269525239006410135714283699648991959894332868446109170827166448301044689");

	v = decomposeProbablePrime(big);
	if ((sqr(v[0]) + sqr(v[1])) != big)
		return false;
	
	bool thrown = false;
	try {
		v = decomposeProbablePrime(NTL::to_ZZ(11)); // =3 mod 4
	} catch (std::runtime_error e) {
		// std::cout << e.what() << std::endl;
		thrown = true;
	}
	return thrown;
}

bool test_decompose4()
{
	auto v = decompose4(NTL::to_ZZ(100)); // 100 is a square
	if ((sqr(v[0])+sqr(v[1])+sqr(v[2])+sqr(v[3])) != 100)
		return false;

	v = decompose4(NTL::to_ZZ(11002)); // not a square, =2 mod 4
	if ((sqr(v[0])+sqr(v[1])+sqr(v[2])+sqr(v[3])) != 11002)
		return false;

	v = decompose4(NTL::to_ZZ(37)); // 37 is a prime, =1 mod 4
	if ((sqr(v[0])+sqr(v[1])+sqr(v[2])+sqr(v[3])) != 37)
		return false;

	// 2986*64 = 191,104 is an exception case
	v = decompose4(NTL::to_ZZ(191104));
	if ((sqr(v[0])+sqr(v[1])+sqr(v[2])+sqr(v[3])) != 191104)
		return false;

	// try twenty random large numbers
	for (int i=0; i<20; i++) {
		NTL::ZZ n = NTL::RandomBits_ZZ(200);
		v = decompose4(n);
		if ((sqr(v[0])+sqr(v[1])+sqr(v[2])+sqr(v[3])) != n)
			return false;
	}
	return true;
}

int main(int, char**) {
    if (test_decomposeProbablePrime() && test_decompose4())
        std::cout << LWEVSS_TESTS::passed << std::endl;
    else
        std::cout << LWEVSS_TESTS::failed << std::endl;
	return 0;
}


#if 0
# 'l' is a list of tuples where the first elements form the argument to 'func'
# and the last element is the expected result. Returns True iff all tests
# succeed.
def	testfunc(func, l):
	return False not in [func(*x[:-1]) == x[-1] for x in l]

# Test the gcd function
# Returns True if no error has been detected
def	testgcd():
	return testfunc(gcd, [(4, 6, 2), (6, 4, 2),
		(1, 1, 1), (2, 1, 1), (1, 2, 1), (13000, 17000, 1000), (3, 4, 1)])

# Test the jacobi function by comparing with a pre-computed table
# Returns True if no error has been detected
def	testjacobi():
	return testfunc(jacobi, [
		(1, 1, 1), (1, 3, 1), (1, 5, 1), (1, 7, 1), (1, 9, 1), (1, 11, 1),
		(1, 13, 1), (1, 15, 1), (1, 17, 1), (1, 19, 1), (1, 21, 1), (1, 23,
		1), (1, 25, 1), (1, 27, 1), (1, 29, 1), (1, 31, 1), (2, 1, 1), (2, 3,
		-1), (2, 5, -1), (2, 7, 1), (2, 9, 1), (2, 11, -1), (2, 13, -1), (2,
		15, 1), (2, 17, 1), (2, 19, -1), (2, 21, -1), (2, 23, 1), (2, 25, 1),
		(2, 27, -1), (2, 29, -1), (2, 31, 1), (3, 1, 1), (3, 3, 0), (3, 5,
		-1), (3, 7, -1), (3, 9, 0), (3, 11, 1), (3, 13, 1), (3, 15, 0), (3,
		17, -1), (3, 19, -1), (3, 21, 0), (3, 23, 1), (3, 25, 1), (3, 27, 0),
		(3, 29, -1), (3, 31, -1), (4, 1, 1), (4, 3, 1), (4, 5, 1), (4, 7, 1),
		(4, 9, 1), (4, 11, 1), (4, 13, 1), (4, 15, 1), (4, 17, 1), (4, 19, 1),
		(4, 21, 1), (4, 23, 1), (4, 25, 1), (4, 27, 1), (4, 29, 1), (4, 31,
		1), (5, 1, 1), (5, 3, -1), (5, 5, 0), (5, 7, -1), (5, 9, 1), (5, 11,
		1), (5, 13, -1), (5, 15, 0), (5, 17, -1), (5, 19, 1), (5, 21, 1), (5,
		23, -1), (5, 25, 0), (5, 27, -1), (5, 29, 1), (5, 31, 1), (6, 1, 1),
		(6, 3, 0), (6, 5, 1), (6, 7, -1), (6, 9, 0), (6, 11, -1), (6, 13, -1),
		(6, 15, 0), (6, 17, -1), (6, 19, 1), (6, 21, 0), (6, 23, 1), (6, 25,
		1), (6, 27, 0), (6, 29, 1), (6, 31, -1), (7, 1, 1), (7, 3, 1), (7, 5,
		-1), (7, 7, 0), (7, 9, 1), (7, 11, -1), (7, 13, -1), (7, 15, -1), (7,
		17, -1), (7, 19, 1), (7, 21, 0), (7, 23, -1), (7, 25, 1), (7, 27, 1),
		(7, 29, 1), (7, 31, 1), (8, 1, 1), (8, 3, -1), (8, 5, -1), (8, 7, 1),
		(8, 9, 1), (8, 11, -1), (8, 13, -1), (8, 15, 1), (8, 17, 1), (8, 19,
		-1), (8, 21, -1), (8, 23, 1), (8, 25, 1), (8, 27, -1), (8, 29, -1),
		(8, 31, 1), (9, 1, 1), (9, 3, 0), (9, 5, 1), (9, 7, 1), (9, 9, 0), (9,
		11, 1), (9, 13, 1), (9, 15, 0), (9, 17, 1), (9, 19, 1), (9, 21, 0),
		(9, 23, 1), (9, 25, 1), (9, 27, 0), (9, 29, 1), (9, 31, 1), (10, 1,
		1), (10, 3, 1), (10, 5, 0), (10, 7, -1), (10, 9, 1), (10, 11, -1),
		(10, 13, 1), (10, 15, 0), (10, 17, -1), (10, 19, -1), (10, 21, -1),
		(10, 23, -1), (10, 25, 0), (10, 27, 1), (10, 29, -1), (10, 31, 1),
		(11, 1, 1), (11, 3, -1), (11, 5, 1), (11, 7, 1), (11, 9, 1), (11, 11,
		0), (11, 13, -1), (11, 15, -1), (11, 17, -1), (11, 19, 1), (11, 21,
		-1), (11, 23, -1), (11, 25, 1), (11, 27, -1), (11, 29, -1), (11, 31,
		-1), (12, 1, 1), (12, 3, 0), (12, 5, -1), (12, 7, -1), (12, 9, 0),
		(12, 11, 1), (12, 13, 1), (12, 15, 0), (12, 17, -1), (12, 19, -1),
		(12, 21, 0), (12, 23, 1), (12, 25, 1), (12, 27, 0), (12, 29, -1), (12,
		31, -1), (13, 1, 1), (13, 3, 1), (13, 5, -1), (13, 7, -1), (13, 9, 1),
		(13, 11, -1), (13, 13, 0), (13, 15, -1), (13, 17, 1), (13, 19, -1),
		(13, 21, -1), (13, 23, 1), (13, 25, 1), (13, 27, 1), (13, 29, 1), (13,
		31, -1), (14, 1, 1), (14, 3, -1), (14, 5, 1), (14, 7, 0), (14, 9, 1),
		(14, 11, 1), (14, 13, 1), (14, 15, -1), (14, 17, -1), (14, 19, -1),
		(14, 21, 0), (14, 23, -1), (14, 25, 1), (14, 27, -1), (14, 29, -1),
		(14, 31, 1), (15, 1, 1), (15, 3, 0), (15, 5, 0), (15, 7, 1), (15, 9,
		0), (15, 11, 1), (15, 13, -1), (15, 15, 0), (15, 17, 1), (15, 19, -1),
		(15, 21, 0), (15, 23, -1), (15, 25, 0), (15, 27, 0), (15, 29, -1),
		(15, 31, -1)])

# Test the probable prime detector 'func' on all odd numbers between
# n and upperN. Return False iff there is a case where a prime number
# is erroneously flagged as composite.
def	testisProbablePrimeFunc(func, n, upperN):
	if	n & 1 == 0:
		n += 1						# Make sure that n is odd
	while n <= upperN:
		if	func(n) < isPrime(n):	# Error if composite was prime after all
			return False
		n += 2						# Next odd
	return True

def	testdp():
	return testfunc(dp, [(100, 4, 1, 101), (101, 4, 1, 101), (100, 6, 4, 101),
		(101, 6, 4, 101)])

def	testisnpk():
	return testfunc(isnpk, [(4, 13, True), (2, 5003, True), (4, 5003, False),
		(2, (1 << 31) - 1, False), (46, (1 << 31) - 1, True), (32, 3, True),
		(20, 5, True), (22, 5, False)])

# Test the iunit function for arguments between p and upperP making sure
# that the argument is a (probable) prime congruent 1 modulo 4
# Returns True if no error has been detected
def	testiunit(p, upperP):
	p = ((p >> 2) << 2) + 1	# Make sure that p % 4 = 1
	upperP = min(upperP, 42799)	# and that upperP does not exceed range where
	while p <= upperP:			# isProbablePrime works correctly.
		if	isProbablePrime(p):
			if	(iunit(p)[0] ** 2 + 1) % p:	# This is the check
				return False
		p += 4					# maintain invariant p % 4 = 1
	return True

# Perform n tests starting at the smallest prime p >= start with p % 4 = 1
def	testdecomposeProbablePrime(start, n):
	p = ((start >> 2) << 2) + 1
	if	p < start:
		p += 4
	while n:
		while not isProbablePrime(p):
			p += 4
		a, b, c = decomposeProbablePrime(p)
		if	c and (a * a + b * b != p):
			return False
		n -= 1
		p += 4
	return True

#endif
