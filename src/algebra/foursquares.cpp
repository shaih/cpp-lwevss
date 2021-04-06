/* foursquares.cpp - Lagraamge four squares theorem
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
#include <iostream>
#include <stdexcept>
#include <cmath>
//#include <climits>
#include <set>
#include <map>
#include <utility>
#include <array>
#include <algorithm>

#include "NTL/ZZ.h"
#include "utils.hpp"
// This implementation is based on Peter Schorn's Python code from
// https://schorn.ch/lagrange.html

namespace ALGEBRA {

// n = 10080 = 2^5 *3^2 *5 *7 is a "magic number", there are exactly 336
// squares mod n. This is the smallest rate of squares for any n < 15840
static constexpr int magicN = 10080;
static std::set<int> computeSquaresModMagic() {
    std::set<int> squares;
    for (int i=0; i<=magicN/2; i++) {
        squares.insert((i*i) % magicN);
    }
    return squares;
}
// This will only be called when the program is first loaded
static std::set<int> squaresModMagic = computeSquaresModMagic();

// If maybeSquare returns false then n is certainly not a square. If it
// returns true then n is likely a square, the fraction of non-suqre n's
// for which it returns true is quite small (3 in a million or so).
static bool maybeSquare(const NTL::ZZ& n) {
	if (n.SinglePrecision()) { // handle small n's
		NTL::ZZ sq = NTL::SqrRoot(n);
		return (sq*sq) == n;
	}
	int residue = n % magicN;
    if (squaresModMagic.find(residue)==squaresModMagic.end())
        return false; // n is not a squae modulo magicN

    // ten small primes, co-prime with the "magic N" above
    for (int p: {11,13,17,19,23,29,31,37,41,43})
        if (NTL::Jacobi(n, NTL::to_ZZ(p))==-1)
            return false;

    return true; // could not demonstrate that n is not a square
}

// returns a square-root of -1 mod p if found, otherwise returns zero.
// Will only be called when p<281.
static int iunit_small(int p) {
    if (p<281 && p&3==1) {
        for (long i=2; i<=p/2; i++)
            if ((i*i) % p == (p-1))
                return i;
    }
    return 0;
}

/* Compute a square root of -1 modulo p if p is a prime and p%4 == 1.
 * If p itself is a square it returns sqrt(p). The boolean return value
 * signifies if p is a square. The ZZ return value is set to zero on
 * failure.
 */
static std::pair<NTL::ZZ,bool> iunit(const NTL::ZZ& p) {
    if (maybeSquare(p)) {
        NTL::ZZ s = NTL::SqrRoot(p);
        if (s*s==p) // p is a square
            return std::make_pair(s, true);
    }
    std::pair<NTL::ZZ,bool> ret(NTL::ZZ::zero(),false);
	if ((p & 7L) == 5L) {
        ret.first = NTL::PowerMod(NTL::to_ZZ(2), p/4, p);
    } else if (p<281) {
        ret.first = NTL::to_ZZ(iunit_small(NTL::conv<int>(p)));
    } else if ((p & 3L) == 1L) {
        NTL::PrimeSeq s; // go over the first 60 primes
        s.reset(2);      // start from 3 rather than 2
        for (long q=s.next(); q<281; q=s.next()) {
			auto qq = NTL::to_ZZ(q);
            if (NTL::Jacobi(qq,p) == -1) {
                ret.first = NTL::PowerMod(qq, (p-1)/4, p);
            }
        }
    }
    return ret;
}

// NTL::NextPrime(n) instead of nextProbablePrime(n), np(n)
// NTL::NumBits(n) instead of floorLog2

// Try to decompose a prime p, p%4==1, into a sum of two squares.
// Returns <0,0> on failure
TwoSqrts decomposeProbablePrime(NTL::ZZ p) {
	if ((p & 3) != 1) {
		throw std::runtime_error("decomposeProbablePrime: must have p=1 mod 4");
	}
    auto [b, issqr] = iunit(p);
	if (issqr) // p is a square, return [0,sqrt(p)]
	    return {NTL::ZZ::zero(), b};

    if (NTL::IsZero(b)) // sqrt(-1) not found
        return {NTL::ZZ::zero(), NTL::ZZ::zero()};

	// Now we have b^2 = -1 mod p, run Cornacchia's algorithm with d=1
	auto a = p;
	while (b * b > p) { // set (a,b) = (b, a % b)
        NTL::ZZ tmp = b;
        b = a % b;
        a = tmp;
    }
	return {b, a % b};
}


// A dictionary of exceptional cases the search in decompose4 cannot handle
typedef std::array<int, 3> ThreeSqrts;
std::map<int,ThreeSqrts> decomposeExceptions = {
    {   2,{ 0,  1,  1}},    {   3,{ 1,  1,  1}},    {  10,{ 0,  1,  3}},
    {  34,{ 3,  3,  4}},    {  58,{ 0,  3,  7}},    {  85,{ 0,  6,  7}},
    { 130,{ 0,  3, 11}},	{ 214,{ 3,  6, 13}},    { 226,{ 8,  9,  9}},
    { 370,{ 8,  9, 15}},	{ 526,{ 6,  7, 21}},    { 706,{15, 15, 16}},
    { 730,{ 0,  1, 27}},	{1414,{ 6, 17, 33}},    {1906,{13, 21, 36}},
    {2986,{21, 32, 39}},	{9634,{56, 57, 57}}
};

static FourSqrts& sortScaled(FourSqrts& list, const NTL::ZZ& v) {
    std::sort(list.begin(), list.end());
    for (auto& x: list) x *= v;
    return list;
}

/* Decompose an integer n>=0 into a sum of up to four squares. Returns a
 * 4-array of integers, [-1,-1,-1,-1] if the search loop fails. Currently
 * there are no known inputs where the search loop fails, but there is
 * no known proof.
 */
FourSqrts decompose4(NTL::ZZ n) {
    if (n<0) {
        throw std::runtime_error("decompose4: must have n>=0");
    }
    if (n <= 1)
        return {NTL::ZZ::zero(),NTL::ZZ::zero(),NTL::ZZ::zero(),n};
    
    // Remove powers of 4 from n and remember them in v
    NTL::ZZ v = NTL::to_ZZ(1);
	while ((n & 3) == 0) {
		n >>= 2; // n = n / 4
		v <<= 1; // v = 2v
    }
	// now original-n = n * v^2

    NTL::ZZ sq = NTL::SqrRoot(n);
    auto p = n - (sq*sq);
    if (NTL::IsZero(p)) { // n is a square, sq=sqrt(n), p=0
        return {p, p, p, sq*v};
    }

	//  a return value that signifies failure
	const FourSqrts failed = {NTL::to_ZZ(-1),NTL::to_ZZ(-1),NTL::to_ZZ(-1),NTL::to_ZZ(-1)};

	FourSqrts ret; // used as scratch space

	if (((n & 3) == 1) && NTL::ProbPrime(n)) { // n is prime, n % 4 = 1
		auto [s, r] = decomposeProbablePrime(n);
        if (!NTL::IsZero(r)) { // r==0 means that n was not a prime
			ret = {NTL::ZZ::zero(), NTL::ZZ::zero(), s, r};
			return sortScaled(ret, v);
		}
    }

	// Recall that we have sq = floor(sqrt(n)) and p = n - sq^2

    NTL::ZZ delta;
	if	((n & 7) == 7) {// Need 4 squares, subtract largest square delta^2
					    // such that (n > delta^2) and (delta^2 % 8 != 0)
        delta = sq;
        n = p;
		if ((sq & 3) == 0) {
			delta -= 1;
			n += (delta<<1) + 1;
        }
		// sq % 4 = 0 -> delta % 8 in [3, 7]
		//	          -> delta^2 % 8 = 1        -> n % 8 = 6
		// sq % 4!= 0 -> delta % 8 in [1, 2, 3, 5, 6, 7]
		//            -> delta^2 % 8 in [1, 4]  -> n % 8 in [3, 6]
		// this implies n % 4 != 0,1,2, so n cannot be a sum of two squares

        sq = NTL::SqrRoot(p);
        p = n - (sq*sq);
		// sq^2 != n since cannot be a sum of two squares
    }

    // At this point we have sq = floor(sqrt(n)) and (n % 8 != 7) and
    // (n % 4 != 0) and moreover the original_n = v^2 * (n + delta^2).
    // This implies that n is a sum of three squares.
    
    // First check whether n is one of the special cases the rest
    // of the algorithm could not handle
	if (n <= 9634) {
	    auto it = decomposeExceptions.find(NTL::conv<int>(n));
    	if (it != decomposeExceptions.end()) {
        	auto [x,y,z] = it->second;
			ret = {delta, NTL::to_ZZ(x), NTL::to_ZZ(y), NTL::to_ZZ(z)};
    	    return sortScaled(ret, v);
    	}
	}
	// Now perform search distinguishing two cases noting that n % 4 != 0

    // Case 1: n % 4 = 3, n = x^2 + 2*p, p % 4 = 1,
	//      if p is prime, p=y^2+z^2, then n=x^2 +(y+z)^2 + (y-z)^2
	if ((n & 3) == 3) {
		if (!NTL::IsOdd(sq)) {
			sq -= 1;           // make sure that sq is odd
			p += (sq<<1) + 1;  // recover n = sq^2 + p
        } // since n, sq are both odd then p must be even
		p >>= 1;
		while (true) {
			if (NTL::ProbPrime(p)) {
				auto [y,z] = decomposeProbablePrime(p);
				if (!NTL::IsZero(z)) {
					// if the above succeeded then n=
					ret = {delta, sq, y+z, NTL::abs(y-z)};
                    return sortScaled(ret, v);
				}
            }
			sq -= 2;			// Next odd sq
			if (sq < 0)			// Should not happen, no known case
				return failed;
			p += (sq<<1) + 2;	// Recover n = sq^2 + 2p
        }
    }

	// Case 2: n % 4 = 1 or n % 4 = 2, n = x^2 + p,
	//      if p prime, p % 4 = 1, p = y^2 + z^2, then n = x^2 + y^2 + z^2
	if (!NTL::IsOdd(n - sq)) { // make sure that n-sq is odd
		sq -= 1;
		p += (sq<<1) + 1;      // recover n = sq^2 + p
    } // in either case n=1,2 (mod 4), p is odd
	while (true) {
		if (NTL::ProbPrime(p)) {
			auto [y,z] = decomposeProbablePrime(p);
			if (!NTL::IsZero(z)) {
				ret = {delta,sq,y,z};
                return sortScaled(ret, v);
			}
        }
        sq -= 2;			// Next sq
		if (sq < 0)			// Should not happen, no known case
			return failed;
		p += (sq + 1)<<2;	// Recover n = sq^2 + p
    }
}
} // end of namespace UTILS
