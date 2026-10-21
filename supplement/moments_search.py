#!/usr/bin/env python3
"""Numerical evidence for open problem 2 (not a proof).

For N in the arguments (default 12 18 24), enumerates every maximal primitive subset A
of {2,...,N} and compares E min(Z_A^k, c^k) = int_0^c k u^{k-1} P_A(u) du with the
primes, in 40-digit arithmetic (mpmath), for k in {5/2, 3, 7/2, 4, 17/4, 9/2, 5, 6, 8,
12, 20} and c in {1/2, 9/10, 19/20, 99/100, 1}. Maximal antichains suffice: adding an
element lowers P_A pointwise. Requires mpmath.

usage: python3 moments_search.py [N ...]
"""
import sys
from fractions import Fraction as F
from mpmath import mp, mpf, findroot, quad, exp, log
mp.dps = 40
def polymul(a,b):
    r=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b): r[i+j]+=x*y
    return r
def PA(A):
    r=[1]
    for n in A:
        q=[0]*(n+1); q[0]=1; q[n]=-1; r=polymul(r,q)
    return r
def mom(poly,k,c):
    k=mpf(k); c=mpf(c)
    return sum(cf*k*c**(m+k)/(m+k) for m,cf in enumerate(poly) if cf)
def maximal_antichains(N):
    nums=list(range(2,N+1)); out=[]
    def comp(a,b): return a%b==0 or b%a==0
    def rec(i,chosen):
        if i==len(nums):
            # maximal?
            if all(any(comp(n,a) for a in chosen) for n in nums if n not in chosen):
                out.append(tuple(chosen))
            return
        n=nums[i]
        if all(not comp(n,a) for a in chosen):
            rec(i+1,chosen+[n])
        # skip n only if it could still be blocked later or already blocked
        rec(i+1,chosen)
    rec(0,[]); return out
ks=[F(5,2),3,F(7,2),4,F(17,4),F(9,2),5,6,8,12,20]
cs=[F(1),F(99,100),F(95,100),F(9,10),F(1,2)]
for N in [int(a) for a in sys.argv[1:]] or [12, 18, 24]:
    ACs=maximal_antichains(N)
    primes=tuple(p for p in range(2,N+1) if all(p%q for q in range(2,p)))
    polys={A:PA(A) for A in ACs}
    print(f"N={N}: {len(ACs)} maximal antichains")
    for k in ks:
        worst=None
        for c in cs:
            base=mom(polys[primes],k,c)
            for A in ACs:
                if A==primes: continue
                d=mom(polys[A],k,c)-base
                if worst is None or d<worst[0]: worst=(d,A,c)
        flag="PRIMES WIN" if worst[0]>0 else "COUNTEREXAMPLE"
        print(f"  k={float(k):6.3f}: min over A≠P of (F_A - F_P) = {float(worst[0]):+.3e} at c={float(worst[2])}, A={worst[1]}  {flag}")
