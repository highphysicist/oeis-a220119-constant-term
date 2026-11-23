#!/usr/bin/env python3
"""Exact finite checks accompanying the all-n algebraic proof.

This script uses only Python's standard library. Tests are supporting evidence;
the universal claim is proved in A220119_proof.md / A220119_proof.tex.
"""
from math import comb
from collections import defaultdict
import argparse
import json
import time

def C(n,k):
    return comb(n,k) if n >= 0 and 0 <= k <= n else 0

def F(n,k):
    return C(n,k)**2*C(n+k,n)

def double_sum(n):
    f=[F(n,k) for k in range(n+1)]
    return sum(f[j]*f[k]*C(j+k,n) for j in range(n+1) for k in range(n+1))

def direct_constant_term(n):
    """Expand the SIX LINEAR FACTORS, with independent 5-variable arithmetic.

    All numerator exponents are nonnegative, so terms already exceeding n in
    any coordinate cannot contribute to [a^n b^n c^n d^n e^n]. Remaining-degree
    pruning likewise discards only terms that cannot reach this target.
    """
    factors=[(2,), (2,3), (0,), (0,2,3,4), (0,1), (0,1,2,3,4)]
    steps=[f for f in factors for _ in range(n)]
    remaining=[sum(v in f for f in steps) for v in range(5)]
    poly={(0,0,0,0,0):1}
    for variables in steps:
        for v in variables:
            remaining[v]-=1
        new=defaultdict(int)
        for exponent,coefficient in poly.items():
            if all(exponent[v]+remaining[v]>=n for v in range(5)):
                new[exponent]+=coefficient
            for v in variables:
                if exponent[v]>=n:
                    continue
                e=list(exponent);e[v]+=1;e=tuple(e)
                if all(e[i]+remaining[i]>=n for i in range(5)):
                    new[e]+=coefficient
        poly=new
    return poly.get((n,n,n,n,n),0)

def check_identities(bound):
    counts=dict(legendre_coefficients=0,outer_weights=0,
                factorial_bridges=0,auxiliary_identities=0,final_convolutions=0)
    for n in range(bound+1):
        for ell in range(n+1):
            # Coefficients of L_n(x)=sum C(n,r)^2*x^r*(1+x)^(n-r).
            assert sum(C(n,r)**2*C(n-r,ell-r) for r in range(ell+1)) == C(n,ell)*C(n+ell,n)
            counts['legendre_coefficients']+=1
            # Eliminate e and b from the Laurent numerator.
            assert C(n,ell)*sum(C(n,i)**2*C(i,n-ell) for i in range(n+1)) == F(n,ell)
            counts['outer_weights']+=1
            # H is computed by a different coefficient expansion in c+d.
            H=sum(C(n,r)*C(n,ell-r)*C(n+r,n) for r in range(ell+1))
            H2=sum(C(n,r)**2*C(2*n-r,ell-r) for r in range(ell+1))
            assert H==H2
            for r in range(ell+1):
                assert C(2*n-ell,n)*C(n,r)**2*C(2*n-r,ell-r) == C(n,ell)*C(n,r)*C(ell,r)*C(2*n-r,n)
                counts['factorial_bridges']+=1
            assert C(2*n-ell,n)*H == sum(F(n,k)*C(k,n-ell) for k in range(n+1))
            counts['auxiliary_identities']+=1
        for j in range(n+1):
            H=lambda ell:sum(C(n,r)*C(n,ell-r)*C(n+r,n) for r in range(ell+1))
            left=sum(C(j,ell)*C(2*n-ell,n)*H(ell) for ell in range(j+1))
            right=sum(F(n,k)*C(j+k,n) for k in range(n+1))
            assert left==right
            counts['final_convolutions']+=1
    return counts

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--ct-max',type=int,default=8)
    ap.add_argument('--identity-max',type=int,default=35)
    ap.add_argument('--json',default=None)
    args=ap.parse_args();start=time.time()
    report={'claim':'A220119 constant-term identity','direct_expansion':[],
            'finite_checks_are_not_a_universal_proof':True}
    for n in range(args.ct_max+1):
        ct=direct_constant_term(n);a=double_sum(n);assert ct==a,(n,ct,a)
        report['direct_expansion'].append({'n':n,'value':str(a)})
        print('DIRECT FIVE-VARIABLE EXPANSION',n,a,'PASS',flush=True)
    report['identity_bound']=args.identity_max
    report['identity_checks']=check_identities(args.identity_max)
    report['elapsed_seconds']=round(time.time()-start,3)
    print(json.dumps(report,indent=2),flush=True)
    if args.json:
        with open(args.json,'w')as f:json.dump(report,f,indent=2)

if __name__=='__main__':
    main()
