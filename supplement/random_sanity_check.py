#!/usr/bin/env python3
"""Seeded numerical sanity check, not a proof; Python standard library only."""
import math
import random

N = 302
SEED = 20260922
CS = (0.1, 0.25, 0.5, 0.75, 0.9, 1.0)
U = set(range(2, N + 1))
P = {n for n in U if all(n % d for d in range(2, math.isqrt(n) + 1))}

def primitive(a):
    return all(y % x for x in a for y in a if x < y)

def gauss(n):
    out = []
    for i in range(1, n + 1):
        z = math.cos(math.pi * (i - 0.25) / (n + 0.5))
        for _ in range(30):
            p0, p1 = 1.0, z
            for k in range(2, n + 1):
                p0, p1 = p1, ((2*k-1)*z*p1-(k-1)*p0)/k
            dp = n*(z*p1-p0)/(z*z-1)
            dz = p1/dp
            z -= dz
            if abs(dz) < 2e-15:
                break
        out.append(((z+1)/2, 1/((1-z*z)*dp*dp)))
    return out

def run(sets, order):
    results = {name: [] for name, _ in sets}
    baseline = []
    for c in CS:
        nodes = [(c*w, [0.0, 0.0] + [math.log1p(-(c*x)**a) for a in range(2,N+1)]) for x,w in gauss(order)]
        baseline.append(math.fsum(w*math.exp(math.fsum(logs[a] for a in P)) for w,logs in nodes))
        for name, a in sets:
            common, added, removed = a & P, a-P, P-a
            terms = []
            for w, logs in nodes:
                lc = math.fsum(logs[t] for t in common)
                la = math.fsum(logs[t] for t in added)
                lp = math.fsum(logs[t] for t in removed)
                # Compute the difference directly, avoiding cancellation against baseline.
                delta = (math.exp(lp)*math.expm1(la-lp) if la <= lp else -math.exp(la)*math.expm1(lp-la))
                terms.append(w*math.exp(lc)*delta)
            results[name].append(math.fsum(terms))
    return baseline, results

def main():
    rng = random.Random(SEED)
    sets = [('all_2_to_302', U), ('upper_half', set(range(152,303))), ('469_exchange', (P-{2,3})|{4,6,9})]
    for kind in ('random_primitive', 'prime_biased_primitive', 'prime_like_unrestricted'):
        for i in range(100):
            order = sorted(U)
            if kind == 'prime_like_unrestricted':
                # Same cardinality as the primes, with a 1/log(n) sampling bias.
                order.sort(key=lambda n: -math.log(rng.random())*math.log(n))
                a = set(order[:len(P)])
            else:
                if kind == 'random_primitive':
                    rng.shuffle(order)
                else:
                    order.sort(key=lambda n: -math.log(rng.random())/(8 if n in P else 1))
                a = set()
                for n in order:
                    if all(n % b and b % n for b in a):
                        a.add(n)
                assert primitive(a)
            sets.append((f'{kind}_{i}', a))
    for p in sorted(P):
        sets.append((f'delete_prime_{p}', P-{p}))
        if p*p <= N:
            sets.append((f'replace_prime_{p}_with_square', (P-{p})|{p*p}))
    base, result = run(sets, 192)
    base2, result2 = run(sets, 384)
    print(f'N={N}, primes={len(P)}, seed={SEED}, candidates={len(sets)}')
    print('c, prime integral:')
    for c,v in zip(CS,base2): print(f'  {c:g}: {v:.16g}')
    print('Maximum absolute 192/384-node discrepancy:', max([abs(a-b) for a,b in zip(base,base2)] + [abs(a-b) for name in result for a,b in zip(result[name],result2[name])]))
    valid = [(name,a) for name,a in sets if primitive(a) and a != P]
    violations = [(name,c,d) for name,a in valid for c,d in zip(CS,result2[name]) if d <= 0]
    print(f'Distinct nonprime primitive candidates: {len({tuple(sorted(a)) for _,a in valid})}; comparisons: {len(valid)*len(CS)}; nonpositive gaps: {violations}')
    for name in ('all_2_to_302','upper_half','469_exchange'):
        print(name, 'F_1=', format(base2[-1]+result2[name][-1],'.16g'), 'gap=', format(result2[name][-1],'.8g'))
    for kind in ('random_primitive','prime_biased_primitive','prime_like_unrestricted','delete_prime','replace_prime'):
        names = [name for name,a in sets if name.startswith(kind)]
        best = min(names,key=lambda name: result2[name][-1])
        print(kind, 'count=',len(names),'beating primes at c=1=',sum(result2[name][-1]<0 for name in names),'smallest F_1 gap=',format(result2[best][-1],'.12g'),'candidate=',best)
    assert not violations

if __name__ == '__main__':
    main()
