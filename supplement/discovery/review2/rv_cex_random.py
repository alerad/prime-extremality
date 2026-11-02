#!/usr/bin/env python3
"""Random greedy maximal primitive sets for larger N (floating point; evidence only).
Two orderings: uniform random permutation of [2,N], and a small-element-biased one (key n*U).
Every set is evaluated at k = k_9 - 1e-6 over ALL truncations; thresholds computed for the lowest."""
import json, os, sys, time, random
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rv_common import is_prime, progress
import rv_cex as C

K9 = 125.8404540694456574832


def greedy(N, rng, biased):
    nums = list(range(2, N + 1))
    if biased:
        nums.sort(key=lambda n: n * rng.random() ** 2)
    else:
        rng.shuffle(nums)
    A = []
    for x in nums:
        if all(x % a and a % x for a in A):
            A.append(x)
    return tuple(sorted(A))


def run(args):
    N, seed, nsamp = args
    rng = random.Random(seed)
    sets = list({greedy(N, rng, i % 2 == 1) for i in range(nsamp)})
    PN = tuple(q for q in range(2, N + 1) if is_prime(q))
    sets = [A for A in sets if A != PN]
    viol, lows = 0, []
    for s in range(0, len(sets), 500):
        batch = sets[s:s + 500]
        D = C.D_matrix(batch, N)
        m9, _ = C.running_min(D, K9 - 1e-6)
        viol += int((m9 < -1e-10).sum())
        m150, _ = C.running_min(D, 150.0)
        idx = np.where(m150 < -1e-10)[0]
        if len(idx):
            ks = C.thresholds(D[idx])
            lows += [(float(k), batch[i]) for k, i in zip(ks, idx)]
    lows.sort()
    return {"N": N, "seed": seed, "nsets": len(sets), "violations": viol, "n_fail_150": len(lows),
            "lowest": lows[:2]}


if __name__ == "__main__":
    from multiprocessing import Pool
    cfg = [(N, 1000 * N + r, int(os.environ.get("NSAMP", 3000))) for N in (70, 80, 100, 130, 160, 200, 260, 330, 400)
           for r in range(2)]
    res = []
    t0 = time.time()
    with Pool(int(os.environ.get("JOBS", 16))) as pool:
        for i, r in enumerate(pool.imap_unordered(run, cfg)):
            res.append(r)
            print(json.dumps(r), flush=True)
            progress(i + 1, len(cfg), "random", "config")
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "rv_cex_random.json"), "w") as f:
        json.dump(sorted(res, key=lambda r: (r["N"], r["seed"])), f, indent=1)
    print(f"done in {time.time()-t0:.0f}s; total sets {sum(r['nsets'] for r in res)}, "
          f"violations {sum(r['violations'] for r in res)}")
