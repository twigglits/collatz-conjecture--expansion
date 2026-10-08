"""Numerical sanity checks for docs/NATURAL-DENSITY-ALMOST-BOUNDED.md.

These checks support, but do not prove, the written natural-density argument:
1. Lemma 2.1 at small n: the tilted characteristic function never exceeds
   Tao's absolute-value bound in floating-point evaluations truncated at AMAX.
2. Lemma 3.1 with psi(z)=2^z: four renewal sums are close to 1/ln(4/3).
3. Monte Carlo: coarsened first-passage histograms for uniform starts at two
   scales and log-uniform starts are compared with a same-law noise diagnostic.

Roundoff is not certified. The Monte Carlo bins do not measure total variation
of the full integer-valued laws. Fuel exhaustion remains unresolved.
"""
from datetime import datetime, timezone
import cmath
import hashlib
import json
import math
from pathlib import Path
import random

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/natural-density'
AMAX = 70
BETA = math.log2(3)
PASSAGE_FUEL = 10000


def tilted_ratio(n, thetas):
    """Floating-point ratio to Tao's (7.5), over unit xi and the given tilts."""
    Q, per = 3 ** n, 2 * 3 ** (n - 1)
    p2 = [pow(pow(2, -1, Q), k, Q) for k in range(2 * per + 2 * AMAX + 2)]
    units = [xi for xi in range(Q) if xi % 3]
    tw = [cmath.exp(-2j * cmath.pi * k / Q) for k in range(Q)]
    tilted = {}
    for th in thetas:
        w = {(0, 0): 1 + 0j}            # (X mod Q, |a| mod per) -> weight
        for i in range(1, n + 1):
            nw = {}
            for (x, s), v in w.items():
                for a in range(1, AMAX + 1):
                    s2 = (s + a) % per
                    key = ((x + pow(3, i - 1, Q) * p2[s2 + per]) % Q, s2)
                    nw[key] = nw.get(key, 0) + v * 0.5 ** a * cmath.exp(2j * cmath.pi * th * a)
            w = nw
        dist = [0j] * Q
        for (x, _), v in w.items():
            dist[x] += v
        tilted[th] = {xi: abs(sum(dist[x] * tw[xi * x % Q] for x in range(Q) if dist[x])) for xi in units}
    worst = 0.0
    for xi in units:
        chi = lambda y: tw[xi * (y % Q) % Q]
        st = {0: 1.0}                    # b_[1,j] mod per -> prob * prod |f|
        for j in range(1, n // 2 + 1):
            ns = {}
            for l, v in st.items():
                for b in range(2, AMAX + 1):
                    l2 = (l + b) % per
                    x = pow(3, 2 * j - 2, Q) * p2[l2 + per] % Q
                    f = abs(sum(chi(x * (pow(2, a2, Q) + 3)) for a2 in range(1, b)) / (b - 1))
                    ns[l2] = ns.get(l2, 0) + v * (b - 1) / 2 ** b * f
            st = ns
        bound = sum(st.values())
        worst = max(worst, max(tilted[th][xi] for th in thetas) / bound)
    return worst


def renewal(tau):
    """Floating-point renewal sum, restricted to 40 sqrt(kstar) about kstar."""
    kstar, total = tau / (2 - BETA), 0.0
    for k in range(max(1, int(kstar - 40 * kstar ** 0.5)), int(kstar + 40 * kstar ** 0.5) + 2):
        t = k * BETA + tau
        s = math.ceil(t)
        lp = math.lgamma(s) - math.lgamma(k) - math.lgamma(s - k + 1) - s * math.log(2)
        if lp > -700:
            total += math.exp(lp) * 2 ** (s - t)
    return total


X_LOG2 = 40


def syr(n):
    n = 3 * n + 1
    return n >> ((n & -n).bit_length() - 1)


def passage_cell(n):
    x = 1 << X_LOG2
    for steps in range(PASSAGE_FUEL + 1):
        if n <= x:
            return (min(int(math.log2(x / n) / 0.5), 11), n % 9), steps
        if steps == PASSAGE_FUEL:
            return None, steps
        n = syr(n)


def sample(kind, rng):
    if kind == 'log60_80':
        # The proposal probability of an odd n in block b is 2**(1-b)/20.
        # Integer rejection accepts with probability 2**b/n, so the accepted
        # weights are proportional to 1/n under the ideal uniform-random model.
        while True:
            b = rng.randrange(60, 80)
            n = 2 * rng.randrange(1 << (b - 1), 1 << b) + 1
            if rng.randrange(n) < (1 << b):
                return n
    if kind not in ('unif60', 'unif80'):
        raise ValueError(f'Unknown sample kind: {kind}')
    lo = 60 if kind == 'unif60' else 80
    return rng.randrange(1 << lo, 1 << (lo + 1)) | 1


def law(kind, count, seed):
    rng, h = random.Random(seed), {}
    exhausted, max_steps = 0, 0
    for _ in range(count):
        c, steps = passage_cell(sample(kind, rng))
        max_steps = max(max_steps, steps)
        if c is None:
            exhausted += 1
            continue
        h[c] = h.get(c, 0) + 1
    return {c: v / count for c, v in h.items()}, {
        'kind': kind, 'seed': seed, 'count': count,
        'fuel_exhausted': exhausted, 'max_syracuse_steps': max_steps,
    }


def tv(p, q):
    return sum(abs(p.get(c, 0) - q.get(c, 0)) for c in set(p) | set(q)) / 2


def main():
    thetas = [0.0, 0.1, 0.25, 0.37, 0.5, 0.81]
    ratios = {n: tilted_ratio(n, thetas) for n in range(2, 6)}
    assert all(r <= 1 + 1e-9 for r in ratios.values()), ratios
    target = 1 / math.log(4 / 3)
    ren = {tau: renewal(tau) for tau in (300.9, 1000.37, 3000.11, 10000.5)}
    assert all(abs(r - target) < 1e-3 for r in ren.values()), ren
    count = 60000
    laws, diagnostics = {}, {}
    for key, kind, seed in (('unif60', 'unif60', 1), ('unif80', 'unif80', 2),
                            ('log60_80', 'log60_80', 3), ('unif60_repeat', 'unif60', 99)):
        laws[key], diagnostics[key] = law(kind, count, seed)
    exhausted = sum(d['fuel_exhausted'] for d in diagnostics.values())
    noise = tv(laws['unif60'], laws['unif60_repeat'])
    pairs = {f'{a}|{b}': tv(laws[a], laws[b])
             for a, b in (('unif60', 'unif80'), ('unif60', 'log60_80'), ('unif80', 'log60_80'))}
    compatible = not exhausted and max(pairs.values()) < 2 * noise + 0.01
    files = ['docs/NATURAL-DENSITY-ALMOST-BOUNDED.md', 'verify_natural_density.py']
    manifest = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'conjecture_status': 'unresolved',
        'written_scope': ['Lemma 2.1, Corollary 2.2, Proposition 2.3 (joint fine-scale mixing)',
                          'Lemma 3.1 (renewal lemma)', 'Proposition 4.1 and Theorem ND (natural density)'],
        'external_inputs': ['Tao, arXiv:1909.03562 (Forum Math. Pi 2022): Props 1.9, 5.2, 7.3, Lemma 2.2, Section 3',
                            'local limit theorem with rate (Petrov VII.3)', 'Erdos-Turan-Koksma inequality',
                            'a finite irrationality exponent for log_2 3 (e.g. Rhin 1987)'],
        'not_proved': ['Collatz convergence or divergence',
                       'explicit constants; positive-density Collatz via numerical verification',
                       'universal analytic statements by these finite numerical checks'],
        'numerical_scope': {
            'arithmetic': 'Python float/complex; no certified roundoff bounds',
            'tilt_truncation': AMAX, 'tilts': thetas,
            'tilt_omitted_mass_upper_by_n': {n: n * 2.0 ** -AMAX for n in ratios},
            'product_omitted_mass_upper_by_n': {
                n: (n // 2) * (AMAX + 1) * 2.0 ** -AMAX for n in ratios},
            'renewal_window': '40 sqrt(kstar) on either side; no certified tail or roundoff bound',
            'mc_bins': '(min(floor(log2(x/n)/0.5), 11), n mod 9)',
            'mc_interpretation': 'TV of coarsened empirical histograms only; heuristic noise comparison',
            'log_sampler': 'odd-only proposal and integer rejection; ideal accepted mass proportional to 1/n',
            'passage_fuel': PASSAGE_FUEL,
        },
        'replay_summary': {'tilted_over_bound_7_5_max_by_n': ratios, 'renewal_values': ren,
                           'renewal_target_1_over_ln_4_3': target, 'mc_samples_per_law': count,
                           'mc_coarse_same_law_tv': noise, 'mc_coarse_pairwise_tv': pairs,
                           'mc_diagnostics': diagnostics, 'fuel_exhausted': exhausted,
                           'mc_noise_diagnostic_passed': compatible, 'x': f'2^{X_LOG2}'},
        'commands': ['python3 verify_natural_density.py'],
        'sha256': {f: hashlib.sha256((ROOT / f).read_bytes()).hexdigest() for f in files},
    }
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / 'verification.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps(manifest['replay_summary'], indent=2))
    assert exhausted == 0, f'{exhausted} trajectories exhausted fuel and remain unresolved'
    assert compatible, (pairs, noise)
    print('Numerical sanity checks passed; they do not prove the written theorem.')


if __name__ == '__main__':
    main()
