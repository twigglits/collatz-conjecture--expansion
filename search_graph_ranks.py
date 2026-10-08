"""Exact SMT search for an eventual affine rank on undirected Collatz edges.

Requires z3-solver (tested with 5.1.0.0). The solver results are not Lean proofs.
Use e.g. PYTHONPATH=/tmp/collatz-rank-solver python3 search_graph_ranks.py.
Only sufficiently large inputs are constrained: strict negative slope suffices,
and zero slope is allowed when the constant difference is strictly negative.
"""
import argparse
import hashlib
import json
import sys
import time
import z3

DEFAULT_MODULI = (1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 27,
                  32, 36, 48, 54, 64, 72, 96, 108, 128, 144)


def constraints(modulus):
    refinement = 6 * modulus
    slopes = [z3.Real(f'a_{i}') for i in range(modulus)]
    offsets = [z3.Real(f'b_{i}') for i in range(modulus)]
    result = [(f'positive_{i}', slopes[i] >= 1) for i in range(modulus)]
    for s in range(refinement):
        source = s % modulus
        edges = [(3*refinement//2 if s % 2 else refinement//2,
                  (3*s+1)//2 if s % 2 else s//2),
                 (2*refinement, 2*s)]
        if s % 3 == 2:
            edges.append((2*refinement//3, (2*s-1)//3))
        options = []
        for A, B in edges:
            target = B % modulus
            slope = slopes[target]*A - slopes[source]*refinement
            offset = (slopes[target]*B + offsets[target]
                      - slopes[source]*s - offsets[source])
            options.append(z3.Or(slope < 0, z3.And(slope == 0, offset < 0)))
        result.append((f'class_{s}', z3.Or(options)))
    return slopes, offsets, result


def solve(modulus, timeout):
    slopes, offsets, rows = constraints(modulus)
    solver = z3.Solver()
    solver.set(timeout=timeout, random_seed=0)
    for name, condition in rows:
        solver.assert_and_track(condition, name)
    # assert_and_track uses assumptions. Include their activation in the
    # fingerprint, rather than hashing only the conditional assertions.
    smt_text = solver.sexpr() + '\n(check-sat-assuming (' + ' '.join(
        name for name, _ in rows) + '))\n'
    problem_hash = hashlib.sha256(smt_text.encode()).hexdigest()
    started = time.monotonic()
    status = solver.check()
    result = dict(modulus=modulus, refinement=6*modulus,
                  status=str(status), seconds=time.monotonic()-started,
                  smt_sha256=problem_hash)
    if status == z3.unsat:
        result['unsat_core'] = [str(x) for x in solver.unsat_core()]
    elif status == z3.sat:
        model = solver.model()
        result['coefficients'] = [
            [str(model.eval(a)), str(model.eval(b, model_completion=True))]
            for a, b in zip(slopes, offsets)]
    else:
        result['reason'] = solver.reason_unknown()
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--moduli', type=int, nargs='+', default=DEFAULT_MODULI)
    parser.add_argument('--timeout-ms', type=int, default=30000)
    args = parser.parse_args()
    if any(m <= 0 for m in args.moduli) or args.timeout_ms <= 0:
        parser.error('moduli and timeout must be positive')
    rows = []
    for modulus in args.moduli:
        row = solve(modulus, args.timeout_ms)
        rows.append(row)
        print(f'M={modulus}: {row["status"]}', file=sys.stderr, flush=True)
    print(json.dumps(dict(solver='Z3', version=z3.get_version_string(),
                          timeout_ms=args.timeout_ms, cases=rows,
                          all_unsat=all(row['status']=='unsat' for row in rows),
                          scope='Exact SMT results for the listed templates; not kernel-checked proofs.'),
                     indent=2))


if __name__ == '__main__':
    main()
