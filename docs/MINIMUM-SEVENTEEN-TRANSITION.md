# Smaller sources across arbitrarily many negative seventeen blocks

Two smaller Mersenne sources exclude a weighted quadrupled Collatz family
as least counterexamples after an arbitrary number of blocks following
the negative-seventeen itinerary. For every prescribed number of blocks
and every exponent bound, pure sources in this excluded family exist.
The positive sources stay positive; the negative orbit only supplies
the parity pattern and affine constants.

The [Lean module](../lean/MinimumSeventeenTransition.lean) proves nineteen
theorem roots using only standard logical axioms. The construction covers
two scalar exit residues. Other exits, convergence of every family member,
and the full positive-integer Collatz conjecture remain unresolved.

## Three sources with variable block length

Let R>=14 and w,u>0. For any natural r, assume

    X=9^R*w,       X+7=2^(57+11r)*u,       a=3^(33+7r)*u.

Define

    N=4*8^R*w-5,
    P=2^(2R+5)*w-1,
    Q=2^(2R+15)*w-1.

The kernel proves 0<P<N and 0<Q<N, together with these ordinary clocks:

| Source | Clock | Endpoint |
|---|---:|---:|
| N | 5R+91+18r | 72a-17 |
| P | 4R+99+18r | 81a-17 |
| Q | 4R+99+18r | 64a-17 |

The initial prefixes reach 4X-5, 243X-1, and 14348907X-1. Three
kernel bridges, valid for every positive q, give

    C^19(2^12*q-33)        =3^7*q-17,
    C^35(2^24*q-1702)      =3^11*q-17,
    C^69(2^51*q-100442350) =3^18*q-17.

Their inverse words use respectively (5,7), (13,11), and (33,18)
extra even and odd steps. Here an inverse odd step corresponds to two
ordinary forward operations. The offsets satisfy
1702=7*3^5+1 and 100442350=7*3^15+1.

After these bridges, N follows r+4 negative-seventeen blocks, P follows
r+3, and Q follows r. Each block has shortcut word OOOOEOOOEEE and
ordinary length 18. The existing kernel identity

    C^(18r)(2048^r*q-17)=2187^r*q-17

transports all three sources to the stated scalar endpoints.

## Two exit residues

If a=64v+13, short profiles give

    C^10(72a-17)=972v+194=b,
    C^4(81a-17)=1944v+389=2b+1.

Since b=2 modulo 4, the existing double-partner identity yields
C^7(81a-17)=C^12(72a-17). Thus P coalesces with N at full ordinary
clocks 4R+106+18r and 5R+103+18r. The independent complete-word
replay appends one common halving, giving clocks larger by one.

If a=64v+61, the profiles are

    C^12(72a-17)=1458v+1385=b,
    C^6(81a-17)=2916v+2771=2b+1,
    C^17(64a-17)=1458v+1384=b-1.

Write b+1=2^k*q with k>0 and q positive odd. The earlier universal
odd-block cover chooses a partner according to 3^k*q modulo 4:

| Exit | Chosen source | Full partner clock | Full clock from N |
|---|---|---:|---:|
| 3 mod4 | P | 4R+109+18r+2k | 5R+106+18r+2k |
| 1 mod4 | Q | 4R+118+18r+2k | 5R+105+18r+2k |

There is no bound on k. In either scalar residue, a strictly smaller
positive source coalesces with N. If N were least, that smaller source
would converge, forcing N to converge too. Hence N cannot be a least
counterexample. This argument does not establish convergence of every
family member without the least-counterexample assumption.

## Pure exponents beyond every bound

For every r, every bound B, and either e=13 or e=61, the kernel constructs
R>B, R>=14, and u>0 such that

    9^R+7=2^(57+11r)*u,       3^(33+7r)*u=e mod64.

Consequently 4*8^R-5 is excluded as least at arbitrarily large exponents
after any prescribed number r of the additional blocks.

The construction uses m=57+11r, D=2^m, T=2^(m-3), and the earlier
binary exponent lift A=liftExponent(m+3). It gives

    9^A+7=64D*t,       9^T=1+D*v,       v odd.

An elementary induction proves

    (1+64d*v)^h=1+64d*U,       U=h*v mod64.

Apply this with d=2^(m-6). Since 9^A=57 modulo 64, choose h0<64
so that 57*3^(33+7r)*v*h0=e modulo 64. A finite kernel proof checks
that every odd multiplier admits both target residues. Set

    h=h0+64*(B+14),       R=A+T*h,       u=64*t+9^A*U.

The identities and bounds follow without an external lifting theorem.
These pure exponents are enormous even when r is small. Their finite
Python checks use modular powers; they do not construct their starting
integers or replay their full trajectories.

## Verification and scope

Run the [verifier](../verify_minimum_seventeen_transition.py) with

    python3 verify_minimum_seventeen_transition.py --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16 --cache /tmp/collatz-locality-dev

Omit --cache for fresh builds of all dependencies. With the cache, each
dependency must match the previous manifest's source, log, object bytes,
and compiler version before being copied into an isolated import directory.
The new module is always freshly built. The [manifest](../results/minimum-seventeen-transition/verification.json)
retains fresh and reused build provenance separately.

The [independent replay](../results/minimum-seventeen-transition/replay.json)
checks the three bridges, both scalar exits, all three merger branches,
complete weighted source paths, and inverse guards. Complete cases include
r=4096, R=16384, and later odd blocks of length 4096. Larger source
coordinates have only their transition and exit tails replayed. Pure
exponent checks are modular-only, separately from the universal kernel
existence theorem. No native finite reduction is used by the new module.

The uncovered scalar residues, unrestricted weights and exponents,
arbitrary least sources, universal cap/residual estimates, nontrivial
cycles, divergence, and the full Collatz conjecture remain open.
