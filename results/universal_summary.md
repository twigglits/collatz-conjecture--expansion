# Universal-cycle verification summary

- S1 rigidity grid: 274877906944 (a,c) pairs, odd a,c < 2^20 — formula violations 0, iff violations 0, fixed points 10485760 = 20 Mersenne a x 2^19 c  [1.05s GPU]
- S2 fixed-point census: 137438953472 triples (a,c<512, x<2^22) — 5477 fixed points, all matching the one-step law, set-equal to exact divisor enumeration  [0.48s GPU]
- S3 catalog: odd a < 2^24, fuel 4096 — periodic 25, escape 8388583, fuelout 0  [0.00s GPU]
- S4 scaling fuzz: 8589934592 trials, 0 violations  [0.03s GPU]

## Universal cycle families found (1 periodic under F_{a,1}, a < 2^24)

| a | period k | H (halvings) | a+1 power of 2? |
|---:|---:|---:|:---:|
| 1 | 1 | 1 | yes |
| 3 | 1 | 2 | yes |
| 5 | 2 | 5 | NO |
| 7 | 1 | 3 | yes |
| 15 | 1 | 4 | yes |
| 31 | 1 | 5 | yes |
| 63 | 1 | 6 | yes |
| 127 | 1 | 7 | yes |
| 255 | 1 | 8 | yes |
| 511 | 1 | 9 | yes |
| 1023 | 1 | 10 | yes |
| 2047 | 1 | 11 | yes |
| 4095 | 1 | 12 | yes |
| 8191 | 1 | 13 | yes |
| 16383 | 1 | 14 | yes |
| 32767 | 1 | 15 | yes |
| 65535 | 1 | 16 | yes |
| 131071 | 1 | 17 | yes |
| 262143 | 1 | 18 | yes |
| 524287 | 1 | 19 | yes |
| 1048575 | 1 | 20 | yes |
| 2097151 | 1 | 21 | yes |
| 4194303 | 1 | 22 | yes |
| 8388607 | 1 | 23 | yes |
| 16777215 | 1 | 24 | yes |
