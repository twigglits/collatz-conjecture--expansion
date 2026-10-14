# Finite energy from comparable binary source prefixes

**Collatz remains unresolved.** The preceding slope budget controlled
the individual squared masses of the return columns. This note also
controls every cross term whose binary source prefixes are nested.
Only pairs of disjoint binary source cylinders remain uncontrolled in
this decomposition of the full squared norm.

Keep the even-source, nonfused return columns
\[
 K^*_0=\sum_i p_iF_i,\quad p_i=2^{-t_i},\quad
 F_i=3^{a_i}\mathbf1_{I_i},\quad
 I_i=\{z:z=x_i\pmod{3^{a_i}}\}.
\]
Let \(B_i=\{n:n=r_i\pmod{2^{t_i}}\}\) be the binary source cylinder.
Write \(i\prec j\) when `t_i<t_j` and \(B_j\subset B_i\).
With the previous \(C_*=540\,2^{5180}\), the new written bound is

\[
 \boxed{
 \sum_i\|p_iF_i\|_2^2+
 2\sum_{i\prec j}p_ip_j\int F_iF_j\,d\mu_3
       \le88C_*+2476820<\infty.}                            \tag{1}
\]

The analytic inputs proved below are

\[
 \boxed{\mathbb E\sum_{j=1}^{N}\Lambda_j
                  \log_2(D_j+1)\le12383}                   \tag{2}
\]
for initially adjacent sources, and the uniform restart estimate
\[
 \boxed{\mathbb E[N\mid D_0=D]
                     \le C_*+100\log_2(D+1)+2,\quad D>0.}   \tag{3}
\]

Twelve kernel arithmetic roots support these **written probability,
logarithm, and Haar-energy arguments**. Exact finite checks retain
unfinished paths and independently split the actual truncated energy
into diagonal, nested-source, and disjoint-source parts. No external
analytic theorem is used. None of these statements is an `L2` bound
on the whole density or an estimate for actual forward gradients.

## 1. A second moment for the return-conditioned clock

Under the slope tilt, condition a fresh odd-separation excursion on
returning. The preceding [occupation argument](RETURN-SLOPE-OCCUPATION.md)
shows that its absolute active gap has inward probability `3/4`.
At gap `k>=1` its wait `W`, including the active step, satisfies
\[
 \Pr(W>3v(k)+h\mid\text{prefix, return})\le(3/4)^h,\quad h\ge0,
 \qquad v(k)=v_2(3^k-1)<2k.
\]
Consequently it is stochastically bounded by `3v(k)+G`, where a
positive geometric variable `G` has tail `Pr(G>h)=(3/4)^h`.
The geometric sums give `E G=4` and `E G^2=28`. Thus
\[
 \mathbb EW\le6k+4,\qquad
 \mathbb EW^2\le36k^2+48k+28.                               \tag{4}
\]
This is a conditional moment bound at every finite prefix, not an
assertion that the waits are independent.

For the inward walk set \(V(k)=6k^2+20k\), \(V(0)=0\). The exact
curvature identity is
\[
 V(k)-\{\tfrac34V(k-1)+\tfrac14V(k+1)\}=6k+4.
\]
Stopping at finitely many active blocks and then passing monotonically
shows that the mean remaining physical clock from gap `k` is at most
`V(k)`. This repeats the first-moment argument with arbitrary initial
gap; no boundary value at infinity is prescribed.

For a finite sum of block lengths, expand its square. After a block,
the conditional mean future length is at most `V(k')<=V(k+1)`.
The expected contribution charged to a visit to `k` is therefore at most
\[
 \begin{aligned}
 c_2(k)
 &=36k^2+48k+28+2(6k+4)V(k+1)\\
 &=72k^3+468k^2+616k+236.                                  \tag{5}
 \end{aligned}
\]
Bounding `V(k')` before multiplying by `W` avoids an independence
assumption about the duration and the next direction.

The inward walk from one has expected visits `4*3^-k` to each `k`.
Its physical clock `sigma` before absorption hence satisfies
\[
                  \mathbb E\sigma^2
                       \le4\sum_{k\ge1}3^{-k}c_2(k)=6316.
\]
This can first be applied at an active-step cutoff; the finite sums
have finite second moments by (4), and monotone convergence supplies
the infinite statement. The initial departure adds one step and
`E sigma<=26`, so the complete fresh clock has
\[
          \boxed{\widehat{\mathbb E}[\tau^2\mid\text{return}]
                                                     \le6369.} \tag{6}
\]
The kernel checks the curvature and the denominator-cleared geometric
sum, whose remainder at cutoff `H` is
`144H^3+1584H^2+5336H+6316`. It does not formalize the probability limit.

## 2. Squared logarithmic drift for the grouped return chain

Use \(\ell(D)=\log_2(D+1)\) and the grouped chain from the preceding
note: a group contains all `v=v_2(D)` one-step returns, followed by
an odd-separation excursion. It ends on fusion or on a tilted
excursion that never returns. Write `q_j,l_j` for its starting mass
and logarithmic mass, and set
\[
 m_j=\widehat{\mathbb E}
               [\ell(D_j^{\rm group})^2\mathbf1_{A_j}].
\]
For adjacent sources, the previous result gives
\[
 q_0=l_0=m_0=1,\quad
 \sum_jq_j\le2,\quad\sum_jl_j\le43.                         \tag{7}
\]
The superscript distinguishes these group separations from the
separation at every return in (2).

During a zero-gap step the logarithmic increment `delta` lies in
`[-1,3/5]`. Its tilted mean is at most `1/5`, and
\[
 \mathbb E\delta^2\le\tfrac14+\tfrac34(3/5)^2=13/25.
\]
Iterating over the fixed number `v` of such steps gives, with
`L=ell(D)`,
\[
 \widehat{\mathbb E}\ell(\bar D)^2
 \le L^2+\tfrac25vL+\tfrac1{25}v^2+\tfrac{12}{25}v
 \le\tfrac{36}{25}L^2+\tfrac{12}{25}L.                      \tag{8}
\]
The earlier first-moment bound is
`E_tilt ell(Dbar)<=6L/5`.

At the following odd-separation return,
`ell(D_next)<=ell(Dbar)+(3/5)tau`. Return has tilted probability
`1/2`, with conditional clock moments at most `27` and `6369`.
Squaring this bound and using (8) proves
\[
 m_{j+1}\le\tfrac{18}{25}m_j
             +\tfrac{492}{25}l_j+\tfrac{57321}{50}q_j.       \tag{9}
\]
Fusion contributes `ell(0)=0`. All moment estimates are conditional
on the relevant finite prefix, so no separation/clock independence
is needed. Finite telescoping, (7), and monotone convergence imply
\[
       \sum_jm_j\le
       \frac{50+984\cdot43+57321\cdot2}{14}
       =\frac{78502}{7}<11215.                             \tag{10}
\]

## 3. Count the logarithmic cost at every return

Within a zero-gap run, the mean logarithm after `s` steps is at most
`L+s/5`. Therefore its entire expected returned logarithmic cost is
\[
       \sum_{s=1}^{v}\widehat{\mathbb E}\ell(D_s)
       \le vL+\frac{v(v+1)}{10}
       \le\frac{11}{10}L^2+\frac1{10}L.                     \tag{11}
\]
The logarithmic costs at the odd-separation returns are exactly the
next group-start logarithms; a fusion contributes zero. Their total
mean is at most `sum_j l_j-l_0<=42`. Combining (7), (10), and (11),
\[
 \widehat{\mathbb E}\sum_{\text{all completed returns}}
                       \ell(D_j)
 \le\frac{11\cdot11215+43}{10}+42
 =\frac{61914}{5}<12383.
\]
At each finite return the tilted likelihood ratio is its cumulative
slope `Lambda_j`. Tonelli converts the last bound into (2).
In particular, restricting to even-source nonfused prefixes gives
\[
                   \sum_i p_i\Lambda_i\ell(D_i)\le12383.    \tag{12}
\]

## 4. A logarithmic unweighted restart bound

This step uses the **original** fair binary law. The earlier
[cycle-count argument](RETURN-OCCUPATION-DENSITY.md) puts
`V(D)=D^(1/4)`, `R=400^4`, and `q=399/400`. If `sigma` counts
returns to first reach `D<=R`, its proved conditional tail is
\[
                  \Pr(\sigma>n)\le\frac{D^{1/4}}{400}q^n.
                                                                    \tag{13}
\]
For a start already in this set, `sigma=0`. The same prescribed-attempt
argument bounds the remaining mean fusion count by `C_*` uniformly
over every finite prefix with `D<=R`; it was not specific to `D=1`.

The kernel comparison `2*399^400<400^400` gives `q^400<1/2`.
Choose \(n_0=\lceil100\log_2(D+1)\rceil\). Then
\[
 q^{n_0}\le2^{-n_0/400}\le(D+1)^{-1/4}.
\]
Use the probability bound one for the first `n_0` terms of the tail
sum and (13) thereafter. Since `1-q=1/400`, the remaining geometric
tail is at most one. Thus
\[
             \mathbb E\sigma\le n_0+1
                              \le100\log_2(D+1)+2.
\]
Restart at that finite hitting prefix to obtain (3). The argument
does not change the unweighted adjacent fusion constant already used
elsewhere; it improves the dependence on a general initial separation.

## 5. Sum all overlaps on one binary source path

If \(i\prec j\), the odd counts satisfy `a_i<=a_j`. The ternary
image cylinders are either disjoint or the deeper one is contained
in the shallower one. Hence
\[
 p_ip_j\int F_iF_j\,d\mu_3
       \le p_ip_j3^{a_i}=\Lambda_i p_j.                     \tag{14}
\]
For a fixed prefix `i`, the conditional binary probability of the
continuation prefix `j` is `p_j/p_i`. Its future number of nonfused
returns is bounded by the fresh fusion count from separation `D_i`.
Equation (3) and the tower property therefore give
\[
 \sum_{j:i\prec j}p_ip_j\int F_iF_j\,d\mu_3
 \le p_i\Lambda_i\{C_*+2+100\ell(D_i)\}.                     \tag{15}
\]
Dropping the image-intersection condition is an upper bound on
nonnegative terms. It makes no mixing or independence assumption.

Sum (15), use (12) and the previous
`sum_i p_i Lambda_i<=44`, and add the diagonal. This proves (1).
All infinite sums are nonnegative; equivalently, prove the bounds for
finite prefix collections and then pass monotonically.

Any two distinct binary cylinders are either disjoint or properly
nested. Thus the exact complementary term is
\[
 \mathcal D=
   2\sum_{\substack{i<j\\B_i\cap B_j=\varnothing}}
                         p_ip_j\int F_iF_j\,d\mu_3.          \tag{16}
\]
The total squared Haar norm is the sum of this quantity and the
finite expression in (1). Consequently \(K^*_0\in L^2\) holds if
and only if \(\mathcal D<\infty\). **Neither is proved here.**
The already recorded prefixes `(6,48,2,8)` and `(7,74,3,17)` give
a positive term in (16): binary disjointness does not imply disjoint
ternary images.

## Verification and remaining problem

Run `python3 verify_return_ancestral_overlap.py`. The
[record](../results/return-ancestral-overlap/verification.json) separates
twelve kernel roots, exact rational finite calculations, and the
written infinite proof. It checks the actual nested-source cross sum
both by source-path enumeration and by binary prefix lookup, and
computes the remaining disjoint-source energy separately.

The unresolved overlap now involves different binary source paths.
An estimate for those correlations, or one paired directly with actual
future losses, is still needed. This note does not prove that `L2` is
necessary for Collatz, nor that a full `L2` estimate would alone settle
it. The actual-gradient criterion `Q`, escape exclusion, additional
cycle exclusion, and full Collatz remain open.
