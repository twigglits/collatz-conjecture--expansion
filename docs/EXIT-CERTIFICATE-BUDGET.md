# Cutoff and precision requirements for exit-mass certificates

**Collatz remains unresolved.** The direct exit test has a quantitative
resource constraint, even when its cutoff and arithmetic precision are
chosen adaptively. At floor 64 and exponent 3/2, certifying contraction
by 993/1000 at **G distinct horizons** requires
\[
             R_*\ge64(1000/993)^{2G},                 \tag{1}
\]
where \(R_*\) is the largest source cutoff used. With integer lower
weights \(\lfloor S n^{-3/2}\rfloor\), the largest scale also satisfies
\[
             S_*>4(1000/993)^{G-1}\qquad(G\ge1).      \tag{2}
\]
Thus neither a fixed cutoff nor a fixed arithmetic scale can produce
infinitely many successful tests of this form. These are restrictions
on the certificate method, not on the actual survivor mass. They do
not refute the existing 128 certificates or an eventual contraction.

The discrete envelope and product inequalities below are kernel
theorems in [ExitCertificateBudget.lean](../lean/ExitCertificateBudget.lean).
The real sums, integrals, adaptive-cutoff argument, and precision bound
are written proofs. No external theorem is needed for this result.

## 1. Monotonicity in the source cutoff

Use the actual nested survivor sets from
[SURVIVOR-EXIT-MASS.md](SURVIVOR-EXIT-MASS.md), now with general
integer floor \(H\ge1\) and exponent \(s>1\). Put
\[
 T(R)=\frac{R^{1-s}}{s-1},\quad
 P_k(R)=\sum_{H<n\le R,\ \tau_H(n)>k}n^{-s},\quad
 E_k(R)=\sum_{H<n\le R,\ \tau_H(n)=k+1}n^{-s},
\]
and \(V_k(R)=P_k(R)+T(R)\). Infinite hitting times are allowed.
For fixed \(R\ge H\), the exact identity is
\[
             V_{k+1}(R)=V_k(R)-E_k(R).                \tag{3}
\]
Moreover, for integers \(H\le R\le R'\),
\[
\begin{split}
 P_k(R')-P_k(R)
 &\le\sum_{R<n\le R'}n^{-s}
 \le\int_R^{R'}t^{-s}\,dt=T(R)-T(R'),\\
 E_k(R')&\ge E_k(R).
\end{split}
\]
Consequently \(V_k(R')\le V_k(R)\), and
\(E_k(R')/V_k(R')\ge E_k(R)/V_k(R)\). This is monotonicity of the
**exact real test**. Rounded integer upper bounds need not be
monotone in the cutoff; that stronger assertion is not used.

If the integer test implemented in the exit-mass replay passes, then
the exact real test passes: its exit lower bound is at most
\(E_k(R)\), and its mass upper bound is at least \(V_k(R)\). The
argument covers these square-root enclosures, with different scales
permitted at different horizons. A different method that obtains a
sharper bound on the omitted tail would need its own analysis.

## 2. The product budget, including arbitrary cutoff schedules

At distinct selected horizons \(k_1<\cdots<k_G<K\), suppose
\[
 E_{k_i}(R_i)\ge(1-\rho)V_{k_i}(R_i),\qquad 0<\rho<1.
\]
Set \(R_*=\max(H,R_1,\ldots,R_G)\). Section 1 transfers every
selected success to this single cutoff. Equation (3) contracts its
envelope by \(\rho\) at each selected horizon and decreases it at
every other horizon. Hence
\[
 T(R_*)\le V_K(R_*)\le\rho^G V_0(R_*)\le\rho^G T(H). \tag{4}
\]
The last inequality follows by integrating over \([H,R_*]\), as in
Section 1. Rearranging gives the general requirement
\[
 \boxed{R_*\ge H\rho^{-G/(s-1)}.}                     \tag{5}
\]
No monotonicity of the chosen schedule \(R_i\) is assumed. Counting
the same horizon again at another cutoff does not supply another
contraction. For \(H=64,s=3/2,\rho=993/1000\), (5) is (1), or
equivalently the integer inequality
\[
       64\,1000^{2G}\le R_*\,993^{2G}.               \tag{6}
\]

There is also a variable-loss version. If the selected tests certify
\(0\le\ell_i\le E_{k_i}(R_i)/V_{k_i}(R_i)<1\), then
\[
 \prod_i(1-\ell_i)\ge(H/R_*)^{s-1},\qquad
 \sum_i-\log(1-\ell_i)\le(s-1)\log(R_*/H).            \tag{7}
\]
In particular \(\sum_i\ell_i\) obeys the same upper bound. This
follows from the same telescoping and \(\ell\le-\log(1-\ell)\).
At a fixed cutoff, using every exact loss makes the product telescope
to \(V_K/V_0\). If all starts through that cutoff have entered the
floor, its final value is exactly \(T(R)/V_0(R)\).

## 3. What the kernel theorem says

Let \(U_k,L_k\) be nonnegative integers satisfying
\[
 U_{k+1}+L_k\le U_k,\qquad B\le U_k.
\]
For the existing fixed-cutoff replay,
\(U_k=A_k+C_k+B\) and
\(U_k-U_{k+1}=L_k+\#\{n\le R:\tau_H(n)=k+1\}\), so these
inequalities hold exactly. If a successful index obeys
\((q+h)L_k\ge hU_k\), then
\((q+h)U_{k+1}\le qU_k\). The kernel theorem
`exit_tail_product` proves, for all horizons \(K\),
\[
       (q+h)^{G(K)}B\le q^{G(K)}U_0,                 \tag{8}
\]
where \(G(K)\) counts successful indices less than \(K\).
It does not assume they are consecutive. A separate kernel theorem
gives \(G(K)\le U_0-B\) when \(B>0\) and \(q<q+h\); this weaker
integer bound already excludes an unbounded success count in a
positive integer envelope that decreases at every step.

For the stored \(R=2{,}000{,}000\), \(S=2^{96}\) record,
\[
 B=112045541949572279837463878,\qquad
 U_0=19729971610812289723786322775.
\]
Exact Python power comparisons give
\[
 1000^{736}B\le993^{736}U_0,\qquad
 1000^{737}B>993^{737}U_0.
\]
Thus this product budget allows at most **736** successful horizons
at that cutoff and scale. This is a necessary bound, not an assertion
that 736 successes exist; only 128 passed. The existing table already
has no exits after time 335, so its last possible successful horizon
is 334. The product bound is useful for arbitrary schedules through
(5), not as a sharper description of this exhausted finite table.

## 4. A fixed integer scale also runs out of possible certificates

Suppose the lower numerator at a successful horizon is an integer
\(L_i\), with \(L_i/S_i\le D_{k_i}\), and the positive upper
denominator makes success imply \(L_i\ge1\). This holds for the
implemented test, whose tail upper numerator is at least two.
Let \(S_*=\max_i S_i\). Before the last of \(G\ge1\) successful
horizons, the actual mass has undergone \(G-1\) certified contractions.
Therefore
\[
 \frac1{S_*}\le\frac1{S_G}\le D_{k_G}\le M_{k_G}
       \le\rho^{G-1}M_0
       <\rho^{G-1}\frac{H^{1-s}}{s-1}.               \tag{9}
\]
The strict integral bound on \(M_0=\sum_{n>H}n^{-s}\) gives
\[
            S_*>(s-1)H^{s-1}\rho^{-(G-1)}.           \tag{10}
\]
This proves (2) independently of the cutoff schedule. With a fixed
scale \(2^{96}\), the resulting upper bound is **9276** successful
horizons, even if cutoffs can increase without limit. Exact powers
verify that (2) permits \(G=9276\) but excludes \(G=9277\).
No claim of attaining this bound is made. For \(S_*=2^b\), (2) reads
\[
 b>2+(G-1)\log_2(1000/993).
\]
The coefficient of \(G-1\) is approximately 0.01013438; decimals are
explanatory and do not decide the bounds.

## 5. Consequences for an infinite extension

If all cutoffs used through horizon \(K\) are at most
\(C(K+1)^a\), then (5) permits only \(G(K)=O(\log(K+1))\) fixed-factor
successes. This does **not** rule out infinitely many sparse successes:
such a sequence would still force \(M_k\to0\). A positive proportion
of successful horizons requires an exponentially growing largest cutoff.

There is a stronger conditional caution. If the actual mass satisfies
\(M_k\le A\sigma^k\), \(0<\sigma<1\), and \(R_k\le C(k+1)^a\), then
\[
 \frac{E_k(R_k)}{V_k(R_k)}
 \le(s-1)A C^{s-1}\sigma^k(k+1)^{a(s-1)}\longrightarrow0.
\]
Thus, even under exponential decay of the actual mass, a polynomial
cutoff would eventually fail every fixed positive loss threshold.
A failed truncated test remains inconclusive about actual contraction.

Both cutoff growth and precision growth are necessary for infinitely
many successes of the implemented fixed-factor test. Neither is
sufficient. This result supplies no theorem forcing a new successful
horizon, no vanishing-mass result, and no exclusion of nontrivial
positive cycles or divergent positive trajectories.

Run `python3 verify_exit_certificate_budget.py`. Its
[verification record](../results/exit-certificate-budget/verification.json)
separates the fresh Lean build, reused source-table verification,
exact finite comparisons, and written analytic scope.
