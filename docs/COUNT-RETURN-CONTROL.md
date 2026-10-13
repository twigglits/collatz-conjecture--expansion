# Controlling repeated returns of the odd-count gap

**Collatz remains unresolved.** This note gives a written proof of a
uniform first-moment bound for the *unstopped* adjacent odd-count gap,
a polynomial upper bound on full-period balanced noncoalescence, and
the consequent actual-energy estimate \(E_s=O(s^{4/5})\). A bounded
energy subsequence is still missing, as is the exclusion of other cycles.

The stochastic argument is written, not fully formalized in Lean.
[CountReturnControl.lean](../lean/CountReturnControl.lean) proves the
exact restart accounting, the finite-step descent mechanisms, and the
integer comparisons used in the constants. The independent replay
checks finite distributions and the arithmetic, not the infinite
probability argument. No external coalescence theorem is assumed or
replayed, and no claim of novelty is made.

## 1. The probability space and the exact restart identity

Use a Haar-uniform binary input \(x\in\mathbb Z_2\), equivalently
independent fair input bits. Every assertion determined by the first
\(t\) bits has the uniform law on \(0\le r<2^t\). This is a coherent
family of residue laws, **not** a uniform distribution on positive integers.
The shortcut map has the affine lift
\[
 U^t(2^tq+r)=3^{a_t(r)}q+U^t(r),
\]
where \(a_t\) counts odd inputs. The coefficient is odd. Thus, after
any exposed prefix, each endpoint is an odd affine function of the
remaining Haar input. Each endpoint's next parity is fair, and the next
input bit flips both parities. The two endpoints need not be independent.
This observation also applies after any almost-surely finite prefix
stopping time, by partitioning into its countably many finite prefixes.

Let \(d_t=a_t(x)-a_t(x+1)\). Given the exposed prefix, its two next-bit
children either both hold or make opposite unit steps. At zero, opposite
endpoint parities cause a new departure. The kernel proves the exact
two-child identity and hence
\[
 \mathbb E|d_{t+1}|-\mathbb E|d_t|
   =\Pr(d_t=0,\ U^t(x)\not\equiv U^t(x+1)\pmod2).       \tag{1}
\]
No stopping is used in (1). It accounts for precisely the restarts omitted
by the earlier stopped-gap martingale.

## 2. A uniform bound on the first count-return clock

Start at equal odd counts and endpoints differing by a positive integer
\(D\). Let \(\tau\) be the first *positive* time their additional odd
counts agree. If \(D\) is even, \(\tau=1\). If it is odd, the first
step makes the absolute count gap one.

While the count gap is nonzero, orient the lower-count endpoint as \(X\)
and write the other as
\[
                       Y=3^dX+c,\qquad d\ge1,\quad c\in\mathbb Z.
\]
Here \(X\) is conditionally Haar-uniform. If \(R\) is the number of
holding steps before the next active count-gap step, then
\[
 \Pr(R\ge h\mid d,c)
 =\Pr((3^d-1)X+c\equiv0\pmod{2^h})
 \le\min(1,2^{v-h}),\quad v=\nu_2(3^d-1).              \tag{2}
\]
To justify the equality, two starting values have the same first \(h\)
parities exactly when they are congruent modulo \(2^h\). This follows
inductively from the two inverse branches: division by two removes one
bit, and multiplication by three is invertible modulo powers of two.
Equal parities throughout are exactly the event that this nonzero count
gap keeps holding. The linear congruence in (2) has either no solutions
or \(2^{\min(v,h)}\) solutions modulo \(2^h\).

The kernel checks \(0<3^d-1<2^{2d}\), so \(v\le2d-1\).
Summing (2) gives
\[
                   \mathbb E(R+1\mid d,c)\le v+2\le2d+1.             \tag{3}
\]
In particular the next active step exists almost surely, uniformly in
the offset \(c\). At an active step its sign is chosen by a fresh fair
bit. Until the first count return, the embedded absolute gap is therefore
a simple symmetric walk from one, absorbed at zero. This does not assert
independence between its holding times and its past.

Stop after absorption or \(m\) active steps. Before that stop the gap
is at most \(m+1\). Including the initial departure, (3) bounds the
expected physical clock by
\(1+m(2m+3)\le3(m+1)^2\). The reflection count for a simple walk gives
survival through \(m\) active steps at most \(2/\sqrt{m+1}\).
For completeness, its exact probability is
\(2^{-m}\binom m{\lfloor m/2\rfloor}\); the displayed upper bound
follows by induction from the central-binomial ratio.
Markov's inequality consequently gives, for any integer \(H\ge1\),
\[
 \Pr(\tau>H)\le\frac2{\sqrt{m+1}}+\frac{3(m+1)^2}{H}.
\]
Choose \(m=\lfloor H^{2/5}\rfloor\). Then \(m+1\ge H^{2/5}\)
and \(m+1\le2H^{2/5}\), yielding the convenient uniform bound
\[
             \boxed{\Pr(\tau>H)\le16H^{-1/5}.}          \tag{4}
\]
Thus \(\tau<\infty\) almost surely for every starting separation.

## 3. A fractional-moment contraction at count returns

For either endpoint, write its affine trajectory as
\[
 U^t(X)=\lambda_tX+B_t,\quad
 \lambda_t=3^{a_t}/2^t,\quad B_0=0,
\]
where \(B_{t+1}=m_tB_t+\epsilon_t/2\),
\(m_t=1/2\) or \(3/2\), and \(\epsilon_t\) is the odd parity bit.
These nonnegative real coefficients are determined by finite parity
words even though \(X\) itself is 2-adic. Conditional on the past,
\(\epsilon_t\) is fair. For \(0<\alpha<1\), put
\[
 r_\alpha=\tfrac12[(1/2)^\alpha+(3/2)^\alpha]<1.
\]
Subadditivity of the \(\alpha\)-power gives
\[
 \mathbb EB_{t+1}^\alpha
 \le r_\alpha\mathbb EB_t^\alpha+2^{-\alpha-1}.
\]
Take \(\alpha=1/2\). The kernel's integer square comparison implies
\(r_{1/2}<31/32\), hence
\[
                         \mathbb EB_t^{1/2}\le16\quad(t\ge0).       \tag{5}
\]

A fixed-time estimate cannot simply be evaluated at \(\tau\). To
justify the stopping step, take \(\beta=1/16\). On
\(2^{j-1}<\tau\le2^j\), Hölder's inequality, (4), and (5) give
\[
\begin{split}
 \mathbb E[B_\tau^\beta\mathbf1_{2^{j-1}<\tau\le2^j}]
 &\le(16\,2^j)^{1/8}
          (16\,2^{-(j-1)/5})^{7/8}\\
 &\le64\,2^{-j/20}.
\end{split}
\]
Here \(\mathbb E\max_{t\le2^j}B_t^{1/2}\le16\,2^j\) by a
finite sum. The event \(\tau=1\) contributes at most two. The integer
comparison \(51^{20}<2\,50^{20}\) proves
\(\sum_{j\ge1}2^{-j/20}<50\). Consequently, for either endpoint,
uniformly in \(D\),
\[
                         \mathbb EB_\tau^\beta\le3202.              \tag{6}
\]

Also \(\lambda_t^\beta\) is a nonnegative supermartingale.
Since \(\tau\ge1\), bounded optional stopping followed by Fatou gives
\[
 \mathbb E\lambda_\tau^\beta\le r_\beta
 <\gamma:=509/512.
\]
The strict numerical bound follows from the kernel-checked integer
comparisons \(256^{16}<2\,246^{16}\) and
\(3\,256^{16}<2\,263^{16}\).

At a count return the two multiplicative coefficients coincide. Their
new separation \(D'\) is an ordinary nonnegative integer, independent
of the still-unexposed input, and
\(D'\le\lambda_\tau D+B^{(1)}_\tau+B^{(2)}_\tau\).
There is no assumption that the two corrections are independent.
Equations (6) and the last bound prove
\[
 \boxed{\mathbb E[(D')^{1/16}\mid D]
            \le\frac{509}{512}D^{1/16}+6404.}           \tag{7}
\]

## 4. Reaching zero in finitely many count-return cycles on average

Iterate first positive count returns, retaining separation \(D_n\),
and absorb at \(D_n=0\). The fresh-prefix observation in Section 1
makes (7) valid conditionally at every return.
Put \(V(D)=D^{1/16}\), and choose the explicit integer
\[
                        R=1093120^{16}<2^{336}.
\]
For \(D>R\), (7) gives \(\mathbb E[V(D')\mid D]\le V(D)-1\),
because \(3\cdot1093120=512\cdot6405\).
Stopping this drift inequality on first reaching \(D\le R\) shows
that its expected number of return cycles is at most \(V(D)\).
Indeed the truncated stopped expectation satisfies
\(\mathbb E V(D_{n\wedge\sigma})+\mathbb E(n\wedge\sigma)\le V(D)\),
and monotone convergence bounds \(\mathbb E\sigma\).

There is a prescribed path that reduces every positive separation:

* For even \(D\), choose the next lower endpoint parity even. Both
  endpoints halve, so the next count return has separation \(D/2\).
* For odd \(D\), choose that parity even. The gap becomes one and
  the offset is \(c=(3D+1)/2>0\). As long as \(c\) is even,
  choose the lower-count endpoint even, replacing \(c\) by \(c/2\)
  without changing the count gap. At the first odd \(c\), choose
  the lower-count endpoint odd. This returns the counts to equality
  with separation \((c-1)/2\le(3D-1)/4\).

All transition identities and the strict descent inequalities are kernel
proved. Each prescribed bit has conditional probability one half.
Along the prescribed return path, separation decreases by a factor at
most \(3/4\). Since \((3/4)^4<1/2\), from \(D\le R\) it reaches
zero within \(M=4\cdot336=1344\) return cycles. Each cycle uses at
most 338 bits: in the odd case \(c<2^{337}\), followed by its finite
halving run and the return bit. Hence the probability of fusion within
those \(M\) cycles is at least
\[
                              p=2^{-454272}.            \tag{8}
\]

Starting within \(D\le R\), iterating (7) for \(M\) cycles gives
\[
 \mathbb EV(D_M)\le1093120+6404\frac{512}3<2186070.
\]
If fusion has not occurred, wait until the chain next reaches \(D\le R\)
and start another attempt. The drift bound shows that the conditional
expected length of an attempt, including this return to the finite set,
is at most \(1344+2186070=2187414\). Every attempt succeeds with
conditional probability at least \(p\). Summing the geometric upper
bound on the probability that attempt \(j\) is reached proves, from
initial separation one,
\[
 \boxed{\mathbb EN\le C_*:=2187414\,2^{454272}<\infty,}  \tag{9}
\]
where \(N\) is the number of count-return cycles until balanced fusion.
This argument does not assume independence of the attempts or a bounded
physical duration for a return cycle.

## 5. Consequences for the actual residue laws

Every departure from zero belongs to one of the \(N\) return cycles.
Summing (1) therefore gives the all-depth written bound
\[
        \boxed{2^{-t}\sum_{0\le r<2^t}|a_t(r)-a_t(r+1)|\le C_*.}     \tag{10}
\]
Conditioning on either initial parity gives at most \(2C_*\).
This bounds the full gap, including all its restarts. The constant is
deliberately very large; the finite numerical moments are not used to
guess it.

Let \(T\) be the physical clock of balanced fusion. From (4), uniformly
at the start of every still-needed return cycle,
\[
                     \mathbb E\min(\tau,H)\le21H^{4/5}.
\]
The event that cycle \(j\) is needed is determined before it starts.
Conditional expectation and the nonnegative sum formula thus give
\[
 \mathbb E\sum_{j\le N}\min(\tau_j,H)\le21C_*H^{4/5}.
\]
If \(T>H\), this sum is at least \(H\). Markov's inequality proves
\[
              \boxed{1-p_H=\Pr(T>H)\le21C_*H^{-1/5}.}   \tag{11}
\]
For either conditioned first parity, the bound is twice as large. Thus
balanced coalescence has density one in these coherent full-period laws.
The earlier \(H^{-1/2}\) lower bound is compatible with (11); the
physical mean coalescence clock is still infinite.

Finally use the existing [actual-annulus energy cap](COALESCENCE-ENERGY-CAPS.md),
\(e_{s,k}\le\tfrac12(1-p_{k+1}^{(0)})\), and its geometric tail.
For \(J(s)=\lceil121s/50\rceil\), (11) yields
\[
\begin{split}
 E_s
 &\le21C_*\sum_{h=1}^{J(s)}h^{-1/5}+\frac{23}4\\
 &\le\boxed{\frac{105}4 C_*J(s)^{4/5}+\frac{23}4}.       \tag{12}
\end{split}
\]
In particular \(E_s=O(s^{4/5})=o(s)\). This is an actual-energy upper
bound using the actual source intervals, with a written probability input.
The previous smaller numerical linear bound remains available. Neither
bound implies a bounded energy subsequence or excludes an escaping orbit.

## 6. Verification boundary

Run `python3 verify_count_return_control.py`. The
[record](../results/count-return-control/verification.json) distinguishes
the twelve new kernel roots, independent exact finite checks, and the
written arguments (2)--(12). It revalidates the previous energy-cap and
reversal-persistence records without rewriting them.

The first-return clock tail, stopped fractional moments, finite-set
return argument, probabilistic bounds, and real energy summation are
**not complete Lean formalizations**. Their proofs are provided above;
finite distributions cannot establish their all-depth assertions.
No external density or coalescence package is needed for these bounds.
The original goal of proving or disproving positive-integer Collatz
remains active.
