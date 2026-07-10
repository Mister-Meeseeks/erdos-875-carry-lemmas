# Critique run (targeted: three write-up additions in candidates/875-note/note.tex)
- target: candidates/875-note/note.tex (provenance-flagged additions only)
- backend: codex
- date: 20260710-000237

## Output

Overall: addition 1 is refuted as an “exact” claim, although its displayed inequality is valid under the stated carry bound. Additions 2 and 3 survive complete verification.

## 1. Automatic quotient constant

Let
\[
S=\sum_{c\in C_m}c=\frac{m(m^2+1)}2,\qquad Q=m^2+m+1.
\]
If \(Y\in\Delta_t(C_m)\), then \(|Y|\le S\). Thus, assuming the hypothesis actually used in the remark, namely \(|u|\le m\),
\[
Q|w|=|Y+u|\le S+m,
\]
and hence
\[
|w|\le
\left\lfloor\frac{S+m}{Q}\right\rfloor.
\]
This evaluates to
\[
\left\lfloor\frac{S+m}{Q}\right\rfloor=
\begin{cases}
0,&m=1,\\
1,&m=2,\\
m/2-1,&m\ge4\text{ even},\\
(m-1)/2,&m\text{ odd}.
\end{cases}
\]
Therefore the proposed \(\lfloor m/2\rfloor\) bound is valid, but it is not exact for even \(m\ge4\).

The smallest decisive counterexample to exactness is \(m=4\):
\[
C_4=\{1,6,11,16\},\quad Q_4=21,\quad S=34.
\]
If \(|u|\le4\), then
\[
21|w|\le34+4=38,
\]
so \(|w|\le1\), whereas \(\lfloor m/2\rfloor=2\). Moreover \(w=1\) really occurs:
\[
-1-6+11+16=20=21\cdot1-1.
\]
Thus the actual maximum here is \(1\), not \(2\).

At the radius relevant to Proposition 1, \(|u|\le\lceil m/2\rceil\), the same argument gives
\[
|w|\le\left\lfloor\frac{m-1}{2}\right\rfloor,
\]
so \(2|w|<m\) automatically. Consequently the statement that even \(m\) can sit “just outside” the old strict window is based only on a loose bound, not on a realizable boundary quotient.

- VERDICT: REFUTED
- FATAL FLAWS:
  1. Calling \(\lfloor m/2\rfloor\) the “exact” constant is false; \(m=4\) has exact maximum \(1<2\).
  2. Without a bound on \(u\), the claim is false altogether: take \(Y=0\) and \(u=Qw\) for arbitrary \(w\). The proof establishes only the conditional statement \(|u|\le m\).
- SUSPICIOUS BUT NOT FATAL:
  1. The weaker inequality \(|w|\le\lfloor m/2\rfloor\) is correct under \(|u|\le m\).
  2. The claimed need for a one-unit quotient-window widening is unsupported; at the actual carry radius, all realizable quotients already satisfy the old strict window.

## 2. Attainment of the quadratic wall by flat blocks

Put \(D=C-Q=\{d_1,\dots,d_k\}\). If
\[
\sum_{d\in D}|d|<Q,
\]
then for any signed representation
\[
Y=\sum_i\varepsilon_i(Q+d_i)
   =Qt+\sum_i\varepsilon_i d_i,
\qquad t=\sum_i\varepsilon_i,
\]
the condition \(Y=Qw\) gives
\[
Q(w-t)=\sum_i\varepsilon_i d_i.
\]
The right side has absolute value strictly less than \(Q\), so it must be zero. Hence \(w=t\), proving the exact all-quotient property.

Now choose \(D\) to minimize \(\sum|d|\):

- With \(0\in D\), the minimum is \(\lfloor k^2/4\rfloor\).
- With \(0\notin D\), the minimum is \(\lfloor(k+1)^2/4\rfloor\).

Taking \(Q\) to be one greater than the appropriate minimum makes \(\sum|d|=Q-1\), so the preceding argument applies and equality in the wall follows.

Explicit extremizers are:

\[
\begin{array}{c|c|c}
&k=2h&k=2h+1\\ \hline
0\in D&
\{-(h-1),\ldots,h\}&
\{-h,\ldots,h\}\\
0\notin D&
\{-h,\ldots,-1,1,\ldots,h\}&
\{-h,\ldots,-1,1,\ldots,h+1\}.
\end{array}
\]
With \(C=Q+D\), these even give positive-integer blocks. Thus both bounds really are attained for every \(k\).

For \(k=2\), the sharpened \(Q\notin C\) bound is indeed attained by
\[
D=\{-1,1\},\quad Q=3,\quad C=\{2,4\}.
\]

- VERDICT: SURVIVES
- FATAL FLAWS: none.
- SUSPICIOUS BUT NOT FATAL:
  1. “Smallest example” is literally inaccurate unless degenerate \(k=1\) blocks are being silently excluded. For example, \(C=\{1\},Q=2\) attains the \(Q\notin C\) bound at \(k=1\).
  2. The example \(\{2,4\},Q=3\) attains the stronger \(Q\notin C\) bound, not the first bound at equality; for \(k=2\), the first bound is attained by \(C=\{2,3\},Q=2\).
- VERIFICATION COVERAGE: The flat-block implication, both extremal \(\ell^1\) values, all four parity constructions, positivity, distinctness, and the small examples were checked in detail; nothing was skimmed.

## 3. The \(m=3\) staggered-lift example

For \(m=3\),
\[
(c_0,c_1,c_2)=(1,5,9),\qquad Q=13.
\]
A signed relation modulo \(13\) has the form
\[
\varepsilon_0+5\varepsilon_1+9\varepsilon_2\equiv0\pmod{13},
\qquad \varepsilon_i\in\{-1,0,1\}.
\]
Because the expression lies in \([-15,15]\), it can only be \(0,\pm13\). Directly solving gives exactly
\[
(0,0,0),\qquad (-1,1,1),\qquad (1,-1,-1).
\]
Thus the only nontrivial relation is
\[
c_1+c_2-c_0=13.
\]

After lifting, this becomes
\[
\widetilde c_1+\widetilde c_2-\widetilde c_0
 =13(1+\lambda_1+\lambda_2-\lambda_0).
\]
Its cardinality defect is \(1\), so \(\mathcal L_0\) holds precisely when
\[
1+\lambda_1+\lambda_2-\lambda_0=1,
\]
or
\[
\lambda_0=\lambda_1+\lambda_2.
\]
The converse follows because the enumeration above exhausted every signed relation divisible by \(13\). Hence the asserted two-parameter classification is exact.

The example \((1,1,0)\) satisfies the equation but is not of the form
\(\alpha(3,2,1)\), so Proposition 4(ii) cannot be extended to \(m=3\).

In fact the threshold is also necessary for part (iii): for every \(s\),
\[
\lambda=(0,s,-s)
\]
satisfies \(\mathcal L_1\). Enumerating the relations with \(|u|\le1\) shows that all of them have \(\varepsilon_1=\varepsilon_2\), so the lift contribution \(13s(\varepsilon_1-\varepsilon_2)\) vanishes. Thus nontrivial unit-radius lifts exist at \(m=3\) as well.

- VERDICT: SURVIVES
- FATAL FLAWS: none.
- SUSPICIOUS BUT NOT FATAL:
  1. The written example \((1,1,0)\) establishes sharpness specifically for Proposition 4(ii), not by itself for every part of Proposition 4. The broader threshold statement is nevertheless true, as witnessed for part (iii) by \((0,s,-s)\).
- VERIFICATION COVERAGE: All \(27\) signed coefficient patterns were reduced analytically to the three modular relations above; necessity, sufficiency, the example, and the unit-radius extension were checked in detail.
