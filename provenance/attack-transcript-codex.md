# Attack run
- problem: 875
- backend: codex
- date: 20260709-224805
- tag: ratio-wide-window

## Output

The full problem remains unresolved, but the proposed wide-window route yields a rigorous partial result: Mazur’s quotient window is not the bottleneck, scalar carry blocks necessarily have quadratic radix, and straightforward staggered lifts of the Mazur block are rigid.

The problem is still listed as open, and the forum explicitly distinguishes the known absolute-gap construction from the ratio question. [Erdős Problem #875](https://www.erdosproblems.com/875), [discussion thread](https://www.erdosproblems.com/forum/thread/875?order=newest).

## 1. Precise formulation

For a finite set \(B\subset\mathbb Z\), write

\[
\Delta_t(B)=
\left\{
\sum_{x\in U}x-\sum_{x\in V}x:
U,V\subseteq B,\ |U|-|V|=t
\right\}.
\]

An infinite \(A=\{a_1<a_2<\cdots\}\subset\mathbb N\) is admissible exactly when

\[
0\notin\Delta_t(A)
\qquad(t\ne0),
\]

where every difference uses finite subsets.

The ratio subproblem asks whether an admissible \(A\) can satisfy

\[
\frac{a_{n+1}}{a_n}\longrightarrow1.
\]

I attack the construction direction, specifically the proposed overlapping scalar-carry mechanism.

For a finite \(C\subset\mathbb Z\), an integer \(Q>0\), and \(U\ge0\), define the local property

\[
\mathcal L_U(C,Q):
\quad
Y\in\Delta_t(C),\quad
Y=Qw-u,\quad |u|\le U
\ \Longrightarrow\
t=w-u.
\]

There is no separate restriction on \(w\).

Mazur’s published local lemma proves a weaker version for

\[
C_m=\{1+i(m+1):0\le i<m\},\qquad
Q_m=m^2+m+1,
\]

under \(|u|<m/4\) and \(|w|<m/2\). See the source [reference note](https://github.com/lechmazur/erdos_875/blob/main/docs/reference/admissible_carry_note_erdos875.tex).

## 2. Sharp local theorem for the Mazur AP

### Proposition 1

For every \(m\ge1\),

\[
\mathcal L_{\lceil m/2\rceil}(C_m,Q_m)
\]

holds. This is sharp: \(\mathcal L_{\lceil m/2\rceil+1}(C_m,Q_m)\) fails.

In particular, the \(w\)-window can be removed entirely, while the carry radius improves from approximately \(m/4\) to the sharp value \(m/2\).

### Proof

Put

\[
d=m+1,\qquad Q=md+1=m^2+m+1,
\qquad L=\frac{m(m+1)}2.
\]

The \(i\)-th element of \(C_m\) can be written as

\[
c_i=1+di=Q-d(m-i).
\]

After cancelling the common part of two subsets, write

\[
Y=\sum_{i=0}^{m-1}\varepsilon_i c_i,
\qquad \varepsilon_i\in\{-1,0,1\}.
\]

Let

\[
t=\sum_i\varepsilon_i,\qquad
z=\sum_i(m-i)\varepsilon_i.
\]

Then

\[
Y=Qt-dz,\qquad |z|\le L.
\]

Suppose \(Y=Qw-u\), and set \(v=w-t\). Then

\[
Qv=u-dz.
\]

Since \(Q\equiv1\pmod d\),

\[
v\equiv u\pmod d,
\]

so \(v=u+\ell d\) for some \(\ell\in\mathbb Z\). Substitution gives

\[
z=-mu-\ell Q. \tag{1}
\]

Let \(r=\lceil m/2\rceil\). If \(|u|\le r\) and \(\ell\ne0\), then

\[
|z|
=|mu+\ell Q|
\ge Q-m|u|
\ge Q-mr.
\]

A parity calculation gives

\[
Q-mr>L.
\]

Indeed:

- If \(m=2h\), then \(Q-mr-L=h+1>0\).
- If \(m=2h+1\), then \(Q-mr-L=1\).

This contradicts \(|z|\le L\). Hence \(\ell=0\), so \(v=u\). Since \(v=w-t\),

\[
t=w-u.
\]

That proves \(\mathcal L_r\).

For sharpness, take

\[
u_0=r+1,\qquad z_0=Q-mu_0.
\]

Directly, \(0\le z_0\le L\). Every integer in \([0,L]\) is a subset sum of \(\{1,\dots,m\}\), so choose \(\varepsilon_i\in\{0,1\}\) satisfying

\[
\sum_i(m-i)\varepsilon_i=z_0.
\]

In (1), choose \(\ell=-1\). Then \(v=u_0-d\ne u_0\), and with \(w=t+v\),

\[
Y=Qw-u_0,
\]

but \(t\ne w-u_0\). Thus the next carry radius fails. ∎

An exhaustive check for \(m\le12\) independently found the first bad value at \(|u|=\lceil m/2\rceil+1\), matching the proof.

## 3. Containment-free closure

The previous theorem removes another apparent obstruction.

Call \((A,M)\) weakly carry-good if

\[
D\in\Delta_T(A),\quad D=Mq
\quad\Longrightarrow\quad T=q.
\]

Unlike the published definition, this does not require \(A\subset[1,M)\).

### Proposition 2

Let \((A,M)\) be weakly carry-good, let \(N=|A|\), and suppose

\[
N\le \left\lceil\frac{k}{2}\right\rceil,
\qquad A\cap MC_k=\varnothing.
\]

Then

\[
\bigl(A\cup MC_k,\;MQ_k\bigr)
\]

is weakly carry-good.

### Proof

Let

\[
D=D_A+MY=MQ_kq,
\]

where

\[
D_A\in\Delta_{T_A}(A),\qquad
Y\in\Delta_t(C_k).
\]

Then

\[
D_A=M(Q_kq-Y)=Me
\]

for an integer \(e\). Weak carry-goodness of \((A,M)\) gives

\[
e=T_A.
\]

Therefore

\[
|e|=|T_A|\le |A|=N\le\left\lceil\frac{k}{2}\right\rceil.
\]

Also

\[
Y=Q_kq-e.
\]

Proposition 1, with \(u=e\) and \(w=q\), gives

\[
t=q-e.
\]

Consequently,

\[
T_A+t=e+(q-e)=q.
\]

Thus the enlarged pair is weakly carry-good. ∎

This is a genuine simplification of the published closure mechanism:

- no hypothesis \(A\subset[1,M)\);
- no estimate involving \(\sum A/M\);
- no separate quotient bound;
- the necessary block size drops from approximately \(4|A|\) to \(2|A|\).

It does not solve the geometry: the standard \(C_k\) still satisfies \(\max C_k<Q_k\), so the usual induction remains non-overlapping.

## 4. Universal quadratic wall for scalar carry blocks

The strongest reduction is independent of the AP structure.

### Proposition 3

Suppose \(C\) is a \(k\)-element set and \(Q>0\) satisfies the exact scalar-carry property

\[
Y\in\Delta_t(C),\quad Y=Qw
\quad\Longrightarrow\quad t=w. \tag{2}
\]

Then

\[
Q\ge \left\lfloor\frac{k^2}{4}\right\rfloor+1. \tag{3}
\]

### Proof

Define

\[
D=C-Q=\{c-Q:c\in C\},
\]

and let \(\operatorname{FS}(D)\) denote the set of distinct subset sums of \(D\), including \(0\).

Take two subsets \(U,V\subseteq D\) whose sums are congruent modulo \(Q\). Regard \(U,V\) as the corresponding index subsets of \(C\). Then

\[
\sum_{u\in U}u-\sum_{v\in V}v=Qr
\]

for some \(r\in\mathbb Z\), while

\[
\sum_{c\in U}c-\sum_{c\in V}c
=
Q\bigl(r+|U|-|V|\bigr).
\]

By (2), its quotient by \(Q\) must equal its cardinality defect \(|U|-|V|\). Hence \(r=0\), so the two subset sums of \(D\) were equal as integers.

Therefore reduction modulo \(Q\) is injective on the set of distinct values \(\operatorname{FS}(D)\), giving

\[
|\operatorname{FS}(D)|\le Q. \tag{4}
\]

Bhanja and Pandey’s sharp lower bounds for subset sums of arbitrary finite integer sets imply that every \(k\)-element \(D\subset\mathbb Z\) satisfies

\[
|\operatorname{FS}(D)|
\ge
\left\lfloor\frac{k^2}{4}\right\rfloor+1.
\]

This is Corollary 9 at \(\alpha=0\), obtained from their Theorem 7 and Corollary 8; see J. Bhanja and R. K. Pandey, “On the minimum size of subset and subsequence sums in integers” ([published paper](https://comptes-rendus.academie-sciences.fr/mathematique/item/10.5802/crmath.361.pdf)).

Combining this with (4) proves (3). ∎

### Consequence

Any replacement block that retains the same scalar invariant necessarily has

\[
Q=\Omega(k^2).
\]

Thus the hoped-for scalar block with \(Q\asymp k^{2-\delta}\) cannot exist. Mazur’s quadratic radix is optimal in exponent for the entire scalar-carry framework, not merely for his AP.

This does not prove the exponent \(3+2\sqrt2\) optimal among all constructions. It proves that improving it through a subquadratic radix while retaining the scalar rule \(q=t\) is impossible.

## 5. Rigidity of staggered lifts

One natural attempt is to retain the Mazur residues while lifting elements by multiples of \(Q\):

\[
\widetilde c_i=c_i+Q\lambda_i.
\]

This would place different parts of the block beyond the next modulus.

### Proposition 4

Let \(m\ge4\). If

\[
\widetilde C=\{c_i+Q\lambda_i:0\le i<m\}
\]

satisfies the exact property \(\mathcal L_0\), then for some \(\lambda\in\mathbb Z\),

\[
\lambda_i=\lambda(m-i). \tag{5}
\]

If \(\widetilde C\) also satisfies \(\mathcal L_1\), then

\[
\lambda_i=0
\qquad\text{for every }i.
\]

### Proof sketch with all constraints explicit

For \(1\le j\le m-2\),

\[
c_j+c_{m-1}-c_{j-1}=Q.
\]

Its cardinality defect and quotient are both \(1\). After lifting, \(\mathcal L_0\) forces

\[
\lambda_{j-1}=\lambda_j+\lambda_{m-1}. \tag{6}
\]

Let \(\lambda=\lambda_{m-1}\). Equation (6) makes \(\lambda_j\) affine in \(j\).

For \(m\ge5\), the additional relation

\[
c_2+c_{m-2}-c_0=Q
\]

forces the intercept, giving exactly (5). For \(m=4\), the three relations

\[
c_1+c_3-c_0=Q,\qquad
c_2+c_3-c_1=Q,\qquad
c_1+c_2-c_0-c_3=0
\]

give the same conclusion.

Now consider the negative singleton involving the first element:

\[
-\widetilde c_0=-1-Q\lambda_0=Q(-\lambda_0)-1.
\]

Here \(t=-1\), \(u=1\), and \(w=-\lambda_0\). Property \(\mathcal L_1\) demands

\[
-1=-\lambda_0-1,
\]

so \(\lambda_0=0\). From (5), \(m\lambda=0\), hence \(\lambda=0\) and every lift vanishes. ∎

There is also an immediate duplicate-residue obstruction: an exact all-\(w\) scalar block cannot contain two distinct elements congruent modulo \(Q\). Their difference would be \(Qw\) with cardinality defect \(0\), forcing \(w=0\). Thus a union of \(Q\)-translated copies of the same AP fails before any quantitative analysis.

## 6. Interpretation

The proposed wide-window attack splits into three issues:

1. **Quotient range:** not an issue for the Mazur AP. Proposition 1 removes \(w\) completely.

2. **Radix cost:** intrinsically quadratic for every scalar-carry block, by Proposition 3.

3. **Geometric overlap:** the actual obstruction. Standard residues cannot be lifted nontrivially while retaining even unit-error, all-quotient scalar carry, by Proposition 4.

So the desired construction cannot come from merely proving Mazur’s existing AP lemma for larger \(w\), nor from stacking \(Q\)-translates of that AP.

A genuinely new mechanism must relax at least one of:

- the scalar invariant \(q=t\);
- the requirement that the local lemma hold for every quotient \(w\);
- reuse of the Mazur residue system;
- one-stage closure by a single modulus.

The most concrete next experiment is therefore a finite-window relation-lattice search. Given residues \(r_1,\dots,r_k\pmod Q\), carry radius \(U\), and actual quotient range \(W\), form

\[
\mathcal R_{U,W}
=
\operatorname{span}_{\mathbb Q}
\left\{
\varepsilon\in\{-1,0,1\}^k:
\sum_i\varepsilon_i r_i=Qw-u,\ 
|u|\le U,\ |w|\le W
\right\}.
\]

Any allowed lift vector must satisfy a corresponding affine system on this relation set. The useful candidates are those where:

- the carry equations are consistent;
- \(\mathcal R_{U,W}\) has substantial codimension, leaving geometric lift freedom;
- the lifted elements cover a long multiplicative interval;
- the resulting global construction proves that all actually occurring quotients lie inside \(W\).

Whether such finite-window freedom survives the global induction is `[SHAKY]`. Proposition 3 shows that an all-quotient scalar version will not.

## Verdict

- **CLAIM:** The Mazur AP local carry radius is exactly \(\lceil m/2\rceil\), with no quotient bound required. A containment-free closure follows using cardinality alone. Every all-quotient scalar carry block of size \(k\) has radix \(Q\ge\lfloor k^2/4\rfloor+1\). For the Mazur residue system, nontrivial \(Q\)-lifts are incompatible with unit-error all-quotient carry.
- **CONFIDENCE:** High for the four mathematical propositions; they have complete elementary proofs apart from the explicitly cited sharp subset-sum theorem.
- **GAPS:**
  - No construction with \(a_{n+1}/a_n\to1\).
  - The quadratic wall applies to scalar all-quotient carry, not vector-valued or carefully bounded-\(w\) invariants.
  - Different residue systems or genuinely multi-level local blocks remain possible.
  - `[SHAKY]` I have not established that these propositions are absent from all prior literature, only that they are not stated in the checked Mazur note or the supplied dossier.
- **NEXT:** Search finite-window residue systems by the rank/codimension of their protected relation lattice, then attempt a two-coordinate or vector-valued carry invariant if scalar lift freedom again collapses.
