# Literature check (gate 3): #875 carry-lemma bundle

- **Candidate:** `candidates/875-carry-lemma-bundle.md` (four propositions from
  `problems/875/runs/20260709-224805-codex-attack-ratio-wide-window.md`)
- **Check date:** 2026-07-09/10 (UTC)
- **Method:** direct read of both cited primary sources in full (Mazur note LaTeX
  source + companion Lean repo; Bhanja–Pandey published PDF), full read of the
  flagged-unread Nicolas Astérisque paper, fresh browser-UA snapshots of the
  erdosproblems.com #875 and #874 pages + forum threads, GitHub commit-history
  check of the Mazur repo, arXiv API sweeps (math.NT, sorted by date), Semantic
  Scholar citation-trail queries on ENS 1991 / Deshouillers–Freiman 1995 /
  Bhanja–Pandey 2022, and ~10 targeted web searches per the technique list in the
  tasking. All fetched artifacts cached in the session scratchpad.

## OVERALL VERDICT

**PRIOR ART: NONE FOUND for all four propositions as stated.** One proof
*ingredient* of Prop 3 (the quadratic subset-sum lower bound, and the
injectivity-plus-counting scheme generally) is standard and has multiple named
precedents that MUST be cited when posting — but no prior statement of any of
the four propositions, nor anything equivalent or stronger, was located.

---

## 1. Direct-source verification

### 1a. Mazur/GPT-5.5 note (the object being sharpened) — READ IN FULL [verified]

Source: LaTeX at
`https://github.com/lechmazur/erdos_875/blob/main/docs/reference/admissible_carry_note_erdos875.tex`
(fetched raw, 40,282 bytes, read line-by-line; PDF is the same document). Lean
repo tree, `AdmissibleCarry/LocalCarry.lean`, `LocalRange.lean`, and
`docs/LEMMA_INDEX.md` also fetched and checked.

Findings, item by item against our four propositions:

- **Carry radius.** Their Lemma 2 ("local carry") is stated with strict windows
  `|u| < m/4` **and** `|w| < m/2` — exactly as our dossier records. The proof's
  wraparound exclusion uses both windows (their `I = mw−1` vs
  `I ≥ m(m−1)/2 − (a−1)(m−1)` clash, with `L−R = m²/4 + m/2 + a > 0`). There is
  **no sharpness statement, no claim at radius m/2, and no version without the
  quotient window** anywhere in the note.
- **Lean repo agrees:** `LocalCarry.lean` hypotheses are literally
  `4 * u.natAbs < m` (`USmall`/`ZLtQuarter`) and `2 * w.natAbs < m`
  (`WSmall`/`ZLtHalf`); `LEMMA_INDEX.md` lists nothing sharper. So Prop 1's
  sharp radius `⌈m/2⌉` with the w-window removed is strictly beyond both the
  note and the formal artifact.
- **Closure.** Their Lemma 3 ("carry closure") requires **both** the
  containment `A ⊂ [1,M)∩ℕ` (part 1 of the carry-good definition) and the
  quantitative hypothesis `Σ(A)/M < k/4`; the proof uses positivity of `A` to
  get `|D_A| ≤ Σ(A)` and the `Σ(A′)/M′ < k/2` estimate to bound the quotient
  `|q|`. Our Prop 2 (weak carry-goodness, cardinality-only hypothesis
  `N ≤ ⌈k/2⌉`, no containment, no Σ/M estimate, no quotient bound) appears
  nowhere. (Block-size accounting: their chain effectively needs
  `k > 4·(Σ(A)/M)` where `Σ(A)/M` is bounded through `|T_A| ≤ N` — the "~4|A|
  vs ~2|A|" comparison in the candidate summary is a fair reading.)
- **Remark 4 ("Possible improvements") — checked specifically.** It says only:
  a replacement block would need a compatible carry lemma, controlled first
  element, controlled maximum, small internal gaps, and a small edge gap; notes
  `Q_k − max C_k = k+1` matches the internal spacing; concludes improvement
  "appears to require a more radical carry-compatible local structure." It
  contains **no lower bound on the radix Q** (Prop 3 answers a question Remark
  4 leaves fully open), **nothing about lifts or translates of blocks** (Prop
  4's territory), and no sharpness analysis. The other remarks (1: prefix
  changes; 2: parameter choice; 3: counting caution) are likewise disjoint from
  all four propositions.
- **Repo activity:** last commit 2026-05-09 ("pdf"); 14 commits total, all
  2026-05-07 to 2026-05-09. No follow-up work, no forks with new math found.

**Conclusion 1a: the direct source contains none of Props 1–4, in any form.**

### 1b. Bhanja–Pandey (Prop 3's cited input) — READ IN FULL [verified]

J. Bhanja, R. K. Pandey, *On the minimum size of subset and subsequence sums in
integers*, C. R. Math. Acad. Sci. Paris **360** (2022), 1099–1111,
doi:10.5802/crmath.361 (open access; PDF fetched and converted).

- **Corollary 9 (exact statement):** Let `k ≥ 2`, `A` a set of `k` integers,
  `α ∈ [0,k]`. If `0 ∉ A` then `|Σ_α(A)| ≥ ⌊(k+1)²/4⌋ − α(α+1)/2 + 1`; if
  `0 ∈ A` then `|Σ_α(A)| ≥ ⌊k²/4⌋ − α(α−1)/2 + 1`. Here `Σ_0(A)` is the set of
  all subset sums including the empty sum — i.e. `FS(A)`.
- **At α = 0:** both cases give `|FS(D)| ≥ ⌊k²/4⌋ + 1` for every `k`-element
  integer set `D` (mixed signs allowed, `0 ∈ D` allowed), since
  `⌊(k+1)²/4⌋ ≥ ⌊k²/4⌋`. **The citation in the attack run is correct in
  substance.** (For `k = 2` with `0 ∉ D`, Case 1 is verified directly in their
  proof; the corollary's floor `k ≥ 2` matches our use since Prop 3 is trivial
  for `k ≤ 1`.)
- **Citation nuance to fix when posting:** the run says Cor 9 is "obtained from
  their Theorem 7 and Corollary 8." In the paper, Cor 9's proof runs through
  **Theorem 4 + Theorem 7** (case `0 ∉ A`) and the `A′ = A\{0}` reduction (case
  `0 ∈ A`); Corollary 8 is the parallel statement with `0 ∈ A` but is not the
  stated proof path of Cor 9. Cite "Corollary 9 (via Theorems 4 and 7)".
- **Their Remark 10:** the α = 0 and α = 1 cases of Cor 9 are **optimal**, and
  the α = 1 case was **already proved by Nathanson** (Trans. AMS 347 (1995),
  1409–1418; their [18, Theorem 3], see their Remark 6). Two consequences:
  (i) the "independent elementary proof of the subset-sum bound" added by the
  gate-2 critique is a re-derivation of an essentially known result and must be
  presented as such (cite Nathanson 1995 and Bhanja–Pandey 2022 even when
  inlining the proof); (ii) the counting step of Prop 3 cannot be improved —
  any radix below `⌊k²/4⌋+1` must break the injectivity step, which delimits
  Prop 3 sharply.
- **Free strengthening available:** when `Q ∉ C` (so `0 ∉ D = C − Q`), Cor 9's
  first case gives `|FS(D)| ≥ ⌊(k+1)²/4⌋ + 1`, slightly improving Prop 3's
  constant in that (typical) case. Worth a remark in the write-up.

---

## 2. Per-proposition verdicts

### Prop 1 (sharp local carry lemma, radius ⌈m/2⌉, no quotient window)

**PRIOR ART: NONE FOUND.**

- Not in the Mazur note or Lean repo (§1a above — the only documents in
  existence about this two-month-old object).
- Not on the #875 forum thread (7 comments, none mathematical beyond the
  original announcement + natso26's Lean screening; last activity 11 May 2026)
  or the #874 thread (zero comments).
- Neighboring literatures checked for anything equivalent under renaming:
  sum-distinct/Conway–Guy sets, `B_h[g]` sets, dissociated sets, modular
  distinct-subset-sums (Cambie–Gao–Kim–Liu, arXiv:2308.03748), restricted-digit
  ("no-carry") constructions of `B_h` sets, and the carries literature
  (Diaconis–Shao–Soundararajan; Monopoli–Ruzsa arXiv:1506.08869). The classical
  no-carry digit trick (digits < b/h in base b ⇒ h-fold sums add digit-wise)
  is the distant ancestor of the whole carry framework, but nothing in these
  literatures states or implies a sharp radius for cardinality-graded
  differences of the AP block `C_m` mod `m²+m+1` — the object itself did not
  exist before May 2026. The modulus `m²+m+1` also appears in Singer difference
  sets (Sidon sets), but that concerns pairwise differences, not graded subset
  sums; no transferable statement found.
- ENS 1991 citation trail (Semantic Scholar): 4 indexed citations, all
  pre-2019, none relevant. Deshouillers–Freiman 1995: 4 indexed citations,
  likewise irrelevant.

### Prop 2 (containment-free closure, cardinality-only hypothesis)

**PRIOR ART: NONE FOUND.**

- The carry-good closure mechanism exists only in the Mazur note (Lemma 3),
  which requires both `A ⊂ [1,M)` and `Σ(A)/M < k/4` (§1a). No other document
  discusses carry-good pairs at all (web + arXiv searches for the terminology
  and for reformulations came back empty; the term "carry lemma" in Lean/Erdős
  contexts hits only the unrelated Kummer-carry work on #728).
- Caveat for the write-up (already in the candidate's presentation-fixes list):
  achievable quotients in the weak setting are automatically `≲ m/2 + O(1)`, so
  "removes the quotient window" should stay tempered exactly as planned.

### Prop 3 (quadratic wall: all-quotient scalar carry ⇒ Q ≥ ⌊k²/4⌋+1)

**PRIOR ART: NONE FOUND for the statement; the proof technique is standard
(COMPARABLE at ingredient level) and must be attributed.**

- No prior statement bounding the radix of a carry-compatible block was found
  anywhere (it could not predate May 2026 in this exact form, and no generic
  theorem specializing to it was located).
- The two ingredients are individually known, with a substantial pedigree:
  1. *Injectivity/pigeonhole:* "distinct subset sums mod Q ⇒ Q ≥ |FS|" is
     folklore and is the engine of the modular Erdős distinct-subset-sums
     literature — Cambie–Gao–Kim–Liu, *The Erdős distinct subset sums problem
     in a modular setting*, arXiv:2308.03748 (sumset-distinct sets mod
     `N = 2ⁿ+t`). Prop 3's reduction (exact scalar carry ⇒ reduction mod Q is
     injective on `FS(C−Q)`) is a new observation about a new object, but the
     scheme is this standard one.
  2. *Quadratic counting:* quadratic lower bounds for subset sums are classical
     — Olson 1968 (`Z_p`), Erdős–Heilbronn; sharp `F_p` version Balandraud
     (Israel J. Math. 188 (2012) / arXiv:1702.06419); general abelian groups
     DeVos–Goddyn–Mohar–Šámal, *A quadratic lower bound for subset sums*, Acta
     Arith. 129 (2007), arXiv:math/0612045 (`|Σ(A)| ≥ |H| + |A\H|²/64`, H the
     stabilizer) — note this route would already give `Q = Ω(k²)` with a worse
     constant by essentially the same argument applied inside `Z_Q`; integer
     case Nathanson 1995 (α=1) and Bhanja–Pandey 2022 (α=0, the form used, and
     optimal per their Remark 10).
- Similar injectivity-plus-counting arguments in the complete-sequences /
  covering-systems / EGZ neighborhoods were searched for as instructed; the
  standard instances found are the ones above (zero-sum-free subset sums,
  modular sum-distinct sets). Nothing closer.
- Scope note from gate 2 stands and is consistent with everything found: the
  wall is proved only for the exact ALL-quotient scalar invariant; no literature
  bears on bounded-window invariants.

### Prop 4 (rigidity of staggered Q-lifts of the Mazur residue system)

**PRIOR ART: NONE FOUND.**

- Nothing exists on lifts/translates of AP blocks in modulus-tower
  constructions for admissible sets (searched under lifts, translates, residue
  systems, mixed-radix towers, digit constructions).
- Closest work *in spirit* (should be cited as context, not as overlap):
  Monopoli–Ruzsa, *Carries and the arithmetic progression structure of sets*,
  arXiv:1506.08869 (building on Diaconis–Shao–Soundararajan): digit sets mod
  `m²` inducing minimal carry behavior are forced to be arithmetic progressions
  up to linear maps — an "AP structure is rigid under carry constraints"
  theorem. Their setting is two-summand addition carries with no cardinality
  grading, no `Q`-lifts of a fixed residue system, and no admissibility; no
  statement transfers.
- The duplicate-residue observation in §5 of the run (two elements congruent
  mod Q kill exact scalar carry) is elementary and safe to state without
  attribution.

### Nicolas, *Stratified sets*, Astérisque 258 (1999), 205–215 — flagged unread; NOW READ IN FULL

**No overlap with any of the four propositions or with the wide-window
direction.** Content: "stratified" = every t-element sum below every
(t+1)-element sum (interval separation, the within-block/Straus regime);
main theorems are a bijection between stratified sets with max N and partitions
of N (via Durfee squares), the count `S(N) = p(N)`, an improved lower bound for
the number a(N) of admissible sets, and reformulated conjectures from ENS 1991
about maximal admissible sets (stratified/quasistratified/odd-element
classification). No carry arguments, no moduli, no radix bounds, no lifts, no
towers. The only carry-adjacent sentence is a one-line suggestion (p. 206) that
stratification generalizes to APs — e.g. odd-element sets with t vs t+2
separation are admissible by parity — deferred to a future paper (none found;
his 2005 partitions survey is the only later related item indexed). This is a
congruence-reads-off-cardinality-mod-2 observation, strictly weaker than what
is already in the Mazur note, and touches none of Props 1–4.

---

## 3. Recent activity (post-2026-06-20)

- **#875 forum thread** (fresh browser-UA snapshot, ordered newest): 7
  comments; the newest is 11 May 2026 (MalekZ harness chat). The Feb-2026
  GPT-5.2 reference comment and the May-2026 Mazur announcements are all
  previously seen. **Nothing new.** Problem still marked OPEN with "Partial"
  comment-activity flag; no formalisation on the site (formal-conjectures issue
  #995 still the open route).
- **#874 forum thread**: zero comments.
- **Mazur repo**: frozen since 2026-05-09 (commit log checked via GitHub API).
- **arXiv**: math.NT sweeps for "admissible set" (all recent hits are
  prime-tuple/Shimura-variety homonyms), "Erdős problem 875", carry/admissible
  combinations, and gap-exponent phrasings — nothing in the last 3 weeks (or
  indeed since the May note) touching this problem family. The recent
  Erdős-problems land-rush items found (#728 writeup, #1196 Tao, van der
  Waerden, etc.) are unrelated.

---

## CLOSEST WORK (3 nearest overall)

1. **GPT-5.5 Pro & L. Mazur, *On an absolute-gap variant of Erdős Problem
   #875*** (note + Lean repo, May 2026,
   github.com/lechmazur/erdos_875) — proves the windowed (m/4, m/2)
   non-sharp carry lemma and a closure needing containment + Σ/M; our bundle
   sharpens the radius to the exact value, deletes the containment and Σ/M
   hypotheses, and adds impossibility results (Props 3–4) their Remark 4 does
   not anticipate.
2. **J. Bhanja & R. K. Pandey, C. R. Math. 360 (2022) 1099–1111
   (doi:10.5802/crmath.361), with M. B. Nathanson, Trans. AMS 347 (1995)
   1409–1418 behind it** — supplies exactly the sharp `⌊k²/4⌋+1` counting input
   of Prop 3 (their Cor 9 at α=0; α=1 already in Nathanson); ours differs by
   the carry-to-injectivity reduction and the application (a radix lower bound
   for carry blocks), which they do not consider.
3. **F. Monopoli & I. Z. Ruzsa, *Carries and the arithmetic progression
   structure of sets*, arXiv:1506.08869 (after Diaconis–Shao–Soundararajan)** —
   the only prior "AP blocks are rigid under carry constraints in a two-level
   modulus" theorem; ours differs in every technical respect (cardinality-graded
   subset-sum invariants and Q-lifts of a fixed residue system vs two-summand
   addition carries) but shares the moral, so cite as context for Prop 4.

   (Honorable mention for Prop 3's scheme: DeVos–Goddyn–Mohar–Šámal, Acta
   Arith. 129 (2007) — the same injectivity+quadratic-counting logic in abelian
   groups, weaker constant; and Cambie–Gao–Kim–Liu arXiv:2308.03748 for the
   modular sum-distinct pigeonhole.)

## CONFIDENCE

**HIGH for Props 1, 2, 4; MEDIUM-HIGH for Prop 3.** Grounds: both direct
sources were read in full (not summarized), the central object is two months
old with a complete and frozen public paper trail (note + repo + forum, all
checked), the surrounding classical literature is tiny and its citation trail
was walked (ENS 1991 and DF 1995 have 4 indexed citations each, all checked by
title), and the flagged-unread Nicolas paper is now fully read. Prop 3 is rated
a notch lower only because its proof scheme is standard, so an unindexed
instance of "carry-type invariant ⇒ modulus ≥ quadratic" buried in the
zero-sum/complete-sequences literature cannot be excluded with certainty —
though none surfaced under many phrasings.

**What I could NOT access/perform:** MathSciNet and zbMATH (paywalled — the
main residual risk for Prop 3's technique-instance search); Google Scholar
citation graphs (Semantic Scholar's Astérisque/JTNB coverage is sparse);
Nathanson 1995 full text (AMS 403s even with browser UA — its content is taken
from Bhanja–Pandey's Remarks 6 and 10, which is sufficient for the attribution
duty but I could not transcribe his Theorem 3 verbatim); the Er98 Eger
proceedings volume; and Astérisque 258 articles other than DF2/Nicolas
(Chaimovich's dense-subset-sum algorithm paper in the same volume was
title-checked only).

## ACTION ITEMS FOR THE WRITE-UP (beyond the gate-2 presentation fixes)

1. Cite Nathanson 1995 alongside Bhanja–Pandey for the subset-sum bound, even
   with the elementary proof inlined ("well known; see [N95, Thm 3], [BP22,
   Cor 9 and Rem 10]; we include a proof for completeness").
2. Correct the Cor 9 provenance phrase ("via Theorems 4 and 7", not "Theorem 7
   and Corollary 8").
3. Optional: note the `⌊(k+1)²/4⌋+1` strengthening of Prop 3 when `Q ∉ C`, and
   that BP's optimality at α=0 shows the counting step is tight.
4. Cite Monopoli–Ruzsa (and DSS) as spiritual context for Prop 4, and
   DeVos–Goddyn–Mohar–Šámal / Cambie–Gao–Kim–Liu as the standard instances of
   the Prop 3 scheme — pre-empts the obvious referee/forum "isn't this just
   X?" replies.
