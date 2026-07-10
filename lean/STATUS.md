# Gate 4 status — Lean formalization of the #875 carry-lemma bundle

**Date:** 2026-07-09/10 session.
**Result: COMPLETE for the session targets — Prop 1 (both directions) and
Prop 2 are fully proven in Lean 4 / mathlib. Zero `sorry`s. Build is green.**

## What is formalized

All in namespace `Erdos875`, faithful to the statements in
`problems/875/runs/20260709-224805-codex-attack-ratio-wide-window.md`
(§2 Proposition 1, §3 Proposition 2), with the proof steps as verified by the
Gate-2 critique (`20260709-230529-claude-critique-of-...md`).

### `Erdos875/CarryLemma.lean` — Proposition 1 (sharp local carry lemma)

| Declaration | Content | Status |
|---|---|---|
| `IsSignedSum C t Y` | `Y ∈ Δ_t(C)`: `∃ U V ⊆ C`, `\|U\|−\|V\| = t`, `ΣU − ΣV = Y` | def |
| `mazurElt`, `mazurBlock m` | `C_m = {1 + i(m+1) : 0 ≤ i < m}` as `Finset ℤ` | def |
| `mazurQ m` | `Q_m = m² + m + 1` | def |
| `sum_mazurAP` | `Σ_{i∈S} c_i = Q·\|S\| − (m+1)·Σ_{i∈S}(m−i)` (paper step 1) | **proved** |
| `two_indexWeight_range` | `2·Σ_{i<m}(m−i) = m(m+1)` (the `L` bound, Gauss) | **proved** |
| `block_decomp` | `Y ∈ Δ_t(C_m) → Y = Q·t − (m+1)·z`, `2\|z\| ≤ m(m+1)` | **proved** |
| `carry_arith` | arithmetic core: paper steps 2–3 (`ℓ`-shift, eq. (1), `ℓ=0`) | **proved** |
| **`local_carry`** | **Prop 1 main direction**: `Y ∈ Δ_t(C_m)`, `Y = Q_m·w − u`, `2\|u\| ≤ m+1` ⟹ `t = w − u` (NO window on `w`) | **proved** |
| `local_carry_natAbs` | same with radius in the paper form `u.natAbs ≤ (m+1)/2` (`= ⌈m/2⌉` in ℕ) | **proved** |
| `exists_subset_Icc_sum` | every `n ≤ k(k+1)/2` is a subset sum of `{1,…,k}` | **proved** |
| **`local_carry_sharp`** | **Prop 1 sharpness**: for every `m ≥ 1`, a violation with `u.natAbs = (m+1)/2 + 1 = ⌈m/2⌉ + 1` | **proved** |

The radius hypothesis `|u| ≤ ⌈m/2⌉` is stated division-free as `2·|u| ≤ m+1`
(equivalent over ℤ; the `natAbs` corollary makes the `⌈m/2⌉` form explicit).
A note vs the paper: the parity case split of the paper's step 3 is not needed
in this form (`2·m·⌈m/2⌉ ≤ m(m+1) < 2Q − 2L` closes both parities at once);
the sharpness direction does use the parity split, as in the paper.

### `Erdos875/Closure.lean` — Proposition 2 (containment-free closure)

| Declaration | Content | Status |
|---|---|---|
| `WeaklyCarryGood A M` | `D ∈ Δ_T(A)`, `D = M·q` ⟹ `T = q` | def |
| `IsSignedSum.abs_defect_le` | `\|T\| ≤ \|A\|` | **proved** |
| `IsSignedSum.split` | signed sums split over disjoint unions | **proved** |
| `IsSignedSum.of_scaled` | signed sums over `M·C` are `M·(signed sum over C)` | **proved** |
| **`weaklyCarryGood_union`** | **Prop 2**: `(A,M)` weakly carry-good, `2\|A\| ≤ k+1`, `A ∩ M·C_k = ∅` ⟹ `(A ∪ M·C_k, M·Q_k)` weakly carry-good | **proved** |

Hypotheses match the paper: cardinality bound `|A| ≤ ⌈k/2⌉` only (stated
division-free as `2·|A| ≤ k+1`), disjointness, `M ≠ 0` (implicit in the paper
where `M` is a modulus ≥ 1), `k ≥ 1`. No containment `A ⊆ [1,M)`, no `ΣA/M`
estimate, no quotient window.

### Not formalized (out of scope per task priority)

- Prop 3 (quadratic wall `Q ≥ ⌊k²/4⌋+1`) — not started.
- Prop 4 (staggered-lift rigidity) — not started.

## Sorries / axioms

- `grep -rn sorry Erdos875/` → none.
- `#print axioms` on `local_carry`, `local_carry_natAbs`, `local_carry_sharp`,
  `weaklyCarryGood_union`, `carry_arith`, `block_decomp` → only the standard
  `propext`, `Classical.choice`, `Quot.sound` (see axiom audit below).

## Toolchain / build

Pinned to the same versions as Mazur's `lechmazur/erdos_875` repo, so the
mathlib olean cache applies (no mathlib compile needed):

- `lean-toolchain`: `leanprover/lean4:v4.30.0-rc2`
  (Lean 4.30.0-rc2, commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`)
- mathlib: tag `v4.30.0-rc2`, rev `5450b53e5ddc75d46418fabb605edbf36bd0beb6`
- elan 4.2.3 via Homebrew (`brew install elan-init`)

Build commands (from `tools/875/lean/`):

```bash
export PATH=$HOME/.elan/bin:/opt/homebrew/bin:$PATH
lake update          # first time only: fetches mathlib + deps
lake exe cache get   # first time only: downloads prebuilt mathlib oleans (~8300 files)
lake build           # builds Erdos875.CarryLemma, Erdos875.Closure, Erdos875
```

Full build of the two project files takes ~1–2 min on this machine (M-series
mac) once the cache is in; `lake update` + `cache get` took ~10 min.

## Relation to Mazur's formalization

Mazur's `LocalCarry.lean` proves the analogous lemma at weaker constants
(`4|u| < m` AND `2|w| < m`, his `local_carry_range`). `local_carry` here is
strictly stronger on both axes: radius `2|u| ≤ m+1` (sharp, by
`local_carry_sharp`) and **no `w` hypothesis at all**. His repo has **no
license file**, so no code was reused; definitions here are written fresh
against the paper statement (`Δ_t` via `Finset` pairs rather than his
`Sign3`-vector encoding — arguably closer to the paper's set-difference
definition). Statement-level faithfulness to the attack-run formulation was
the design constraint.

## Follow-up estimate

- Prop 3 (quadratic wall): the mod-Q injectivity argument + the critique's
  elementary subset-sum bound (`p` distinct positives give `≥ p(p+1)/2 + 1`
  subset sums, balanced-split minimization). Realistic effort: one focused
  session (the distinct-subset-sum counting over `Finset ℤ` is the fiddly
  part; everything else is arithmetic).
- Prop 4 (rigidity): linear-system bookkeeping over lifted blocks; also about
  one session, mostly `Finset`/index plumbing around eq. (6).
