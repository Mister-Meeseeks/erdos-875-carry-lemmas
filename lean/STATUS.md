# Gate 4 status — Lean formalization of the #875 carry-lemma bundle

**Date:** 2026-07-09/10 session.
**Result: COMPLETE for all four propositions. Props 1, 2, 3, and 4 (including
sharpness witnesses) are proven in Lean 4 / mathlib with zero `sorry`s.**

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

### `Erdos875/Barrier.lean` (Proposition 3: quadratic radix barrier)

| Declaration | Content | Status |
|---|---|---|
| `subsetSums D` | `FS(D) = { Σ_{x∈S} x : S ⊆ D }` | def |
| `mod_injOn_subsetSums`, `card_subsetSums_sub_le` | Lemma 4.1: `WeaklyCarryGood C Q` implies `s ↦ s % Q` injective on `FS(C − Q)` and `\|FS(C − Q)\| ≤ Q` | **proved** |
| `pos_subsetSums_card_ge`, `card_subsetSums_ge`, `card_subsetSums_ge_of_zero_not_mem` | Lemma 4.2: `\|FS(D)\| ≥ ⌊k²/4⌋ + 1`, and `≥ ⌊(k+1)²/4⌋ + 1` when `0 ∉ D` | **proved** |
| **`quadratic_radix_barrier`** | **Prop 3 general bound**: `Q ≥ ⌊\|C\|²/4⌋ + 1` | **proved** |
| **`quadratic_radix_barrier_not_mem`** | **Prop 3 `Q ∉ C` bound**: `Q ≥ ⌊(\|C\|+1)²/4⌋ + 1` | **proved** |
| **`quadratic_radix_barrier_sharp`**, **`quadratic_radix_barrier_not_mem_sharp`** | **Remark 4.5 sharpness**: positive Straus flat blocks attain both bounds for every `k ≥ 1` | **proved** |

### `Erdos875/Rigidity.lean` (Proposition 4: staggered-lift rigidity)

| Declaration | Content | Status |
|---|---|---|
| `LocalCarry C Q R` | All-quotient carry predicate at error radius `\|u\| ≤ R` | def |
| `no_repeated_residues` | Observation 5.1: `WeaklyCarryGood C Q` implies distinct residues mod `Q` | **proved** |
| `liftedElt`, `liftedBlock m lam` | `C̃_λ = {c_i + Q_m·λ_i : 0 ≤ i < m}` | def |
| **`mazurElt_mod_injOn`**, **`liftedBlock_card`** | **Prop 4(i)**: pairwise distinct residues mod `Q_m` and `\|C̃_λ\| = m` | **proved** |
| **`staggered_lift_weaklyCarryGood_iff`** | **Prop 4(ii)**: for `m ≥ 4`, `WeaklyCarryGood (liftedBlock m lam) (mazurQ m)` iff `∃ c, ∀ i < m, lam i = c·(m − i)` | **proved** |
| **`staggered_lift_localCarry1_eq_zero`** | **Prop 4(iii)**: for `m ≥ 4`, `LocalCarry (liftedBlock m lam) (mazurQ m) 1` implies `∀ i < m, lam i = 0` | **proved** |
| `staggered_lift_m3_localCarry0_counterexample`, `staggered_lift_m3_localCarry1_counterexample` | Remark 5.4: `m = 3` counterexamples showing `m ≥ 4` is sharp for both (ii) and (iii) | **proved** |

## Sorries / axioms

- `grep -rn sorry Erdos875/` -> none.
- `#print axioms` on `local_carry`, `local_carry_natAbs`, `local_carry_sharp`,
  `weaklyCarryGood_union`, `quadratic_radix_barrier`,
  `quadratic_radix_barrier_not_mem`, `quadratic_radix_barrier_sharp`,
  `quadratic_radix_barrier_not_mem_sharp`,
  `staggered_lift_weaklyCarryGood_iff`, and
  `staggered_lift_localCarry1_eq_zero` -> only `propext`, `Classical.choice`,
  `Quot.sound`.

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
lake build           # builds CarryLemma, Closure, Barrier, Rigidity, Erdos875
```

Full build of the four project modules takes ~1-2 min on an M-series Mac once
the mathlib cache is present.

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
