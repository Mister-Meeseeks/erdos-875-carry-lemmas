import Erdos875.CarryLemma

/-!
# Containment-free closure (Erdős #875, Proposition 2)

Proposition 2 of the candidate bundle: weak carry-goodness closes under
block extension by a scaled Mazur block, using ONLY the cardinality bound
`|A| ≤ ⌈k/2⌉` — no containment `A ⊆ [1, M)`, no `ΣA/M` estimate, no
quotient window.

* `WeaklyCarryGood A M`: every `D ∈ Δ_T(A)` with `D = M·q` has `T = q`.
* **`weaklyCarryGood_union`** (Prop 2): if `(A, M)` is weakly carry-good,
  `2·|A| ≤ k + 1` (i.e. `|A| ≤ ⌈k/2⌉`), and `A ∩ M·C_k = ∅`, then
  `(A ∪ M·C_k, M·Q_k)` is weakly carry-good.

## Proof outline (paper, as verified by the Gate-2 critique)

Split `D = D_A + M·Y` and `T = T_A + τ` along the disjoint union
(`IsSignedSum.split`, `IsSignedSum.of_scaled`). From `D = (M·Q_k)·q`:
`D_A = M·(Q_k·q − Y) = M·e`. Weak carry-goodness of `(A, M)` gives
`T_A = e`; the trivial bound `|T_A| ≤ |A| ≤ ⌈k/2⌉`
(`IsSignedSum.abs_defect_le`) feeds Proposition 1 (`local_carry`) with
`u = e`, `w = q` — the all-quotient form of Prop 1 is exactly what lets
`q` be unbounded — yielding `τ = q − e`, hence `T = e + (q − e) = q`.
-/

namespace Erdos875

open Finset

/-- `(A, M)` is *weakly* carry-good: `D ∈ Δ_T(A)` and `D = M·q` force the
quotient to equal the cardinality defect, `T = q`. No containment
`A ⊆ [1, M)` is required (hence "weak", versus the published definition). -/
def WeaklyCarryGood (A : Finset ℤ) (M : ℤ) : Prop :=
  ∀ ⦃T D q : ℤ⦄, IsSignedSum A T D → D = M * q → T = q

/-- The signed-sum defect is bounded by the ambient cardinality:
`|T| ≤ |A|` for `D ∈ Δ_T(A)`. -/
theorem IsSignedSum.abs_defect_le {A : Finset ℤ} {T D : ℤ}
    (h : IsSignedSum A T D) : |T| ≤ (A.card : ℤ) := by
  obtain ⟨U, V, hU, hV, ht, -⟩ := h
  have hUcard : U.card ≤ A.card := Finset.card_le_card hU
  have hVcard : V.card ≤ A.card := Finset.card_le_card hV
  rw [abs_le]
  constructor <;> omega

/-- Splitting a signed sum over a disjoint union into its two parts. -/
theorem IsSignedSum.split {A B : Finset ℤ} {T D : ℤ}
    (hAB : Disjoint A B) (h : IsSignedSum (A ∪ B) T D) :
    ∃ TA DA TB DB : ℤ, IsSignedSum A TA DA ∧ IsSignedSum B TB DB ∧
      T = TA + TB ∧ D = DA + DB := by
  classical
  obtain ⟨U, V, hU, hV, ht, hD⟩ := h
  have hUsplit : U = (U ∩ A) ∪ (U ∩ B) := by
    rw [← Finset.inter_union_distrib_left]
    exact (Finset.inter_eq_left.mpr hU).symm
  have hVsplit : V = (V ∩ A) ∪ (V ∩ B) := by
    rw [← Finset.inter_union_distrib_left]
    exact (Finset.inter_eq_left.mpr hV).symm
  have hUdisj : Disjoint (U ∩ A) (U ∩ B) :=
    hAB.mono Finset.inter_subset_right Finset.inter_subset_right
  have hVdisj : Disjoint (V ∩ A) (V ∩ B) :=
    hAB.mono Finset.inter_subset_right Finset.inter_subset_right
  have hUcard : U.card = (U ∩ A).card + (U ∩ B).card := by
    conv_lhs => rw [hUsplit]
    exact Finset.card_union_of_disjoint hUdisj
  have hVcard : V.card = (V ∩ A).card + (V ∩ B).card := by
    conv_lhs => rw [hVsplit]
    exact Finset.card_union_of_disjoint hVdisj
  have hUsum : ∑ x ∈ U, x = (∑ x ∈ U ∩ A, x) + ∑ x ∈ U ∩ B, x := by
    conv_lhs => rw [hUsplit]
    exact Finset.sum_union hUdisj
  have hVsum : ∑ x ∈ V, x = (∑ x ∈ V ∩ A, x) + ∑ x ∈ V ∩ B, x := by
    conv_lhs => rw [hVsplit]
    exact Finset.sum_union hVdisj
  refine ⟨((U ∩ A).card : ℤ) - ((V ∩ A).card : ℤ),
    (∑ x ∈ U ∩ A, x) - ∑ x ∈ V ∩ A, x,
    ((U ∩ B).card : ℤ) - ((V ∩ B).card : ℤ),
    (∑ x ∈ U ∩ B, x) - ∑ x ∈ V ∩ B, x,
    ⟨U ∩ A, V ∩ A, Finset.inter_subset_right, Finset.inter_subset_right,
      rfl, rfl⟩,
    ⟨U ∩ B, V ∩ B, Finset.inter_subset_right, Finset.inter_subset_right,
      rfl, rfl⟩,
    ?_, ?_⟩
  · rw [← ht, hUcard, hVcard]
    push_cast
    ring
  · rw [← hD, hUsum, hVsum]
    ring

/-- A signed sum over a scaled set `M·C` is `M` times a signed sum over `C`
(with the same defect). -/
theorem IsSignedSum.of_scaled {C : Finset ℤ} {M : ℤ} (hM : M ≠ 0) {T D : ℤ}
    (h : IsSignedSum (C.image (fun c => M * c)) T D) :
    ∃ Y : ℤ, IsSignedSum C T Y ∧ D = M * Y := by
  classical
  obtain ⟨U, V, hU, hV, ht, hD⟩ := h
  have hinj : Function.Injective (fun c : ℤ => M * c) :=
    mul_right_injective₀ hM
  obtain ⟨SU, hSUsub, hSU⟩ := exists_image_preimage hU
  obtain ⟨SV, hSVsub, hSV⟩ := exists_image_preimage hV
  refine ⟨(∑ x ∈ SU, x) - ∑ x ∈ SV, x,
    ⟨SU, SV, hSUsub, hSVsub, ?_, rfl⟩, ?_⟩
  · rw [← ht, ← hSU, ← hSV,
      Finset.card_image_of_injective SU hinj,
      Finset.card_image_of_injective SV hinj]
  · have hUsum : ∑ x ∈ U, x = M * ∑ x ∈ SU, x := by
      rw [← hSU, Finset.sum_image fun a _ b _ hab => hinj hab,
        Finset.mul_sum]
    have hVsum : ∑ x ∈ V, x = M * ∑ x ∈ SV, x := by
      rw [← hSV, Finset.sum_image fun a _ b _ hab => hinj hab,
        Finset.mul_sum]
    rw [← hD, hUsum, hVsum]
    ring

/-- **Proposition 2 (containment-free closure).** If `(A, M)` is weakly
carry-good, `|A| ≤ ⌈k/2⌉` (division-free: `2·|A| ≤ k + 1`), and
`A ∩ M·C_k = ∅`, then `(A ∪ M·C_k, M·Q_k)` is weakly carry-good.
Only the cardinality of `A` is used — no containment `A ⊆ [1, M)`,
no `ΣA/M` bound, no quotient window. -/
theorem weaklyCarryGood_union {k : ℕ} (hk : 1 ≤ k)
    {A : Finset ℤ} {M : ℤ} (hM : M ≠ 0)
    (hgood : WeaklyCarryGood A M)
    (hcard : 2 * A.card ≤ k + 1)
    (hdisj : Disjoint A ((mazurBlock k).image (fun c => M * c))) :
    WeaklyCarryGood (A ∪ (mazurBlock k).image (fun c => M * c))
      (M * mazurQ k) := by
  intro T D q hTD hDq
  -- split along the disjoint union
  obtain ⟨TA, DA, TB, DB, hA, hB, hTsplit, hDsplit⟩ := hTD.split hdisj
  -- the block part is M times a signed sum over C_k
  obtain ⟨Y, hY, hDB⟩ := hB.of_scaled hM
  -- D_A = M·e with e = Q_k·q − Y
  have hDA : DA = M * (mazurQ k * q - Y) := by
    rw [hDsplit, hDB] at hDq
    linear_combination hDq
  -- weak carry-goodness of (A, M): T_A = e
  have hTA : TA = mazurQ k * q - Y := hgood hA hDA
  -- cardinality bound: |e| = |T_A| ≤ |A| ≤ ⌈k/2⌉
  have habs : 2 * |TA| ≤ (k : ℤ) + 1 := by
    have h1 := hA.abs_defect_le
    have h2 : ((2 * A.card : ℕ) : ℤ) ≤ ((k + 1 : ℕ) : ℤ) := by
      exact_mod_cast hcard
    push_cast at h2
    linarith
  -- Prop 1 with u = e, w = q (all-quotient form: no bound on q needed)
  have hYeq : Y = mazurQ k * q - TA := by linarith [hTA]
  have hτ : TB = q - TA := local_carry hk hY hYeq habs
  -- assemble: T = T_A + τ = q
  rw [hTsplit, hτ]
  ring

end Erdos875
