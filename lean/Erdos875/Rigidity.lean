import Erdos875.Closure

/-!
# Rigidity of staggered lifts of the Mazur block (Erdős #875, Proposition 4)

This file formalizes Section 5 (Observation 5.1, Proposition 4(i)–(iii), and
Remark 5.4 `m = 3` threshold sharpness) of the note:

* `LocalCarry C Q R`: the all-quotient local carry invariant `ℒ_R(C, Q)`:
  `Y ∈ Δ_t(C)`, `Y = Q·w − u`, `|u| ≤ R` ⟹ `t = w − u`.
* **`no_repeated_residues`** (Observation 5.1): if `(C, Q)` is weakly
  carry-good, distinct elements of `C` lie in distinct residue classes mod `Q`.
* `liftedElt m lam i`, `liftedBlock m lam`: staggered lift
  `C̃_λ = {c_i + Q_m·λ_i : 0 ≤ i < m}` of the Mazur block `C_m`.
* **`mazurElt_mod_injOn`** & **`liftedBlock_card`** (Proposition 4(i)):
  the `c_i` are pairwise incongruent mod `Q_m`, so `|C̃_λ| = m` for every `λ`.
* **`staggered_lift_weaklyCarryGood_iff`** (Proposition 4(ii)): for `m ≥ 4`,
  `WeaklyCarryGood (liftedBlock m lam) (mazurQ m)` holds iff there exists
  `c : ℤ` with `∀ i < m, lam i = c * (m − i)`.
* **`staggered_lift_localCarry1_eq_zero`** (Proposition 4(iii)): for `m ≥ 4`,
  `LocalCarry (liftedBlock m lam) (mazurQ m) 1` forces `∀ i < m, lam i = 0`.
* **`staggered_lift_m3_localCarry0_counterexample`** &
  **`staggered_lift_m3_localCarry1_counterexample`** (Remark 5.4): both parts
  (ii) and (iii) fail at `m = 3` (`λ = (1, 1, 0)` and `λ = (0, 1, −1)`), so
  the threshold `m ≥ 4` is sharp.
-/

namespace Erdos875

open Finset

/-! ## Local carry predicate `ℒ_R(C, Q)` and Observation 5.1 -/

/-- `LocalCarry C Q R` (`ℒ_R(C, Q)` in the note): every `Y ∈ Δ_t(C)` of the
form `Y = Q·w − u` with `|u| ≤ R` satisfies `t = w − u`. -/
def LocalCarry (C : Finset ℤ) (Q : ℤ) (R : ℕ) : Prop :=
  ∀ ⦃t Y u w : ℤ⦄, IsSignedSum C t Y → Y = Q * w - u → |u| ≤ (R : ℤ) → t = w - u

theorem localCarry_zero_iff_weaklyCarryGood {C : Finset ℤ} {Q : ℤ} :
    LocalCarry C Q 0 ↔ WeaklyCarryGood C Q := by
  constructor
  · intro h T D q hTD hDq
    have h0 : |(0 : ℤ)| ≤ ((0 : ℕ) : ℤ) := by simp
    have heq : D = Q * q - 0 := by linarith
    have := h hTD heq h0
    linarith
  · intro h t Y u w hY heq hu
    have hu0 : u = 0 := by
      have h1 := neg_abs_le u
      have h2 := le_abs_self u
      simp at hu
      linarith
    subst hu0
    have heq' : Y = Q * w := by linarith
    have := h hY heq'
    linarith

theorem LocalCarry.mono {C : Finset ℤ} {Q : ℤ} {R₁ R₂ : ℕ} (hR : R₁ ≤ R₂)
    (h : LocalCarry C Q R₂) : LocalCarry C Q R₁ := by
  intro t Y u w hY heq hu
  have hR' : (R₁ : ℤ) ≤ (R₂ : ℤ) := by exact_mod_cast hR
  exact h hY heq (hu.trans hR')

/-- **Observation 5.1 (no repeated residues).** If `(C, Q)` is weakly
carry-good, then reduction modulo `Q` is injective on `C`. -/
theorem no_repeated_residues {C : Finset ℤ} {Q : ℤ}
    (hgood : WeaklyCarryGood C Q) :
    Set.InjOn (fun c : ℤ => c % Q) (C : Set ℤ) := by
  intro x hx y hy hmod
  have hxC : x ∈ C := Finset.mem_coe.mp hx
  have hyC : y ∈ C := Finset.mem_coe.mp hy
  have hdivx := Int.mul_ediv_add_emod x Q
  have hdivy := Int.mul_ediv_add_emod y Q
  have hdiff : x - y = Q * (x / Q - y / Q) := by
    linear_combination -hdivx + hdivy + hmod
  have hsigned : IsSignedSum C 0 (x - y) := by
    refine ⟨{x}, {y}, ?_, ?_, ?_, ?_⟩
    · intro z hz; rw [Finset.mem_singleton.mp hz]; exact hxC
    · intro z hz; rw [Finset.mem_singleton.mp hz]; exact hyC
    · simp
    · simp
  have hq0 := hgood hsigned hdiff
  have : x / Q - y / Q = 0 := by linarith
  rw [this, mul_zero] at hdiff
  linarith

/-! ## Staggered lifts of the Mazur block and Proposition 4(i) -/

/-- The `i`-th lifted Mazur element `c̃_i = c_i + Q_m·λ_i`. -/
def liftedElt (m : ℕ) (lam : ℕ → ℤ) (i : ℕ) : ℤ :=
  mazurElt m i + mazurQ m * lam i

/-- Staggered lift `C̃_λ = {c_i + Q_m·λ_i : 0 ≤ i < m}`. -/
def liftedBlock (m : ℕ) (lam : ℕ → ℤ) : Finset ℤ :=
  (Finset.range m).image (liftedElt m lam)

theorem mazurQ_pos (m : ℕ) : 0 < mazurQ m := by
  unfold mazurQ
  positivity

/-- For `i < m`, `c_i ∈ [1, m²] ⊂ [0, Q_m)`, so `c_i % Q_m = c_i`. -/
theorem mazurElt_mod_eq {m i : ℕ} (hi : i < m) :
    mazurElt m i % mazurQ m = mazurElt m i := by
  have hnonneg : 0 ≤ mazurElt m i := by
    unfold mazurElt
    positivity
  have hlt : mazurElt m i < mazurQ m := by
    have hi' : (i : ℤ) + 1 ≤ (m : ℤ) := by exact_mod_cast hi
    unfold mazurElt mazurQ
    nlinarith
  exact Int.emod_eq_of_lt hnonneg hlt

theorem liftedElt_mod_eq {m i : ℕ} (lam : ℕ → ℤ) (hi : i < m) :
    liftedElt m lam i % mazurQ m = mazurElt m i := by
  unfold liftedElt
  rw [Int.add_mul_emod_self_left, mazurElt_mod_eq hi]

/-- **Proposition 4(i), residue distinctness.** The Mazur elements `c_i`
(`0 ≤ i < m`) are pairwise incongruent modulo `Q_m`. -/
theorem mazurElt_mod_injOn (m : ℕ) :
    Set.InjOn (fun i : ℕ => mazurElt m i % mazurQ m) (Finset.range m : Set ℕ) := by
  intro i hi j hj heq
  dsimp only at heq
  rw [mazurElt_mod_eq (Finset.mem_range.mp (Finset.mem_coe.mp hi)),
    mazurElt_mod_eq (Finset.mem_range.mp (Finset.mem_coe.mp hj))] at heq
  exact mazurElt_injective m heq

/-- Distinct indices in `range m` never collide after lifting. -/
theorem liftedElt_injOn (m : ℕ) (lam : ℕ → ℤ) :
    Set.InjOn (liftedElt m lam) (Finset.range m : Set ℕ) := by
  intro i hi j hj heq
  apply mazurElt_injective m
  have hmod : liftedElt m lam i % mazurQ m = liftedElt m lam j % mazurQ m :=
    congrArg (fun z => z % mazurQ m) heq
  rwa [liftedElt_mod_eq lam (Finset.mem_range.mp (Finset.mem_coe.mp hi)),
    liftedElt_mod_eq lam (Finset.mem_range.mp (Finset.mem_coe.mp hj))] at hmod

/-- **Proposition 4(i), cardinality.** Every staggered lift `C̃_λ` has
cardinality `m`. -/
theorem liftedBlock_card (m : ℕ) (lam : ℕ → ℤ) :
    (liftedBlock m lam).card = m := by
  unfold liftedBlock
  rw [Finset.card_image_of_injOn (liftedElt_injOn m lam), Finset.card_range]

/-! ## Elementary signed-sum witnesses in `C̃_λ` -/

/-- Three-element signed sum `c̃_a + c̃_b − c̃_c ∈ Δ_1(C̃_λ)` for `a ≠ b` in `range m`. -/
theorem signedSum_two_minus_one {m : ℕ} {lam : ℕ → ℤ} {a b c : ℕ}
    (ha : a < m) (hb : b < m) (hc : c < m) (hab : a ≠ b) :
    IsSignedSum (liftedBlock m lam) 1
      (liftedElt m lam a + liftedElt m lam b - liftedElt m lam c) := by
  classical
  have hmem : ∀ k < m, liftedElt m lam k ∈ liftedBlock m lam := fun k hk =>
    Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
  have hne : liftedElt m lam a ≠ liftedElt m lam b := fun heq =>
    hab (liftedElt_injOn m lam (Finset.mem_coe.mpr (Finset.mem_range.mpr ha))
      (Finset.mem_coe.mpr (Finset.mem_range.mpr hb)) heq)
  refine ⟨{liftedElt m lam a, liftedElt m lam b}, {liftedElt m lam c}, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact hmem a ha
    · rw [Finset.mem_singleton.mp hx']
      exact hmem b hb
  · intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact hmem c hc
  · rw [Finset.card_pair hne, Finset.card_singleton]
    norm_num
  · rw [Finset.sum_pair hne, Finset.sum_singleton]

/-- Four-element signed sum `c̃_a + c̃_b − c̃_c − c̃_d ∈ Δ_0(C̃_λ)` for `a ≠ b` and `c ≠ d`. -/
theorem signedSum_two_minus_two {m : ℕ} {lam : ℕ → ℤ} {a b c d : ℕ}
    (ha : a < m) (hb : b < m) (hc : c < m) (hd : d < m)
    (hab : a ≠ b) (hcd : c ≠ d) :
    IsSignedSum (liftedBlock m lam) 0
      (liftedElt m lam a + liftedElt m lam b - liftedElt m lam c - liftedElt m lam d) := by
  classical
  have hmem : ∀ k < m, liftedElt m lam k ∈ liftedBlock m lam := fun k hk =>
    Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
  have hne1 : liftedElt m lam a ≠ liftedElt m lam b := fun heq =>
    hab (liftedElt_injOn m lam (Finset.mem_coe.mpr (Finset.mem_range.mpr ha))
      (Finset.mem_coe.mpr (Finset.mem_range.mpr hb)) heq)
  have hne2 : liftedElt m lam c ≠ liftedElt m lam d := fun heq =>
    hcd (liftedElt_injOn m lam (Finset.mem_coe.mpr (Finset.mem_range.mpr hc))
      (Finset.mem_coe.mpr (Finset.mem_range.mpr hd)) heq)
  refine ⟨{liftedElt m lam a, liftedElt m lam b},
    {liftedElt m lam c, liftedElt m lam d}, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact hmem a ha
    · rw [Finset.mem_singleton.mp hx']; exact hmem b hb
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact hmem c hc
    · rw [Finset.mem_singleton.mp hx']; exact hmem d hd
  · rw [Finset.card_pair hne1, Finset.card_pair hne2]
    norm_num
  · rw [Finset.sum_pair hne1, Finset.sum_pair hne2]
    ring

/-- Negative singleton `−c̃_a ∈ Δ_{−1}(C̃_λ)`. -/
theorem signedSum_neg_one {m : ℕ} {lam : ℕ → ℤ} {a : ℕ} (ha : a < m) :
    IsSignedSum (liftedBlock m lam) (-1) (-liftedElt m lam a) := by
  refine ⟨∅, {liftedElt m lam a}, Finset.empty_subset _, ?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact Finset.mem_image.mpr ⟨a, Finset.mem_range.mpr ha, rfl⟩
  · simp
  · simp

/-! ## Proposition 4(ii): classification of weakly carry-good staggered lifts -/

/-- Necessity direction of Proposition 4(ii). -/
theorem staggered_lift_necessity {m : ℕ} (hm : 4 ≤ m) {lam : ℕ → ℤ}
    (hgood : WeaklyCarryGood (liftedBlock m lam) (mazurQ m)) :
    ∀ i < m, lam i = lam (m - 1) * ((m : ℤ) - (i : ℤ)) := by
  let c : ℤ := lam (m - 1)
  -- Step 1: for 1 ≤ j ≤ m − 2, c_j + c_{m-1} − c_{j-1} = Q_m forces lam j = lam (j-1) − c
  have hstep : ∀ j : ℕ, 1 ≤ j → j ≤ m - 2 → lam j = lam (j - 1) - c := by
    intro j hj1 hj2
    have hjm : j < m := by omega
    have hm1 : m - 1 < m := by omega
    have hjm1 : j - 1 < m := by omega
    have hjne : j ≠ m - 1 := by omega
    have hsigned := signedSum_two_minus_one (lam := lam) hjm hm1 hjm1 hjne
    have hbase : mazurElt m j + mazurElt m (m - 1) - mazurElt m (j - 1) = mazurQ m := by
      have hcast1 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
      have hcast2 : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
      unfold mazurElt mazurQ
      rw [hcast1, hcast2]
      ring
    have hlifted : liftedElt m lam j + liftedElt m lam (m - 1) - liftedElt m lam (j - 1)
        = mazurQ m * (1 + lam j + c - lam (j - 1)) := by
      unfold liftedElt
      change (mazurElt m j + mazurQ m * lam j) +
        (mazurElt m (m - 1) + mazurQ m * c) -
        (mazurElt m (j - 1) + mazurQ m * lam (j - 1)) = _
      linear_combination hbase
    have hq := hgood hsigned hlifted
    linarith
  -- Step 2: by induction on j, lam j = lam 0 − j·c for all j ≤ m − 2
  have hline : ∀ j : ℕ, j ≤ m - 2 → lam j = lam 0 - (j : ℤ) * c := by
    intro j
    induction j with
    | zero =>
        intro _
        simp
    | succ j ih =>
        intro hj
        have h1 := hstep (j + 1) (by omega) hj
        have h2 := ih (by omega)
        have hsub : j + 1 - 1 = j := by omega
        rw [hsub, h2] at h1
        push_cast
        linarith
  -- Step 3: pin the intercept lam 0 = m·c (splitting m = 4 vs m ≥ 5)
  have hintercept : lam 0 = (m : ℤ) * c := by
    by_cases hm4 : m = 4
    · subst hm4
      have h1 : lam 1 = lam 0 - (1 : ℕ) * c := hline 1 (by omega)
      have h2 : lam 2 = lam 0 - (2 : ℕ) * c := hline 2 (by omega)
      have hc3 : lam 3 = c := rfl
      have hsigned := signedSum_two_minus_two (m := 4) (lam := lam)
        (a := 1) (b := 2) (c := 0) (d := 3)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hlifted : liftedElt 4 lam 1 + liftedElt 4 lam 2 -
          liftedElt 4 lam 0 - liftedElt 4 lam 3
          = mazurQ 4 * (lam 1 + lam 2 - lam 0 - lam 3) := by
        unfold liftedElt mazurElt mazurQ
        ring
      have hq := hgood hsigned hlifted
      push_cast at h1 h2 ⊢
      linarith
    · have hm5 : 5 ≤ m := by omega
      have h2_lt : 2 < m := by omega
      have hm2_lt : m - 2 < m := by omega
      have h0_lt : 0 < m := by omega
      have hne : 2 ≠ m - 2 := by omega
      have hsigned := signedSum_two_minus_one (lam := lam) h2_lt hm2_lt h0_lt hne
      have hbase : mazurElt m 2 + mazurElt m (m - 2) - mazurElt m 0 = mazurQ m := by
        have hcast : ((m - 2 : ℕ) : ℤ) = (m : ℤ) - 2 := by omega
        unfold mazurElt mazurQ
        rw [hcast]
        ring
      have hlifted : liftedElt m lam 2 + liftedElt m lam (m - 2) - liftedElt m lam 0
          = mazurQ m * (1 + lam 2 + lam (m - 2) - lam 0) := by
        unfold liftedElt
        linear_combination hbase
      have hq := hgood hsigned hlifted
      have h2 := hline 2 (by omega)
      have hm2 := hline (m - 2) (by omega)
      have hcast : ((m - 2 : ℕ) : ℤ) = (m : ℤ) - 2 := by omega
      rw [hcast] at hm2
      push_cast at h2
      linarith
  -- Step 4: combine for all i < m
  intro i hi
  by_cases him : i = m - 1
  · subst him
    have hcast : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
    change c = c * ((m : ℤ) - ((m - 1 : ℕ) : ℤ))
    rw [hcast]
    ring
  · have hle : i ≤ m - 2 := by omega
    have hi_eq := hline i hle
    rw [hintercept] at hi_eq
    linarith

/-- Sufficiency direction of Proposition 4(ii) (valid for every `m`). -/
theorem staggered_lift_sufficiency (m : ℕ) {lam : ℕ → ℤ} {c : ℤ}
    (hlam : ∀ i < m, lam i = c * ((m : ℤ) - (i : ℤ))) :
    WeaklyCarryGood (liftedBlock m lam) (mazurQ m) := by
  classical
  intro t Y w hY hYw
  obtain ⟨U, V, hU, hV, ht, hsum⟩ := hY
  obtain ⟨S, hSsub, hSU⟩ := exists_image_preimage hU
  obtain ⟨T, hTsub, hTV⟩ := exists_image_preimage hV
  have hinj := liftedElt_injOn m lam
  have hS_inj : Set.InjOn (liftedElt m lam) (S : Set ℕ) :=
    hinj.mono (Finset.coe_subset.mpr hSsub)
  have hT_inj : Set.InjOn (liftedElt m lam) (T : Set ℕ) :=
    hinj.mono (Finset.coe_subset.mpr hTsub)
  have hcardS : U.card = S.card := by
    rw [← hSU]
    exact Finset.card_image_of_injOn hS_inj
  have hcardT : V.card = T.card := by
    rw [← hTV]
    exact Finset.card_image_of_injOn hT_inj
  have hsum_set : ∀ A : Finset ℕ, A ⊆ Finset.range m →
      ∑ i ∈ A, liftedElt m lam i
        = mazurQ m * (A.card : ℤ) + (mazurQ m * c - ((m : ℤ) + 1)) * indexWeight m A := by
    intro A hA
    have hpoint : ∑ i ∈ A, liftedElt m lam i
        = (∑ i ∈ A, mazurElt m i) + mazurQ m * c * indexWeight m A := by
      unfold liftedElt indexWeight
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [hlam i (Finset.mem_range.mp (hA hi))]
      ring
    rw [hpoint, sum_mazurAP m A]
    ring
  have hUS : ∑ x ∈ U, x
      = mazurQ m * (S.card : ℤ) + (mazurQ m * c - ((m : ℤ) + 1)) * indexWeight m S := by
    rw [← hSU, Finset.sum_image (fun a ha b hb hab => hS_inj ha hb hab),
      hsum_set S hSsub]
  have hVT : ∑ x ∈ V, x
      = mazurQ m * (T.card : ℤ) + (mazurQ m * c - ((m : ℤ) + 1)) * indexWeight m T := by
    rw [← hTV, Finset.sum_image (fun a ha b hb hab => hT_inj ha hb hab),
      hsum_set T hTsub]
  let z : ℤ := indexWeight m S - indexWeight m T
  have hz_bound : 2 * |z| ≤ (m : ℤ) * ((m : ℤ) + 1) := by
    have h1 := indexWeight_nonneg hSsub
    have h2 := indexWeight_le hSsub
    have h3 := indexWeight_nonneg hTsub
    have h4 := indexWeight_le hTsub
    have h5 := two_indexWeight_range m
    have habs : |z| ≤ indexWeight m (Finset.range m) := by
      rw [abs_le]
      constructor <;> dsimp [z] <;> linarith
    linarith
  have hY_decomp : Y = mazurQ m * t + (mazurQ m * c - ((m : ℤ) + 1)) * z := by
    rw [hUS, hVT] at hsum
    rw [← ht, hcardS, hcardT] at *
    dsimp [z]
    linear_combination -hsum
  -- Bezout elimination: Q_m − m(m+1) = 1 forces Q_m ∣ z
  let k : ℤ := t - w + c * z
  have hrel : ((m : ℤ) + 1) * z = mazurQ m * k := by
    dsimp [k]
    linear_combination hY_decomp - hYw
  have hz_mult : z = mazurQ m * (z - (m : ℤ) * k) := by
    have hQdef : mazurQ m = (m : ℤ) * ((m : ℤ) + 1) + 1 := by
      unfold mazurQ
      ring
    linear_combination (-(m : ℤ)) * hrel - z * hQdef
  let q : ℤ := z - (m : ℤ) * k
  have hzq : z = mazurQ m * q := hz_mult
  have hQpos := mazurQ_pos m
  have hz1 : -((m : ℤ) * ((m : ℤ) + 1)) ≤ 2 * z := by
    have := neg_abs_le z
    linarith
  have hz2 : 2 * z ≤ (m : ℤ) * ((m : ℤ) + 1) := by
    have := le_abs_self z
    linarith
  have hQ_gt_L : (m : ℤ) * ((m : ℤ) + 1) < 2 * mazurQ m := by
    unfold mazurQ
    nlinarith
  have hq0 : q = 0 := by
    rcases lt_trichotomy q 0 with hneg | hzero | hpos
    · exfalso
      have hle1 : q ≤ -1 := by omega
      have hmul : mazurQ m * q ≤ mazurQ m * (-1) :=
        mul_le_mul_of_nonneg_left hle1 (le_of_lt hQpos)
      linarith
    · exact hzero
    · exfalso
      have hge1 : (1 : ℤ) ≤ q := hpos
      have hmul : mazurQ m * 1 ≤ mazurQ m * q :=
        mul_le_mul_of_nonneg_left hge1 (le_of_lt hQpos)
      linarith
  have hz0 : z = 0 := by
    rw [hzq, hq0, mul_zero]
  rw [hz0] at hY_decomp
  have hQt : mazurQ m * t = mazurQ m * w := by linarith
  exact mul_left_cancel₀ (ne_of_gt hQpos) hQt

/-- **Proposition 4(ii) (classification of `ℒ_0` staggered lifts).**
For `m ≥ 4`, `(C̃_λ, Q_m)` is weakly carry-good iff `λ_i = c·(m − i)` for all
`0 ≤ i < m` and some integer `c`. -/
theorem staggered_lift_weaklyCarryGood_iff {m : ℕ} (hm : 4 ≤ m) (lam : ℕ → ℤ) :
    WeaklyCarryGood (liftedBlock m lam) (mazurQ m) ↔
      ∃ c : ℤ, ∀ i < m, lam i = c * ((m : ℤ) - (i : ℤ)) := by
  constructor
  · intro hgood
    exact ⟨lam (m - 1), staggered_lift_necessity hm hgood⟩
  · rintro ⟨c, hc⟩
    exact staggered_lift_sufficiency m hc

/-! ## Proposition 4(iii): radius-1 carry kills every nontrivial lift -/

/-- **Proposition 4(iii) (unit-radius rigidity).** For `m ≥ 4`, if `C̃_λ`
satisfies `LocalCarry (liftedBlock m lam) (mazurQ m) 1`, then `λ_i = 0` for
every `0 ≤ i < m`. -/
theorem staggered_lift_localCarry1_eq_zero {m : ℕ} (hm : 4 ≤ m) {lam : ℕ → ℤ}
    (h1 : LocalCarry (liftedBlock m lam) (mazurQ m) 1) :
    ∀ i < m, lam i = 0 := by
  have h0 : LocalCarry (liftedBlock m lam) (mazurQ m) 0 :=
    h1.mono (by omega)
  have hgood : WeaklyCarryGood (liftedBlock m lam) (mazurQ m) :=
    localCarry_zero_iff_weaklyCarryGood.mp h0
  obtain ⟨c, hc⟩ := (staggered_lift_weaklyCarryGood_iff hm lam).mp hgood
  have hneg := signedSum_neg_one (m := m) (lam := lam) (a := 0) (by omega)
  have heq : -liftedElt m lam 0 = mazurQ m * (-lam 0) - 1 := by
    unfold liftedElt mazurElt
    ring
  have hu : |(1 : ℤ)| ≤ ((1 : ℕ) : ℤ) := by norm_num
  have ht := h1 hneg heq hu
  have hlam0 : lam 0 = 0 := by linarith
  have hc0_eq : lam 0 = c * (m : ℤ) := by
    have h := hc 0 (by omega)
    simpa using h
  have hm_ne : (m : ℤ) ≠ 0 := by omega
  have hc0 : c = 0 := by
    rw [hlam0] at hc0_eq
    exact (mul_eq_zero.mp hc0_eq.symm).resolve_right hm_ne
  intro i hi
  rw [hc i hi, hc0, zero_mul]

/-! ## Remark 5.4: sharpness of the threshold `m ≥ 4` at `m = 3` -/

/-- Decidable finite check for `LocalCarry C Q R` (`Q > 0`) by enumerating
subset pairs `U, V ∈ C.powerset` and errors `u ∈ [−R, R]`. -/
theorem localCarry_of_powerset_check {C : Finset ℤ} {Q : ℤ} {R : ℕ}
    (hQ : 0 < Q)
    (hcheck : ∀ U ∈ C.powerset, ∀ V ∈ C.powerset,
      ∀ u ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
        ((∑ x ∈ U, x) - (∑ x ∈ V, x) + u) % Q = 0 →
          (U.card : ℤ) - (V.card : ℤ) = ((∑ x ∈ U, x) - (∑ x ∈ V, x) + u) / Q - u) :
    LocalCarry C Q R := by
  intro t Y u w hY heq hu
  obtain ⟨U, V, hU, hV, ht, hsum⟩ := hY
  have hUP : U ∈ C.powerset := Finset.mem_powerset.mpr hU
  have hVP : V ∈ C.powerset := Finset.mem_powerset.mpr hV
  have huIcc : u ∈ Finset.Icc (-(R : ℤ)) (R : ℤ) := by
    rw [Finset.mem_Icc]
    exact abs_le.mp hu
  have hprod : (∑ x ∈ U, x) - (∑ x ∈ V, x) + u = w * Q := by
    linear_combination hsum + heq
  have hmod : ((∑ x ∈ U, x) - (∑ x ∈ V, x) + u) % Q = 0 := by
    rw [hprod, Int.mul_emod_left]
  have hdiv : ((∑ x ∈ U, x) - (∑ x ∈ V, x) + u) / Q = w := by
    rw [hprod, Int.mul_ediv_cancel w (ne_of_gt hQ)]
  have hres := hcheck U hUP V hVP u huIcc hmod
  rw [ht, hdiv] at hres
  exact hres

/-- **Remark 5.4, part (ii) fails at `m = 3`.** The lift `λ = (1, 1, 0)` gives
a weakly carry-good block `{14, 18, 9}` mod `Q_3 = 13` outside `{c·(3, 2, 1)}`. -/
theorem staggered_lift_m3_localCarry0_counterexample :
    ∃ lam : ℕ → ℤ, WeaklyCarryGood (liftedBlock 3 lam) (mazurQ 3) ∧
      ¬ ∃ c : ℤ, ∀ i < 3, lam i = c * ((3 : ℤ) - (i : ℤ)) := by
  let lam : ℕ → ℤ := fun i => if i = 0 then 1 else if i = 1 then 1 else 0
  refine ⟨lam, ?_, ?_⟩
  · have hblock : liftedBlock 3 lam = ({14, 18, 9} : Finset ℤ) := by decide
    have hQ : mazurQ 3 = 13 := by decide
    rw [← localCarry_zero_iff_weaklyCarryGood, hblock, hQ]
    exact localCarry_of_powerset_check (by norm_num) (by decide)
  · rintro ⟨c, hc⟩
    have h0 := hc 0 (by omega)
    have h2 := hc 2 (by omega)
    dsimp [lam] at h0 h2
    omega

/-- **Remark 5.4, part (iii) fails at `m = 3`.** The nontrivial lift
`λ = (0, 1, −1)` satisfies `LocalCarry (liftedBlock 3 lam) (mazurQ 3) 1`. -/
theorem staggered_lift_m3_localCarry1_counterexample :
    ∃ lam : ℕ → ℤ, LocalCarry (liftedBlock 3 lam) (mazurQ 3) 1 ∧ lam 1 ≠ 0 := by
  let lam : ℕ → ℤ := fun i => if i = 0 then 0 else if i = 1 then 1 else -1
  refine ⟨lam, ?_, by decide⟩
  have hblock : liftedBlock 3 lam = ({1, 18, -4} : Finset ℤ) := by decide
  have hQ : mazurQ 3 = 13 := by decide
  rw [hblock, hQ]
  exact localCarry_of_powerset_check (by norm_num) (by decide)

end Erdos875
