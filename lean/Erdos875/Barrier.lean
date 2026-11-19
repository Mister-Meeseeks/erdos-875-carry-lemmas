import Erdos875.Closure

/-!
# Quadratic radix barrier for all-quotient scalar carry (Erdős #875, Proposition 3)

This file formalizes Section 4 (Lemma 4.1, Lemma 4.2, Proposition 3, and
Remark 4.5 sharpness) of the note:

* `subsetSums D`: the set `FS(D) = { Σ_{x∈S} x : S ⊆ D }` of distinct subset
  sums of `D ⊆ ℤ` (including `0 = Σ_{x∈∅} x`).
* **`mod_injOn_subsetSums`** & **`card_subsetSums_sub_le`** (Lemma 4.1):
  if `(C, Q)` is weakly carry-good (`Q ≥ 1`), then reduction modulo `Q` is
  injective on `subsetSums (C − Q)`, so `|FS(C − Q)| ≤ Q`.
* **`card_subsetSums_ge`** & **`card_subsetSums_ge_of_zero_not_mem`**
  (Lemma 4.2): any `k`-element `D : Finset ℤ` satisfies
  `|FS(D)| ≥ ⌊k²/4⌋ + 1`, and if `0 ∉ D` then `|FS(D)| ≥ ⌊(k+1)²/4⌋ + 1`.
* **`quadratic_radix_barrier`** & **`quadratic_radix_barrier_not_mem`**
  (Proposition 3): any `k`-element weakly carry-good block `(C, Q)` with
  `Q ≥ 1` satisfies `Q ≥ ⌊k²/4⌋ + 1`, and `Q ≥ ⌊(k+1)²/4⌋ + 1` when `Q ∉ C`.
* **`quadratic_radix_barrier_sharp`** &
  **`quadratic_radix_barrier_not_mem_sharp`** (Remark 4.5): both bounds are
  attained for every `k ≥ 1` by explicit positive flat blocks.
-/

namespace Erdos875

open Finset

/-! ## Subset sums over `Finset ℤ` -/

/-- `subsetSums D` (`FS(D)` in the note) is the set of all subset sums
`Σ_{x∈S} x` as `S` ranges over subsets of `D`. -/
def subsetSums (D : Finset ℤ) : Finset ℤ :=
  D.powerset.image (fun S => ∑ x ∈ S, x)

theorem mem_subsetSums {D : Finset ℤ} {s : ℤ} :
    s ∈ subsetSums D ↔ ∃ S ⊆ D, ∑ x ∈ S, x = s := by
  simp [subsetSums]

theorem zero_mem_subsetSums (D : Finset ℤ) : (0 : ℤ) ∈ subsetSums D :=
  mem_subsetSums.mpr ⟨∅, Finset.empty_subset D, Finset.sum_empty⟩

theorem subsetSums_mono {D₁ D₂ : Finset ℤ} (h : D₁ ⊆ D₂) :
    subsetSums D₁ ⊆ subsetSums D₂ := by
  intro s hs
  obtain ⟨S, hS, rfl⟩ := mem_subsetSums.mp hs
  exact mem_subsetSums.mpr ⟨S, hS.trans h, rfl⟩

/-! ## Lemma 4.1: carry implies modular injectivity on `FS(C − Q)` -/

/-- Shifted block `C − Q = {c − Q : c ∈ C}`. -/
def shiftSub (C : Finset ℤ) (Q : ℤ) : Finset ℤ :=
  C.image (fun c => c - Q)

theorem shiftSub_card (C : Finset ℤ) (Q : ℤ) :
    (shiftSub C Q).card = C.card :=
  Finset.card_image_of_injective C (sub_left_injective)

theorem zero_mem_shiftSub_iff {C : Finset ℤ} {Q : ℤ} :
    (0 : ℤ) ∈ shiftSub C Q ↔ Q ∈ C := by
  simp only [shiftSub, Finset.mem_image]
  constructor
  · rintro ⟨c, hc, hsub⟩
    have hcq : c = Q := by linarith
    rwa [← hcq]
  · intro hQ
    exact ⟨Q, hQ, sub_self Q⟩

/-- Every subset sum in `FS(C − Q)` has the form `(Σ_{x∈X} x) − Q·|X|` for a
subset `X ⊆ C`. -/
theorem mem_subsetSums_shiftSub {C : Finset ℤ} {Q s : ℤ}
    (hs : s ∈ subsetSums (shiftSub C Q)) :
    ∃ X ⊆ C, s = (∑ x ∈ X, x) - Q * (X.card : ℤ) := by
  obtain ⟨S, hS, rfl⟩ := mem_subsetSums.mp hs
  obtain ⟨X, hXC, rfl⟩ := exists_image_preimage hS
  have hinj : Function.Injective (fun c : ℤ => c - Q) := sub_left_injective
  refine ⟨X, hXC, ?_⟩
  rw [Finset.sum_image (fun a _ b _ hab => hinj hab),
    Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Lemma 4.1 (modular injectivity).** If `(C, Q)` is weakly carry-good, then
`s ↦ s % Q` is injective on `subsetSums (shiftSub C Q)`. -/
theorem mod_injOn_subsetSums {C : Finset ℤ} {Q : ℤ}
    (hgood : WeaklyCarryGood C Q) :
    Set.InjOn (fun s : ℤ => s % Q) (subsetSums (shiftSub C Q) : Set ℤ) := by
  intro s₁ hs₁ s₂ hs₂ hmod
  obtain ⟨X₁, hX₁, hs₁eq⟩ := mem_subsetSums_shiftSub (Finset.mem_coe.mp hs₁)
  obtain ⟨X₂, hX₂, hs₂eq⟩ := mem_subsetSums_shiftSub (Finset.mem_coe.mp hs₂)
  have hdiv₁ := Int.mul_ediv_add_emod s₁ Q
  have hdiv₂ := Int.mul_ediv_add_emod s₂ Q
  have hdiff : s₁ - s₂ = Q * (s₁ / Q - s₂ / Q) := by
    linear_combination -hdiv₁ + hdiv₂ + hmod
  have hD : (∑ x ∈ X₁, x) - (∑ x ∈ X₂, x)
      = Q * ((s₁ / Q - s₂ / Q) + ((X₁.card : ℤ) - (X₂.card : ℤ))) := by
    linear_combination -hs₁eq + hs₂eq + hdiff
  have hsigned : IsSignedSum C ((X₁.card : ℤ) - (X₂.card : ℤ))
      ((∑ x ∈ X₁, x) - (∑ x ∈ X₂, x)) :=
    ⟨X₁, X₂, hX₁, hX₂, rfl, rfl⟩
  have hteq := hgood hsigned hD
  have hqzero : s₁ / Q - s₂ / Q = 0 := by linarith
  rw [hqzero, mul_zero] at hdiff
  linarith

/-- **Lemma 4.1 (cardinality consequence).** If `Q ≥ 1` and `(C, Q)` is weakly
carry-good, then `|FS(C − Q)| ≤ Q`. -/
theorem card_subsetSums_sub_le {C : Finset ℤ} {Q : ℤ} (hQ : 1 ≤ Q)
    (hgood : WeaklyCarryGood C Q) :
    ((subsetSums (shiftSub C Q)).card : ℤ) ≤ Q := by
  have hQpos : (0 : ℤ) < Q := by omega
  let f : ℤ → ℕ := fun s => (s % Q).toNat
  have hf_cast : ∀ s : ℤ, ((f s : ℤ)) = s % Q := fun s =>
    Int.toNat_of_nonneg (Int.emod_nonneg s (by omega))
  have hf_inj : Set.InjOn f (subsetSums (shiftSub C Q) : Set ℤ) := by
    intro s₁ hs₁ s₂ hs₂ hfeq
    apply mod_injOn_subsetSums hgood hs₁ hs₂
    dsimp only
    rw [← hf_cast s₁, ← hf_cast s₂, hfeq]
  have hf_sub : (subsetSums (shiftSub C Q)).image f ⊆ Finset.range Q.toNat := by
    intro r hr
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hr
    rw [Finset.mem_range]
    have hlt : s % Q < Q := Int.emod_lt_of_pos s hQpos
    have hQcast : ((Q.toNat : ℤ)) = Q := Int.toNat_of_nonneg (by omega)
    have hlt' : ((f s : ℤ)) < ((Q.toNat : ℤ)) := by
      rw [hf_cast s, hQcast]
      exact hlt
    exact_mod_cast hlt'
  have hcard_nat : (subsetSums (shiftSub C Q)).card ≤ Q.toNat := by
    calc (subsetSums (shiftSub C Q)).card
        = ((subsetSums (shiftSub C Q)).image f).card :=
          (Finset.card_image_of_injOn hf_inj).symm
      _ ≤ (Finset.range Q.toNat).card := Finset.card_le_card hf_sub
      _ = Q.toNat := Finset.card_range Q.toNat
  have hcast : ((subsetSums (shiftSub C Q)).card : ℤ) ≤ ((Q.toNat : ℤ)) := by
    exact_mod_cast hcard_nat
  rwa [Int.toNat_of_nonneg (by omega)] at hcast

/-! ## Lemma 4.2: elementary subset-sum counting bound -/

/-- Any finite set `P` of `p` strictly positive integers produces at least
`p(p+1)/2` distinct strictly positive subset sums. -/
theorem pos_subsetSums_card_ge :
    ∀ (p : ℕ) (P : Finset ℤ), P.card = p → (∀ x ∈ P, 0 < x) →
      p * (p + 1) / 2 ≤ ((subsetSums P).filter (fun s => 0 < s)).card := by
  intro p
  induction p with
  | zero =>
      intro P _ _
      simp
  | succ p ih =>
      intro P hcard hpos
      have hne : P.Nonempty := Finset.card_pos.mp (by omega)
      let m : ℤ := P.max' hne
      have hm_mem : m ∈ P := Finset.max'_mem P hne
      have hm_pos : 0 < m := hpos m hm_mem
      have hm_ge : ∀ x ∈ P, x ≤ m := fun x hx => Finset.le_max' P x hx
      let P' : Finset ℤ := P.erase m
      have hP'sub : P' ⊆ P := Finset.erase_subset m P
      have hP'card : P'.card = p := by
        rw [Finset.card_erase_of_mem hm_mem, hcard]
        omega
      have hP'pos : ∀ x ∈ P', 0 < x := fun x hx => hpos x (hP'sub hx)
      have hih := ih P' hP'card hP'pos
      let Pos' : Finset ℤ := (subsetSums P').filter (fun s => 0 < s)
      let Shifted : Finset ℤ := Pos'.image (fun s => m + s)
      let Pos : Finset ℤ := (subsetSums P).filter (fun s => 0 < s)
      -- Group 1: all p + 1 singletons of P lie in Pos and are ≤ m
      have hG1 : P ⊆ Pos := by
        intro x hx
        rw [Finset.mem_filter]
        refine ⟨mem_subsetSums.mpr ⟨{x}, ?_, by simp⟩, hpos x hx⟩
        intro y hy
        rw [Finset.mem_singleton.mp hy]
        exact hx
      -- Group 2: m + Pos' lies in Pos and every element exceeds m
      have hG2 : Shifted ⊆ Pos := by
        intro z hz
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨hs_sum, hs_pos⟩ := Finset.mem_filter.mp hs
        obtain ⟨U, hUP', rfl⟩ := mem_subsetSums.mp hs_sum
        have hm_not_U : m ∉ U := fun hmU => by
          have := hUP' hmU
          simp [P'] at this
        rw [Finset.mem_filter]
        refine ⟨mem_subsetSums.mpr ⟨insert m U, ?_, Finset.sum_insert hm_not_U⟩, by omega⟩
        rw [Finset.insert_subset_iff]
        exact ⟨hm_mem, hUP'.trans hP'sub⟩
      have hdisj : Disjoint P Shifted := by
        rw [Finset.disjoint_left]
        intro z hzP hzS
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hzS
        have hs_pos : 0 < s := (Finset.mem_filter.mp hs).2
        have hle : m + s ≤ m := hm_ge (m + s) hzP
        omega
      have hShifted_card : Shifted.card = Pos'.card :=
        Finset.card_image_of_injective Pos' (add_right_injective m)
      have hunion_le : (P ∪ Shifted).card ≤ Pos.card :=
        Finset.card_le_card (Finset.union_subset hG1 hG2)
      rw [Finset.card_union_of_disjoint hdisj, hcard, hShifted_card] at hunion_le
      dsimp only [Pos', Pos] at hunion_le
      obtain ⟨c, hc⟩ := Nat.even_mul_succ_self p
      have hexp : (p + 1) * (p + 1 + 1) = p * (p + 1) + 2 * (p + 1) := by ring
      rw [hc] at hih
      rw [hexp, hc]
      omega

/-- Symmetric lower bound for strictly negative subset sums. -/
theorem neg_subsetSums_card_ge {D : Finset ℤ} :
    let n := (D.filter (fun x => x < 0)).card
    n * (n + 1) / 2 ≤ ((subsetSums D).filter (fun s => s < 0)).card := by
  intro n
  let Dneg := D.filter (fun x => x < 0)
  let P := Dneg.image (fun x => -x)
  have hPcard : P.card = n :=
    Finset.card_image_of_injective Dneg neg_injective
  have hPpos : ∀ y ∈ P, 0 < y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hxneg : x < 0 := (Finset.mem_filter.mp hx).2
    omega
  have hpos := pos_subsetSums_card_ge n P hPcard hPpos
  let PosP := (subsetSums P).filter (fun s => 0 < s)
  let NegImg := PosP.image (fun s => -s)
  have hsub : NegImg ⊆ (subsetSums D).filter (fun s => s < 0) := by
    intro z hz
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hs_sum, hs_pos⟩ := Finset.mem_filter.mp hs
    obtain ⟨U, hUP, rfl⟩ := mem_subsetSums.mp hs_sum
    obtain ⟨V, hVDneg, rfl⟩ := exists_image_preimage hUP
    rw [Finset.mem_filter]
    refine ⟨mem_subsetSums.mpr ⟨V, hVDneg.trans (Finset.filter_subset _ D), ?_⟩, ?_⟩
    · rw [Finset.sum_image (fun a _ b _ hab => neg_injective hab), Finset.sum_neg_distrib, neg_neg]
    · omega
  have hcard : NegImg.card = PosP.card :=
    Finset.card_image_of_injective PosP neg_injective
  exact hpos.trans (hcard ▸ Finset.card_le_card hsub)

/-- Balanced-split quadratic bound: `⌊(p+n+1)²/4⌋ ≤ p(p+1)/2 + n(n+1)/2`. -/
theorem balanced_quad_bound (p n : ℕ) :
    (p + n + 1) ^ 2 / 4 ≤ p * (p + 1) / 2 + n * (n + 1) / 2 := by
  obtain ⟨cp, hcp⟩ := Nat.even_mul_succ_self p
  obtain ⟨cn, hcn⟩ := Nat.even_mul_succ_self n
  have hp_div : p * (p + 1) / 2 = cp := by omega
  have hn_div : n * (n + 1) / 2 = cn := by omega
  rw [hp_div, hn_div]
  by_cases hpn : p = n
  · subst hpn
    have hexp : (p + p + 1) ^ 2 = 4 * (p * (p + 1)) + 1 := by ring
    rw [hexp, hcp]
    omega
  · have h4z : ((p + n + 1 : ℕ) : ℤ) ^ 2 ≤ 4 * ((cp : ℤ) + (cn : ℤ)) := by
      have hcpz : (p : ℤ) * ((p : ℤ) + 1) = (cp : ℤ) + (cp : ℤ) := by exact_mod_cast hcp
      have hcnz : (n : ℤ) * ((n : ℤ) + 1) = (cn : ℤ) + (cn : ℤ) := by exact_mod_cast hcn
      have hdiff : (p : ℤ) - (n : ℤ) ≠ 0 := by omega
      have hsq1 : (1 : ℤ) ≤ ((p : ℤ) - (n : ℤ)) ^ 2 := by
        rcases lt_or_gt_of_ne hdiff with hlt | hgt <;> nlinarith
      push_cast
      nlinarith
    have h4n : (p + n + 1) ^ 2 ≤ 4 * (cp + cn) := by exact_mod_cast h4z
    omega

/-- Core bound in terms of the number of nonzero elements `s = |D \ {0}|`. -/
theorem card_subsetSums_ge_nonzero (D : Finset ℤ) :
    ((D.filter (fun x => x ≠ 0)).card + 1) ^ 2 / 4 + 1 ≤ (subsetSums D).card := by
  let Dpos := D.filter (fun x => 0 < x)
  let Dneg := D.filter (fun x => x < 0)
  have hpos_sub : (subsetSums Dpos).filter (fun s => 0 < s) ⊆
      (subsetSums D).filter (fun s => 0 < s) :=
    Finset.filter_subset_filter _ (subsetSums_mono (Finset.filter_subset _ D))
  have hp : Dpos.card * (Dpos.card + 1) / 2 ≤ ((subsetSums D).filter (fun s => 0 < s)).card :=
    (pos_subsetSums_card_ge Dpos.card Dpos rfl (fun _ hx => (Finset.mem_filter.mp hx).2)).trans
      (Finset.card_le_card hpos_sub)
  have hn : Dneg.card * (Dneg.card + 1) / 2 ≤ ((subsetSums D).filter (fun s => s < 0)).card :=
    neg_subsetSums_card_ge
  let Spos := (subsetSums D).filter (fun s => 0 < s)
  let Sneg := (subsetSums D).filter (fun s => s < 0)
  let Szero : Finset ℤ := {0}
  have hsub_all : Spos ∪ Sneg ∪ Szero ⊆ subsetSums D := by
    refine Finset.union_subset (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)) ?_
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact zero_mem_subsetSums D
  have hdisj_pn : Disjoint Spos Sneg := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h1 := (Finset.mem_filter.mp hx1).2
    have h2 := (Finset.mem_filter.mp hx2).2
    omega
  have hdisj_z : Disjoint (Spos ∪ Sneg) Szero := by
    rw [Finset.disjoint_right]
    intro x hx0 hpn
    rw [Finset.mem_singleton.mp hx0] at hpn
    rcases Finset.mem_union.mp hpn with h1 | h2
    · exact absurd (Finset.mem_filter.mp h1).2 (by omega)
    · exact absurd (Finset.mem_filter.mp h2).2 (by omega)
  have htotal : Spos.card + Sneg.card + 1 ≤ (subsetSums D).card := by
    have hle := Finset.card_le_card hsub_all
    rw [Finset.card_union_of_disjoint hdisj_z, Finset.card_union_of_disjoint hdisj_pn,
      Finset.card_singleton] at hle
    exact hle
  have hpart : D.filter (fun x => x ≠ 0) = Dpos ∪ Dneg := by
    ext x
    simp only [Dpos, Dneg, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hxD, hx0⟩
      rcases lt_or_gt_of_ne hx0 with hneg | hpos
      · exact Or.inr ⟨hxD, hneg⟩
      · exact Or.inl ⟨hxD, hpos⟩
    · rintro (⟨hxD, hpos⟩ | ⟨hxD, hneg⟩)
      · exact ⟨hxD, by omega⟩
      · exact ⟨hxD, by omega⟩
  have hdisj_D : Disjoint Dpos Dneg := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h1 := (Finset.mem_filter.mp hx1).2
    have h2 := (Finset.mem_filter.mp hx2).2
    omega
  have hs_eq : (D.filter (fun x => x ≠ 0)).card = Dpos.card + Dneg.card := by
    rw [hpart, Finset.card_union_of_disjoint hdisj_D]
  rw [hs_eq]
  dsimp only [Spos, Sneg] at htotal
  have hquad := balanced_quad_bound Dpos.card Dneg.card
  omega

/-- **Lemma 4.2 (`0 ∉ D` case).** Any finite set `D` of `k` nonzero integers has
at least `⌊(k+1)²/4⌋ + 1` distinct subset sums. -/
theorem card_subsetSums_ge_of_zero_not_mem {D : Finset ℤ} (h0 : (0 : ℤ) ∉ D) :
    (D.card + 1) ^ 2 / 4 + 1 ≤ (subsetSums D).card := by
  have hfilt : D.filter (fun x => x ≠ 0) = D := by
    ext x
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro hx rfl
    exact h0 hx
  have h := card_subsetSums_ge_nonzero D
  rwa [hfilt] at h

/-- **Lemma 4.2 (general case).** Any finite set `D` of `k` integers has at least
`⌊k²/4⌋ + 1` distinct subset sums. -/
theorem card_subsetSums_ge (D : Finset ℤ) :
    D.card ^ 2 / 4 + 1 ≤ (subsetSums D).card := by
  by_cases h0 : (0 : ℤ) ∈ D
  · have hfilt : D.filter (fun x => x ≠ 0) = D.erase 0 := by
      ext x
      simp [and_comm]
    have h := card_subsetSums_ge_nonzero D
    rw [hfilt, Finset.card_erase_of_mem h0] at h
    have hpos : 1 ≤ D.card := Finset.card_pos.mpr ⟨0, h0⟩
    have hcancel : D.card - 1 + 1 = D.card := by omega
    rwa [hcancel] at h
  · have h := card_subsetSums_ge_of_zero_not_mem h0
    have hmono : D.card ^ 2 / 4 ≤ (D.card + 1) ^ 2 / 4 :=
      Nat.div_le_div_right (Nat.pow_le_pow_left (by omega) 2)
    omega

/-! ## Proposition 3: the quadratic radix barrier -/

/-- **Proposition 3 (quadratic radix barrier), general case.**
Every weakly carry-good pair `(C, Q)` with `Q ≥ 1` satisfies
`Q ≥ ⌊|C|²/4⌋ + 1`. -/
theorem quadratic_radix_barrier {C : Finset ℤ} {Q : ℤ}
    (hQ : 1 ≤ Q) (hgood : WeaklyCarryGood C Q) :
    ((C.card ^ 2 / 4 : ℕ) : ℤ) + 1 ≤ Q := by
  have hupper := card_subsetSums_sub_le hQ hgood
  have hlower := card_subsetSums_ge (shiftSub C Q)
  rw [shiftSub_card] at hlower
  have hlower_z : ((C.card ^ 2 / 4 + 1 : ℕ) : ℤ) ≤ ((subsetSums (shiftSub C Q)).card : ℤ) := by
    exact_mod_cast hlower
  rw [Nat.cast_add, Nat.cast_one] at hlower_z
  linarith

/-- **Proposition 3 (quadratic radix barrier), `Q ∉ C` sharpening.**
Every weakly carry-good pair `(C, Q)` with `Q ≥ 1` and `Q ∉ C` satisfies
`Q ≥ ⌊(|C|+1)²/4⌋ + 1`. -/
theorem quadratic_radix_barrier_not_mem {C : Finset ℤ} {Q : ℤ}
    (hQ : 1 ≤ Q) (hgood : WeaklyCarryGood C Q) (hnotmem : Q ∉ C) :
    (((C.card + 1) ^ 2 / 4 : ℕ) : ℤ) + 1 ≤ Q := by
  have hupper := card_subsetSums_sub_le hQ hgood
  have h0 : (0 : ℤ) ∉ shiftSub C Q := by
    rwa [zero_mem_shiftSub_iff]
  have hlower := card_subsetSums_ge_of_zero_not_mem h0
  rw [shiftSub_card] at hlower
  have hlower_z : (((C.card + 1) ^ 2 / 4 + 1 : ℕ) : ℤ) ≤
      ((subsetSums (shiftSub C Q)).card : ℤ) := by
    exact_mod_cast hlower
  rw [Nat.cast_add, Nat.cast_one] at hlower_z
  linarith

/-! ## Remark 4.5: Straus flat blocks attain both bounds for every `k ≥ 1` -/

/-- Sufficient condition for weak carry-goodness (Straus flat-block regime):
if `Σ_{c∈C} |c − Q| < Q`, then `(C, Q)` is weakly carry-good. -/
theorem weaklyCarryGood_of_sum_abs_sub_lt {C : Finset ℤ} {Q : ℤ}
    (hsum : ∑ c ∈ C, |c - Q| < Q) :
    WeaklyCarryGood C Q := by
  classical
  have hnonneg_C : 0 ≤ ∑ c ∈ C, |c - Q| :=
    Finset.sum_nonneg (fun c _ => abs_nonneg (c - Q))
  have hQpos : 0 < Q := by linarith
  intro T D q hTD hDq
  obtain ⟨U, V, hU, hV, ht, hD⟩ := hTD
  let U' := U.filter (fun x => x ∉ V)
  let V' := V.filter (fun x => x ∉ U)
  let W := U.filter (fun x => x ∈ V)
  have hW_eq : V.filter (fun x => x ∈ U) = W := by
    ext x
    simp [W, and_comm]
  have hU_part : U = U' ∪ W := by
    ext x
    simp only [U', W, Finset.mem_union, Finset.mem_filter]
    tauto
  have hV_part : V = V' ∪ W := by
    rw [← hW_eq]
    ext x
    simp only [V', Finset.mem_union, Finset.mem_filter]
    tauto
  have hU_disj : Disjoint U' W := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_filter.mp hx1).2 (Finset.mem_filter.mp hx2).2
  have hV_disj : Disjoint V' W := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_filter.mp hx1).2 (Finset.mem_filter.mp hx2).1
  have hUV_disj : Disjoint U' V' := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_filter.mp hx2).2 (Finset.mem_filter.mp hx1).1
  have hT' : (U'.card : ℤ) - (V'.card : ℤ) = T := by
    have hcU : U.card = U'.card + W.card := by
      conv_lhs => rw [hU_part]
      exact Finset.card_union_of_disjoint hU_disj
    have hcV : V.card = V'.card + W.card := by
      conv_lhs => rw [hV_part]
      exact Finset.card_union_of_disjoint hV_disj
    rw [hcU, hcV] at ht
    push_cast at ht
    linarith
  have hD' : (∑ x ∈ U', x) - (∑ x ∈ V', x) = Q * q := by
    have hsU : ∑ x ∈ U, x = (∑ x ∈ U', x) + (∑ x ∈ W, x) := by
      conv_lhs => rw [hU_part]
      exact Finset.sum_union hU_disj
    have hsV : ∑ x ∈ V, x = (∑ x ∈ V', x) + (∑ x ∈ W, x) := by
      conv_lhs => rw [hV_part]
      exact Finset.sum_union hV_disj
    rw [hsU, hsV] at hD
    linarith
  have hshift : ∀ S : Finset ℤ, ∑ x ∈ S, x = Q * (S.card : ℤ) + ∑ x ∈ S, (x - Q) := by
    intro S
    have hq : Q * (S.card : ℤ) = ∑ _x ∈ S, Q := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => by ring)
  have hrem : Q * (q - T) = (∑ x ∈ U', (x - Q)) - (∑ x ∈ V', (x - Q)) := by
    have h1 := hshift U'
    have h2 := hshift V'
    linear_combination -hD' + h1 - h2 + Q * hT'
  have hU'_hi : ∑ x ∈ U', (x - Q) ≤ ∑ x ∈ U', |x - Q| :=
    Finset.sum_le_sum (fun x _ => le_abs_self (x - Q))
  have hU'_lo : -(∑ x ∈ U', |x - Q|) ≤ ∑ x ∈ U', (x - Q) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun x _ => neg_abs_le (x - Q))
  have hV'_hi : ∑ x ∈ V', (x - Q) ≤ ∑ x ∈ V', |x - Q| :=
    Finset.sum_le_sum (fun x _ => le_abs_self (x - Q))
  have hV'_lo : -(∑ x ∈ V', |x - Q|) ≤ ∑ x ∈ V', (x - Q) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun x _ => neg_abs_le (x - Q))
  have hUV_sub : U' ∪ V' ⊆ C :=
    Finset.union_subset ((Finset.filter_subset _ U).trans hU)
      ((Finset.filter_subset _ V).trans hV)
  have hUV_sum : (∑ x ∈ U', |x - Q|) + (∑ x ∈ V', |x - Q|) ≤ ∑ c ∈ C, |c - Q| := by
    rw [← Finset.sum_union hUV_disj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hUV_sub (fun x _ _ => abs_nonneg (x - Q))
  rcases lt_trichotomy (q - T) 0 with hneg | hzero | hpos
  · exfalso
    have hle1 : q - T ≤ -1 := by omega
    have hmul : Q * (q - T) ≤ Q * (-1) := mul_le_mul_of_nonneg_left hle1 (le_of_lt hQpos)
    linarith
  · linarith
  · exfalso
    have hge1 : (1 : ℤ) ≤ q - T := hpos
    have hmul : Q * 1 ≤ Q * (q - T) := mul_le_mul_of_nonneg_left hge1 (le_of_lt hQpos)
    linarith

/-- Gauss sum `Σ_{x ∈ [1, h]} |x| = h(h+1)/2` over `ℤ`. -/
theorem sum_abs_Icc_pos (h : ℕ) :
    ∑ x ∈ Finset.Icc (1 : ℤ) (h : ℤ), |x| = ((h * (h + 1) / 2 : ℕ) : ℤ) := by
  induction h with
  | zero =>
      simp
  | succ h ih =>
      have hins : Finset.Icc (1 : ℤ) (((h + 1 : ℕ) : ℤ))
          = insert (((h + 1 : ℕ) : ℤ)) (Finset.Icc (1 : ℤ) (h : ℤ)) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotmem : (((h + 1 : ℕ) : ℤ)) ∉ Finset.Icc (1 : ℤ) (h : ℤ) := by
        simp only [Finset.mem_Icc]
        omega
      rw [hins, Finset.sum_insert hnotmem, ih, abs_of_nonneg (by positivity)]
      obtain ⟨c, hc⟩ := Nat.even_mul_succ_self h
      have hexp : (h + 1) * (h + 1 + 1) = h * (h + 1) + 2 * (h + 1) := by ring
      have h1 : h * (h + 1) / 2 = c := by omega
      have h2 : (h + 1) * (h + 1 + 1) / 2 = c + (h + 1) := by omega
      rw [h1, h2]
      push_cast
      ring

/-- Symmetric Gauss sum `Σ_{x ∈ [−h, −1]} |x| = h(h+1)/2` over `ℤ`. -/
theorem sum_abs_Icc_neg (h : ℕ) :
    ∑ x ∈ Finset.Icc (-(h : ℤ)) (-1 : ℤ), |x| = ((h * (h + 1) / 2 : ℕ) : ℤ) := by
  have himg : (Finset.Icc (1 : ℤ) (h : ℤ)).image (fun x => -x)
      = Finset.Icc (-(h : ℤ)) (-1 : ℤ) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨x, hx, rfl⟩
      omega
    · intro hy
      exact ⟨-y, by omega, neg_neg y⟩
  rw [← himg, Finset.sum_image (fun a _ b _ hab => neg_injective hab)]
  have hcongr : ∑ x ∈ Finset.Icc (1 : ℤ) (h : ℤ), |-x|
      = ∑ x ∈ Finset.Icc (1 : ℤ) (h : ℤ), |x| :=
    Finset.sum_congr rfl (fun x _ => abs_neg x)
  rw [hcongr, sum_abs_Icc_pos]

/-- **Remark 4.5 (sharpness of Proposition 3, general `Q ∈ C` bound).**
For every `k ≥ 1`, there exist a `k`-element subset `C` of positive integers
and `Q = ⌊k²/4⌋ + 1` with `Q ∈ C` and `WeaklyCarryGood C Q`. -/
theorem quadratic_radix_barrier_sharp {k : ℕ} (hk : 1 ≤ k) :
    ∃ C : Finset ℤ, C.card = k ∧ (∀ c ∈ C, 1 ≤ c) ∧
      ((k ^ 2 / 4 : ℕ) : ℤ) + 1 ∈ C ∧
      WeaklyCarryGood C (((k ^ 2 / 4 : ℕ) : ℤ) + 1) := by
  classical
  let Q : ℤ := ((k ^ 2 / 4 : ℕ) : ℤ) + 1
  rcases Nat.even_or_odd' k with ⟨h, rfl | rfl⟩
  · -- Even case k = 2h (with h ≥ 1): D = [−(h−1), h]
    have hh : 1 ≤ h := by omega
    let D : Finset ℤ := Finset.Icc (-(((h - 1 : ℕ) : ℤ))) (h : ℤ)
    let C : Finset ℤ := D.image (fun d => d + Q)
    have hinj : Function.Injective (fun d : ℤ => d + Q) := add_left_injective Q
    have hDcard : D.card = 2 * h := by
      rw [Int.card_Icc]
      omega
    have hQeq : Q = (h : ℤ) ^ 2 + 1 := by
      have hdiv : (2 * h) ^ 2 / 4 = h ^ 2 := by
        have : (2 * h) ^ 2 = 4 * h ^ 2 := by ring
        omega
      simp only [Q, hdiv]
      push_cast
      ring
    refine ⟨C, ?_, ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective D hinj, hDcard]
    · intro c hc
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
      have hd' := Finset.mem_Icc.mp hd
      have hh' : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hh
      have hcast : ((h - 1 : ℕ) : ℤ) = (h : ℤ) - 1 := by omega
      rw [hcast] at hd'
      rw [hQeq]
      nlinarith
    · refine Finset.mem_image.mpr ⟨0, Finset.mem_Icc.mpr (by omega), by ring⟩
    · apply weaklyCarryGood_of_sum_abs_sub_lt
      rw [Finset.sum_image (fun a _ b _ hab => hinj hab)]
      have hsimp : ∑ d ∈ D, |(d + Q) - Q| = ∑ d ∈ D, |d| :=
        Finset.sum_congr rfl (fun d _ => by ring_nf)
      rw [hsimp]
      let Dn := Finset.Icc (-(((h - 1 : ℕ) : ℤ))) (-1 : ℤ)
      let Dp := Finset.Icc (1 : ℤ) (h : ℤ)
      have hsplit : D = Dn ∪ ({0} : Finset ℤ) ∪ Dp := by
        ext x
        simp only [D, Dn, Dp, Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
        omega
      have hd1 : Disjoint Dn ({0} : Finset ℤ) := by
        rw [Finset.disjoint_right]
        intro x hx0 hxn
        rw [Finset.mem_singleton.mp hx0] at hxn
        have := Finset.mem_Icc.mp hxn
        omega
      have hd2 : Disjoint (Dn ∪ ({0} : Finset ℤ)) Dp := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        have h2 := Finset.mem_Icc.mp hx2
        rcases Finset.mem_union.mp hx1 with h1 | h0
        · have := Finset.mem_Icc.mp h1; omega
        · rw [Finset.mem_singleton.mp h0] at h2; omega
      rw [hsplit, Finset.sum_union hd2, Finset.sum_union hd1,
        Finset.sum_singleton, abs_zero, sum_abs_Icc_neg (h - 1), sum_abs_Icc_pos h]
      obtain ⟨c1, hc1⟩ := Nat.even_mul_succ_self (h - 1)
      obtain ⟨c2, hc2⟩ := Nat.even_mul_succ_self h
      have hhcancel : h - 1 + 1 = h := by omega
      rw [hhcancel] at hc1 ⊢
      have hdiv1 : (h - 1) * h / 2 = c1 := by omega
      have hdiv2 : h * (h + 1) / 2 = c2 := by omega
      change _ < Q
      rw [hdiv1, hdiv2, hQeq]
      have hsum_c : c1 + c2 = h * h := by nlinarith
      have hsum_z : (c1 : ℤ) + (c2 : ℤ) = (h : ℤ) ^ 2 := by
        have : ((c1 + c2 : ℕ) : ℤ) = ((h * h : ℕ) : ℤ) := by rw [hsum_c]
        push_cast at this
        linarith
      linarith
  · -- Odd case k = 2h + 1: D = [−h, h]
    let D : Finset ℤ := Finset.Icc (-(h : ℤ)) (h : ℤ)
    let C : Finset ℤ := D.image (fun d => d + Q)
    have hinj : Function.Injective (fun d : ℤ => d + Q) := add_left_injective Q
    have hDcard : D.card = 2 * h + 1 := by
      rw [Int.card_Icc]
      omega
    have hQeq : Q = (h : ℤ) * ((h : ℤ) + 1) + 1 := by
      have hdiv : (2 * h + 1) ^ 2 / 4 = h * (h + 1) := by
        have : (2 * h + 1) ^ 2 = 4 * (h * (h + 1)) + 1 := by ring
        omega
      simp only [Q, hdiv]
      push_cast
      ring
    refine ⟨C, ?_, ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective D hinj, hDcard]
    · intro c hc
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
      have hd' := Finset.mem_Icc.mp hd
      rw [hQeq]
      nlinarith
    · refine Finset.mem_image.mpr ⟨0, Finset.mem_Icc.mpr (by omega), by ring⟩
    · apply weaklyCarryGood_of_sum_abs_sub_lt
      rw [Finset.sum_image (fun a _ b _ hab => hinj hab)]
      have hsimp : ∑ d ∈ D, |(d + Q) - Q| = ∑ d ∈ D, |d| :=
        Finset.sum_congr rfl (fun d _ => by ring_nf)
      rw [hsimp]
      let Dn := Finset.Icc (-(h : ℤ)) (-1 : ℤ)
      let Dp := Finset.Icc (1 : ℤ) (h : ℤ)
      have hsplit : D = Dn ∪ ({0} : Finset ℤ) ∪ Dp := by
        ext x
        simp only [D, Dn, Dp, Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
        omega
      have hd1 : Disjoint Dn ({0} : Finset ℤ) := by
        rw [Finset.disjoint_right]
        intro x hx0 hxn
        rw [Finset.mem_singleton.mp hx0] at hxn
        have := Finset.mem_Icc.mp hxn
        omega
      have hd2 : Disjoint (Dn ∪ ({0} : Finset ℤ)) Dp := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        have h2 := Finset.mem_Icc.mp hx2
        rcases Finset.mem_union.mp hx1 with h1 | h0
        · have := Finset.mem_Icc.mp h1; omega
        · rw [Finset.mem_singleton.mp h0] at h2; omega
      change _ < Q
      rw [hsplit, Finset.sum_union hd2, Finset.sum_union hd1,
        Finset.sum_singleton, abs_zero, sum_abs_Icc_neg h, sum_abs_Icc_pos h, hQeq]
      obtain ⟨c, hc⟩ := Nat.even_mul_succ_self h
      have hdiv : h * (h + 1) / 2 = c := by omega
      rw [hdiv]
      have hcz : (h : ℤ) * ((h : ℤ) + 1) = (c : ℤ) + (c : ℤ) := by exact_mod_cast hc
      linarith

/-- **Remark 4.5 (sharpness of Proposition 3, `Q ∉ C` bound).**
For every `k ≥ 1`, there exist a `k`-element subset `C` of positive integers
and `Q = ⌊(k+1)²/4⌋ + 1` with `Q ∉ C` and `WeaklyCarryGood C Q`. -/
theorem quadratic_radix_barrier_not_mem_sharp {k : ℕ} (hk : 1 ≤ k) :
    ∃ C : Finset ℤ, C.card = k ∧ (∀ c ∈ C, 1 ≤ c) ∧
      (((k + 1) ^ 2 / 4 : ℕ) : ℤ) + 1 ∉ C ∧
      WeaklyCarryGood C ((((k + 1) ^ 2 / 4 : ℕ) : ℤ) + 1) := by
  classical
  let Q : ℤ := (((k + 1) ^ 2 / 4 : ℕ) : ℤ) + 1
  rcases Nat.even_or_odd' k with ⟨h, rfl | rfl⟩
  · -- Even case k = 2h (with h ≥ 1): D = [−h, −1] ∪ [1, h]
    have hh : 1 ≤ h := by omega
    let Dn := Finset.Icc (-(h : ℤ)) (-1 : ℤ)
    let Dp := Finset.Icc (1 : ℤ) (h : ℤ)
    let D : Finset ℤ := Dn ∪ Dp
    let C : Finset ℤ := D.image (fun d => d + Q)
    have hinj : Function.Injective (fun d : ℤ => d + Q) := add_left_injective Q
    have hdisj : Disjoint Dn Dp := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 := Finset.mem_Icc.mp hx1
      have h2 := Finset.mem_Icc.mp hx2
      omega
    have hQeq : Q = (h : ℤ) * ((h : ℤ) + 1) + 1 := by
      have hdiv : (2 * h + 1) ^ 2 / 4 = h * (h + 1) := by
        have : (2 * h + 1) ^ 2 = 4 * (h * (h + 1)) + 1 := by ring
        omega
      simp only [Q, hdiv]
      push_cast
      ring
    refine ⟨C, ?_, ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective D hinj, Finset.card_union_of_disjoint hdisj,
        Int.card_Icc, Int.card_Icc]
      omega
    · intro c hc
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
      rcases Finset.mem_union.mp hd with hdn | hdp
      · have := Finset.mem_Icc.mp hdn; rw [hQeq]; nlinarith
      · have := Finset.mem_Icc.mp hdp; rw [hQeq]; nlinarith
    · intro hmem
      obtain ⟨d, hd, hdQ⟩ := Finset.mem_image.mp hmem
      have hd0 : d = 0 := by linarith
      subst hd0
      rcases Finset.mem_union.mp hd with hdn | hdp
      · have := Finset.mem_Icc.mp hdn; omega
      · have := Finset.mem_Icc.mp hdp; omega
    · apply weaklyCarryGood_of_sum_abs_sub_lt
      rw [Finset.sum_image (fun a _ b _ hab => hinj hab)]
      have hsimp : ∑ d ∈ D, |(d + Q) - Q| = ∑ d ∈ D, |d| :=
        Finset.sum_congr rfl (fun d _ => by ring_nf)
      change _ < Q
      rw [hsimp, Finset.sum_union hdisj, sum_abs_Icc_neg h, sum_abs_Icc_pos h, hQeq]
      obtain ⟨c, hc⟩ := Nat.even_mul_succ_self h
      have hdiv : h * (h + 1) / 2 = c := by omega
      rw [hdiv]
      have hcz : (h : ℤ) * ((h : ℤ) + 1) = (c : ℤ) + (c : ℤ) := by exact_mod_cast hc
      linarith
  · -- Odd case k = 2h + 1: D = [−h, −1] ∪ [1, h+1]
    let Dn := Finset.Icc (-(h : ℤ)) (-1 : ℤ)
    let Dp := Finset.Icc (1 : ℤ) (((h + 1 : ℕ) : ℤ))
    let D : Finset ℤ := Dn ∪ Dp
    let C : Finset ℤ := D.image (fun d => d + Q)
    have hinj : Function.Injective (fun d : ℤ => d + Q) := add_left_injective Q
    have hdisj : Disjoint Dn Dp := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 := Finset.mem_Icc.mp hx1
      have h2 := Finset.mem_Icc.mp hx2
      omega
    have hQeq : Q = ((h : ℤ) + 1) ^ 2 + 1 := by
      have hdiv : (2 * h + 1 + 1) ^ 2 / 4 = (h + 1) ^ 2 := by
        have : (2 * h + 1 + 1) ^ 2 = 4 * (h + 1) ^ 2 := by ring
        omega
      simp only [Q, hdiv]
      push_cast
      ring
    refine ⟨C, ?_, ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective D hinj, Finset.card_union_of_disjoint hdisj,
        Int.card_Icc, Int.card_Icc]
      omega
    · intro c hc
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
      rcases Finset.mem_union.mp hd with hdn | hdp
      · have := Finset.mem_Icc.mp hdn; rw [hQeq]; nlinarith
      · have := Finset.mem_Icc.mp hdp; rw [hQeq]; nlinarith
    · intro hmem
      obtain ⟨d, hd, hdQ⟩ := Finset.mem_image.mp hmem
      have hd0 : d = 0 := by linarith
      subst hd0
      rcases Finset.mem_union.mp hd with hdn | hdp
      · have := Finset.mem_Icc.mp hdn; omega
      · have := Finset.mem_Icc.mp hdp; omega
    · apply weaklyCarryGood_of_sum_abs_sub_lt
      rw [Finset.sum_image (fun a _ b _ hab => hinj hab)]
      have hsimp : ∑ d ∈ D, |(d + Q) - Q| = ∑ d ∈ D, |d| :=
        Finset.sum_congr rfl (fun d _ => by ring_nf)
      change _ < Q
      rw [hsimp, Finset.sum_union hdisj, sum_abs_Icc_neg h, sum_abs_Icc_pos (h + 1), hQeq]
      obtain ⟨c1, hc1⟩ := Nat.even_mul_succ_self h
      obtain ⟨c2, hc2⟩ := Nat.even_mul_succ_self (h + 1)
      have hdiv1 : h * (h + 1) / 2 = c1 := by omega
      have hdiv2 : (h + 1) * (h + 1 + 1) / 2 = c2 := by omega
      rw [hdiv1, hdiv2]
      have hsum_c : c1 + c2 = (h + 1) * (h + 1) := by nlinarith
      have hsum_z : (c1 : ℤ) + (c2 : ℤ) = ((h : ℤ) + 1) ^ 2 := by
        have : ((c1 + c2 : ℕ) : ℤ) = (((h + 1) * (h + 1) : ℕ) : ℤ) := by rw [hsum_c]
        push_cast at this
        linarith
      linarith

end Erdos875
