import Mathlib

/-!
# Sharp local carry lemma for the Mazur AP block (Erdős #875, Proposition 1)

This file formalizes Proposition 1 of the candidate bundle
`candidates/875-carry-lemma-bundle.md` (attack run
`problems/875/runs/20260709-224805-codex-attack-ratio-wide-window.md`):

For the Mazur AP block `C_m = {1 + i(m+1) : 0 ≤ i < m}` and `Q_m = m² + m + 1`:

* **`local_carry`** (Prop 1, main direction): if `Y ∈ Δ_t(C_m)` and
  `Y = Q_m·w − u` with `|u| ≤ ⌈m/2⌉`, then `t = w − u`.
  There is **no** restriction on the quotient `w` (Mazur's published lemma
  needs `4|u| < m` and `2|w| < m`).

* **`local_carry_sharp`** (Prop 1, sharpness): at `|u| = ⌈m/2⌉ + 1` the
  conclusion fails, for every `m ≥ 1`.

Here `Δ_t(C) = { Σ_{x∈U} x − Σ_{x∈V} x : U, V ⊆ C, |U| − |V| = t }` is
encoded by the predicate `IsSignedSum`.

The radius hypothesis `|u| ≤ ⌈m/2⌉` is stated division-free as
`2·|u| ≤ m + 1`, which is equivalent for integers (`local_carry_natAbs`
restates it as `u.natAbs ≤ (m+1)/2`, and `(m+1)/2 = ⌈m/2⌉` in ℕ).

Definitions are written fresh from the paper statement (Mazur's Lean repo
`lechmazur/erdos_875` carries no license file, so no code is reused from
it; only the general shape — index decompositions over `Finset.range m` —
is common mathematical content).

## Proof outline (paper steps, as verified by the Gate-2 critique)

With `d = m + 1`, `Q = m·d + 1 = m² + m + 1`, `L = m(m+1)/2`:

1. Each block element is `c_i = 1 + d·i = Q − d·(m − i)`; hence any
   `Y ∈ Δ_t(C_m)` decomposes as `Y = Q·t − d·z` with
   `z = Σ_{i∈S}(m−i) − Σ_{i∈T}(m−i)` for index sets `S, T ⊆ range m`,
   and `|z| ≤ L` (lemmas `sum_mazurAP`, `indexWeight_*`, `block_decomp`).
2. If also `Y = Q·w − u`, set `v = w − t`; then `Q·v = u − d·z`, and since
   `Q ≡ 1 (mod d)` we get `v = u + ℓ·d` and `z = −m·u − ℓ·Q`
   (all inside `carry_arith`, where `ℓ` is produced explicitly as
   `ℓ = −z − m·(w−t)`, so no divisibility API is needed).
3. If `ℓ ≠ 0` then `|z| ≥ Q − m·|u| ≥ Q − m·⌈m/2⌉ > L`, contradiction;
   division-free: `2·m·⌈m/2⌉ ≤ m(m+1) < m² + m + 2 = 2Q − 2L`, which even
   avoids the paper's parity split. Hence `ℓ = 0`, i.e. `t = w − u`.
4. Sharpness: with `u₀ = ⌈m/2⌉ + 1` and `z₀ = Q − m·u₀` one checks
   `0 ≤ z₀ ≤ L` (here a parity case split IS needed for the upper bound),
   realizes `z₀` as a subset sum of `{1, …, m}` (`exists_subset_Icc_sum`),
   and takes `w = t + u₀ − d`, giving `Y = Q·w − u₀` with `t ≠ w − u₀`.
-/

namespace Erdos875

open Finset

/-! ## Definitions -/

/-- `IsSignedSum C t Y` says `Y ∈ Δ_t(C)`: there are subsets `U, V ⊆ C` with
`|U| − |V| = t` and `Σ_{x∈U} x − Σ_{x∈V} x = Y`. -/
def IsSignedSum (C : Finset ℤ) (t Y : ℤ) : Prop :=
  ∃ U V : Finset ℤ, U ⊆ C ∧ V ⊆ C ∧
    (U.card : ℤ) - (V.card : ℤ) = t ∧ (∑ x ∈ U, x) - (∑ x ∈ V, x) = Y

/-- The `i`-th element of the Mazur AP block: `c_i = 1 + i(m+1)`. -/
def mazurElt (m : ℕ) (i : ℕ) : ℤ := 1 + (i : ℤ) * ((m : ℤ) + 1)

/-- The Mazur AP block `C_m = {1 + i(m+1) : 0 ≤ i < m}` as a `Finset ℤ`. -/
def mazurBlock (m : ℕ) : Finset ℤ := (Finset.range m).image (mazurElt m)

/-- The Mazur radix `Q_m = m² + m + 1`. -/
def mazurQ (m : ℕ) : ℤ := (m : ℤ) ^ 2 + (m : ℤ) + 1

/-- The index weight `Σ_{i∈S} (m − i)` (the paper's `z`-coordinate). -/
def indexWeight (m : ℕ) (S : Finset ℕ) : ℤ := ∑ i ∈ S, ((m : ℤ) - (i : ℤ))

/-! ## Step 0: elementary Finset plumbing -/

theorem mazurElt_injective (m : ℕ) : Function.Injective (mazurElt m) := by
  intro a b hab
  unfold mazurElt at hab
  have hm : ((m : ℤ) + 1) ≠ 0 := by positivity
  have h : (a : ℤ) * ((m : ℤ) + 1) = (b : ℤ) * ((m : ℤ) + 1) := by linarith
  exact_mod_cast mul_right_cancel₀ hm h

/-- Any subset of an image is the image of a subset (pullback lemma). -/
theorem exists_image_preimage {α β : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → β} {t : Finset α} {U : Finset β} (hU : U ⊆ t.image f) :
    ∃ S : Finset α, S ⊆ t ∧ S.image f = U := by
  classical
  refine ⟨t.filter (fun a => f a ∈ U), Finset.filter_subset _ _, ?_⟩
  ext b
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨a, ⟨_, hfa⟩, rfl⟩
    exact hfa
  · intro hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (hU hb)
    exact ⟨a, ⟨ha, hb⟩, rfl⟩

/-! ## Step 1: the decomposition `Y = Q·t − d·z` with `|z| ≤ L` -/

/-- Pointwise identity `c_i = Q − d·(m−i)`, summed over an index set:
`Σ_{i∈S} c_i = Q·|S| − d·(Σ_{i∈S} (m−i))`. -/
theorem sum_mazurAP (m : ℕ) (S : Finset ℕ) :
    ∑ i ∈ S, mazurElt m i
      = mazurQ m * S.card - ((m : ℤ) + 1) * indexWeight m S := by
  unfold indexWeight
  have h1 : mazurQ m * (S.card : ℤ) = ∑ _i ∈ S, mazurQ m := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have h2 : ((m : ℤ) + 1) * ∑ i ∈ S, ((m : ℤ) - (i : ℤ))
      = ∑ i ∈ S, ((m : ℤ) + 1) * ((m : ℤ) - (i : ℤ)) := by
    rw [Finset.mul_sum]
  rw [h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold mazurElt mazurQ
  ring

/-- `0 ≤ Σ_{i∈S}(m−i)` for `S ⊆ range m`. -/
theorem indexWeight_nonneg {m : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range m) :
    0 ≤ indexWeight m S :=
  Finset.sum_nonneg fun i hi => by
    have := Finset.mem_range.mp (hS hi)
    omega

/-- `Σ_{i∈S}(m−i) ≤ Σ_{i<m}(m−i)` for `S ⊆ range m`. -/
theorem indexWeight_le {m : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range m) :
    indexWeight m S ≤ indexWeight m (Finset.range m) :=
  Finset.sum_le_sum_of_subset_of_nonneg hS fun i hi _ => by
    have := Finset.mem_range.mp hi
    omega

/-- Gauss: `2·Σ_{i<m}(m−i) = m(m+1)`, i.e. the full weight is `L = m(m+1)/2`. -/
theorem two_indexWeight_range (m : ℕ) :
    2 * indexWeight m (Finset.range m) = (m : ℤ) * ((m : ℤ) + 1) := by
  unfold indexWeight
  induction m with
  | zero => simp
  | succ m ih =>
      have step : ∑ i ∈ Finset.range (m + 1), (((m + 1 : ℕ) : ℤ) - (i : ℤ))
          = (∑ i ∈ Finset.range m, ((m : ℤ) - (i : ℤ))) + ((m : ℤ) + 1) := by
        rw [Finset.sum_range_succ]
        have h : ∀ i ∈ Finset.range m,
            (((m + 1 : ℕ) : ℤ) - (i : ℤ)) = ((m : ℤ) - (i : ℤ)) + 1 := by
          intro i _
          push_cast
          ring
        rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
      rw [step]
      push_cast
      linear_combination ih

/-- **Step 1 bundled**: every `Y ∈ Δ_t(C_m)` has the shape `Y = Q·t − d·z`
with `2|z| ≤ m(m+1)` (i.e. `|z| ≤ L = m(m+1)/2`). -/
theorem block_decomp {m : ℕ} {t Y : ℤ} (h : IsSignedSum (mazurBlock m) t Y) :
    ∃ z : ℤ, 2 * |z| ≤ (m : ℤ) * ((m : ℤ) + 1) ∧
      Y = mazurQ m * t - ((m : ℤ) + 1) * z := by
  obtain ⟨U, V, hU, hV, ht, hY⟩ := h
  obtain ⟨S, hSsub, hSU⟩ := exists_image_preimage (f := mazurElt m) hU
  obtain ⟨T, hTsub, hTV⟩ := exists_image_preimage (f := mazurElt m) hV
  have hinj := mazurElt_injective m
  have hcardS : U.card = S.card := by
    rw [← hSU]
    exact Finset.card_image_of_injective S hinj
  have hcardT : V.card = T.card := by
    rw [← hTV]
    exact Finset.card_image_of_injective T hinj
  have hsumS : ∑ x ∈ U, x = ∑ i ∈ S, mazurElt m i := by
    rw [← hSU]
    exact Finset.sum_image fun a _ b _ hab => hinj hab
  have hsumT : ∑ x ∈ V, x = ∑ i ∈ T, mazurElt m i := by
    rw [← hTV]
    exact Finset.sum_image fun a _ b _ hab => hinj hab
  refine ⟨indexWeight m S - indexWeight m T, ?_, ?_⟩
  · -- |z| ≤ L via 0 ≤ wt(·) ≤ wt(range m) and 2·wt(range m) = m(m+1)
    have h1 := indexWeight_nonneg hSsub
    have h2 := indexWeight_le hSsub
    have h3 := indexWeight_nonneg hTsub
    have h4 := indexWeight_le hTsub
    have h5 := two_indexWeight_range m
    have habs : |indexWeight m S - indexWeight m T|
        ≤ indexWeight m (Finset.range m) := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  · -- Y = Q·t − d·z
    have hSm := sum_mazurAP m S
    have hTm := sum_mazurAP m T
    rw [hsumS, hsumT] at hY
    rw [← ht, hcardS, hcardT]
    linear_combination -hY + hSm - hTm

/-! ## Steps 2–3: the arithmetic core (pure integer arithmetic) -/

/-- **Arithmetic core of Prop 1** (paper steps 2–3). If
`Y = Q·t − d·z = Q·w − u` with `2|u| ≤ m+1` (`|u| ≤ ⌈m/2⌉`) and
`2|z| ≤ m(m+1)` (`|z| ≤ L`), then `t = w − u`. -/
theorem carry_arith {m t Y u w z : ℤ} (hm : 1 ≤ m)
    (hYt : Y = (m ^ 2 + m + 1) * t - (m + 1) * z)
    (hYw : Y = (m ^ 2 + m + 1) * w - u)
    (hu : 2 * |u| ≤ m + 1)
    (hz : 2 * |z| ≤ m * (m + 1)) :
    t = w - u := by
  -- v := w − t satisfies Q·v = u − d·z
  have hv : (m ^ 2 + m + 1) * (w - t) = u - (m + 1) * z := by
    linear_combination hYt - hYw
  -- Q ≡ 1 (mod d): the carry shift ℓ, produced explicitly
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℤ, ℓ = -z - m * (w - t) := ⟨_, rfl⟩
  -- v = u + ℓ·d  (paper: v ≡ u mod d)
  have hvl : w - t = u + (m + 1) * ℓ := by
    rw [hℓ]
    linear_combination hv
  -- key identity (paper eq. (1)): z = −m·u − ℓ·Q
  have hkey : z = -(m * u) - (m ^ 2 + m + 1) * ℓ := by
    rw [hℓ]
    linear_combination (-m) * hv
  -- unpack the absolute values
  have hu1 : -(m + 1) ≤ 2 * u := by
    have := neg_abs_le u
    linarith
  have hu2 : 2 * u ≤ m + 1 := by
    have := le_abs_self u
    linarith
  have hz1 : -(m * (m + 1)) ≤ 2 * z := by
    have := neg_abs_le z
    linarith
  have hz2 : 2 * z ≤ m * (m + 1) := by
    have := le_abs_self z
    linarith
  have hQpos : (0 : ℤ) < m ^ 2 + m + 1 := by positivity
  -- trichotomy on ℓ (paper: ℓ ≠ 0 forces |z| > L)
  rcases lt_trichotomy ℓ 0 with hneg | hzero | hpos
  · -- ℓ ≤ −1: 2z = −2mu − 2Qℓ ≥ −m(m+1) + 2Q > m(m+1) ≥ 2z
    exfalso
    have hl1 : ℓ ≤ -1 := by omega
    have hb2 : (m ^ 2 + m + 1) * ℓ ≤ (m ^ 2 + m + 1) * (-1) :=
      mul_le_mul_of_nonneg_left hl1 (le_of_lt hQpos)
    have hb1 : m * (2 * u) ≤ m * (m + 1) :=
      mul_le_mul_of_nonneg_left hu2 (by linarith)
    nlinarith [hkey, hz2, hb1, hb2]
  · -- ℓ = 0: v = u, i.e. t = w − u
    rw [hzero] at hvl
    linarith
  · -- ℓ ≥ 1: 2z = −2mu − 2Qℓ ≤ m(m+1) − 2Q < −m(m+1) ≤ 2z
    exfalso
    have hl1 : (1 : ℤ) ≤ ℓ := hpos
    have hb2 : m ^ 2 + m + 1 ≤ (m ^ 2 + m + 1) * ℓ :=
      le_mul_of_one_le_right (le_of_lt hQpos) hl1
    have hb1 : m * (-(2 * u)) ≤ m * (m + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith [hkey, hz1, hb1, hb2]

/-! ## Proposition 1, main direction -/

/-- **Proposition 1 (sharp local carry lemma), main direction.**
For the Mazur AP block `C_m` with radix `Q_m = m² + m + 1`: if
`Y ∈ Δ_t(C_m)` and `Y = Q_m·w − u` with `|u| ≤ ⌈m/2⌉` (stated
division-free as `2|u| ≤ m + 1`), then `t = w − u`.
No hypothesis on the quotient `w` is required. -/
theorem local_carry {m : ℕ} (hm : 1 ≤ m) {t Y u w : ℤ}
    (hY : IsSignedSum (mazurBlock m) t Y)
    (heq : Y = mazurQ m * w - u)
    (hu : 2 * |u| ≤ (m : ℤ) + 1) :
    t = w - u := by
  obtain ⟨z, hz, hYt⟩ := block_decomp hY
  have hm' : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  refine carry_arith (Y := Y) hm' ?_ ?_ hu hz
  · rw [hYt]
    unfold mazurQ
    ring
  · rw [heq]
    unfold mazurQ
    ring

/-- Proposition 1 restated with the radius in the paper's `⌈m/2⌉` form:
`u.natAbs ≤ (m+1)/2`, where `(m+1)/2 = ⌈m/2⌉` in ℕ. -/
theorem local_carry_natAbs {m : ℕ} (hm : 1 ≤ m) {t Y u w : ℤ}
    (hY : IsSignedSum (mazurBlock m) t Y)
    (heq : Y = mazurQ m * w - u)
    (hu : u.natAbs ≤ (m + 1) / 2) :
    t = w - u := by
  refine local_carry hm hY heq ?_
  have h1 : |u| = (u.natAbs : ℤ) := Int.abs_eq_natAbs u
  rw [h1]
  have h2 : 2 * u.natAbs ≤ m + 1 := by omega
  exact_mod_cast h2

/-! ## Step 4: sharpness at radius `⌈m/2⌉ + 1` -/

/-- Every `n` with `2n ≤ k(k+1)` (i.e. `n ≤ L_k`) is a subset sum of
`{1, …, k}`. Elementary induction on `k`. -/
theorem exists_subset_Icc_sum (k : ℕ) :
    ∀ n : ℕ, 2 * n ≤ k * (k + 1) →
      ∃ S ⊆ Finset.Icc 1 k, ∑ i ∈ S, i = n := by
  induction k with
  | zero =>
      intro n hn
      refine ⟨∅, by simp, ?_⟩
      simp only [Finset.sum_empty]
      omega
  | succ k ih =>
      intro n hn
      by_cases h : 2 * n ≤ k * (k + 1)
      · obtain ⟨S, hS, hsum⟩ := ih n h
        exact ⟨S, hS.trans (Finset.Icc_subset_Icc_right (by omega)), hsum⟩
      · rw [not_le] at h
        -- k(k+1) is even, so 2n ≥ k(k+1) + 2; also n ≥ k+1
        obtain ⟨c, hc⟩ := Nat.even_mul_succ_self k
        have hexp : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by
          ring
        have hkk : k ≤ k * k := by nlinarith
        have hck : k ≤ c := by nlinarith
        rw [hexp, hc] at hn
        rw [hc] at h
        -- now everything is linear in n, k, c
        have hnk : k + 1 ≤ n := by omega
        have hrec : 2 * (n - (k + 1)) ≤ c + c := by omega
        rw [← hc] at hrec
        obtain ⟨S, hS, hsum⟩ := ih (n - (k + 1)) hrec
        have hnotmem : k + 1 ∉ S := fun hmem => by
          have := Finset.mem_Icc.mp (hS hmem)
          omega
        refine ⟨insert (k + 1) S, ?_, ?_⟩
        · rw [Finset.insert_subset_iff]
          exact ⟨Finset.mem_Icc.mpr (by omega),
            hS.trans (Finset.Icc_subset_Icc_right (by omega))⟩
        · rw [Finset.sum_insert hnotmem, hsum]
          omega

/-- Realize any `0 ≤ n ≤ L` as an index weight `Σ_{i∈T}(m−i)`, `T ⊆ range m`
(reindex the subset-sum lemma along `j ↦ m − j`). -/
theorem exists_indexWeight (m : ℕ) (n : ℕ) (hn : 2 * n ≤ m * (m + 1)) :
    ∃ T ⊆ Finset.range m, indexWeight m T = (n : ℤ) := by
  obtain ⟨S, hS, hsum⟩ := exists_subset_Icc_sum m n hn
  have hmem : ∀ j ∈ S, 1 ≤ j ∧ j ≤ m := fun j hj => Finset.mem_Icc.mp (hS hj)
  refine ⟨S.image (fun j => m - j), ?_, ?_⟩
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have := hmem j hj
    exact Finset.mem_range.mpr (by omega)
  · unfold indexWeight
    rw [Finset.sum_image (by
      intro a ha b hb hab
      have h1 := hmem a ha
      have h2 := hmem b hb
      dsimp only at hab
      omega)]
    have h : ∀ j ∈ S, ((m : ℤ) - ((m - j : ℕ) : ℤ)) = (j : ℤ) := by
      intro j hj
      have hj' := hmem j hj
      rw [Nat.cast_sub hj'.2]
      ring
    rw [Finset.sum_congr rfl h, ← Nat.cast_sum]
    exact_mod_cast hsum

/-- **Proposition 1, sharpness.** For every `m ≥ 1` there are `t, Y, u, w`
with `|u| = ⌈m/2⌉ + 1` (i.e. `u.natAbs = (m+1)/2 + 1`) such that
`Y ∈ Δ_t(C_m)`, `Y = Q_m·w − u`, but `t ≠ w − u`. So the carry radius
`⌈m/2⌉` in `local_carry` cannot be enlarged, for any `m`. -/
theorem local_carry_sharp {m : ℕ} (hm : 1 ≤ m) :
    ∃ t Y u w : ℤ, IsSignedSum (mazurBlock m) t Y ∧
      Y = mazurQ m * w - u ∧
      u.natAbs = (m + 1) / 2 + 1 ∧
      t ≠ w - u := by
  classical
  have hm' : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  -- the violating carry: u₀ = ⌈m/2⌉ + 1, with r = ⌈m/2⌉ = (m+1)/2
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = (m + 1) / 2 := ⟨_, rfl⟩
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : ℤ, u₀ = (r : ℤ) + 1 := ⟨_, rfl⟩
  -- the target weight: z₀ = Q − m·u₀ ∈ [0, L]
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ℤ, z₀ = mazurQ m - (m : ℤ) * u₀ := ⟨_, rfl⟩
  have hr2 : 2 * (r : ℤ) ≤ (m : ℤ) + 1 := by
    have : 2 * r ≤ m + 1 := by omega
    exact_mod_cast this
  have hz₀nonneg : 0 ≤ z₀ := by
    -- 2z₀ = 2m² + 2 − 2mr ≥ m² − m + 2 > 0
    have hmul : (m : ℤ) * (2 * (r : ℤ)) ≤ (m : ℤ) * ((m : ℤ) + 1) :=
      mul_le_mul_of_nonneg_left hr2 (by linarith)
    have hmsq : (m : ℤ) ≤ (m : ℤ) * (m : ℤ) :=
      le_mul_of_one_le_left (by linarith) hm'
    rw [hz₀, hu₀]
    unfold mazurQ
    nlinarith [hmul, hmsq]
  have hz₀le : 2 * z₀ ≤ (m : ℤ) * ((m : ℤ) + 1) := by
    -- parity split: 2r = m (m even, m ≥ 2) or 2r = m+1 (m odd)
    rcases (by omega : 2 * r = m ∧ 2 ≤ m ∨ 2 * r = m + 1) with ⟨h2r, hm2⟩ | h2r
    · have h2r' : 2 * (r : ℤ) = (m : ℤ) := by exact_mod_cast h2r
      have hm2' : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm2
      have hprod : (m : ℤ) * (2 * (r : ℤ)) = (m : ℤ) * (m : ℤ) := by
        rw [h2r']
      rw [hz₀, hu₀]
      unfold mazurQ
      nlinarith [hprod, hm2']
    · have h2r' : 2 * (r : ℤ) = (m : ℤ) + 1 := by exact_mod_cast h2r
      have hprod : (m : ℤ) * (2 * (r : ℤ)) = (m : ℤ) * ((m : ℤ) + 1) := by
        rw [h2r']
      rw [hz₀, hu₀]
      unfold mazurQ
      nlinarith [hprod, hm']
  -- realize z₀ as an index weight over range m
  have hn2 : 2 * z₀.toNat ≤ m * (m + 1) := by
    have h1 : ((z₀.toNat : ℤ)) = z₀ := Int.toNat_of_nonneg hz₀nonneg
    have h2 : 2 * ((z₀.toNat : ℤ)) ≤ (m : ℤ) * ((m : ℤ) + 1) := by
      rw [h1]
      exact hz₀le
    exact_mod_cast h2
  obtain ⟨T, hTsub, hTwt⟩ := exists_indexWeight m z₀.toNat hn2
  have hTwt' : indexWeight m T = z₀ := by
    rw [hTwt, Int.toNat_of_nonneg hz₀nonneg]
  -- the witness: U = image of T, V = ∅, t = |T|, w = t + u₀ − (m+1)
  obtain ⟨t, hts⟩ : ∃ t : ℤ, t = (T.card : ℤ) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℤ, Y = mazurQ m * t - ((m : ℤ) + 1) * z₀ := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℤ, w = t + u₀ - ((m : ℤ) + 1) := ⟨_, rfl⟩
  refine ⟨t, Y, u₀, w,
    ⟨T.image (mazurElt m), ∅, ?_, Finset.empty_subset _, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- U ⊆ C_m
    unfold mazurBlock
    exact Finset.image_subset_image hTsub
  · -- cardinality defect = t
    rw [Finset.card_image_of_injective T (mazurElt_injective m),
      Finset.card_empty, hts]
    push_cast
    ring
  · -- signed sum = Y
    rw [Finset.sum_empty,
      Finset.sum_image (fun a _ b _ hab => mazurElt_injective m hab),
      sum_mazurAP m T, hTwt', hY, hts]
    ring
  · -- Y = Q·w − u₀
    rw [hY, hw, hz₀]
    unfold mazurQ
    ring
  · -- |u₀| = ⌈m/2⌉ + 1
    rw [hu₀]
    have hcast : ((r : ℤ) + 1) = ((r + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hcast, Int.natAbs_natCast]
    omega
  · -- t ≠ w − u₀ (they differ by d = m+1 > 0)
    rw [hw]
    intro hcontra
    omega

end Erdos875
