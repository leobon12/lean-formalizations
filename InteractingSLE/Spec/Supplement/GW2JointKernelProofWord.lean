/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ChartGauss
import InteractingSLE.Spec.Exist.StagedLawData
import InteractingSLE.Spec.Exist.StagedLaw3Word
import InteractingSLE.Spec.Sec7.StripSysField

/-!
# The returned word: a boundary word read through `R(z) = −1/z`

Packet PROVE-T14-TIP10. The joint chart of a counterflow stop (`GW2JointKernel.jointChart w s = R ∘ f_s ∘ R`) reads
the field through the infinity-source chart `R` once more after the counterflow's own Loewner chart. So the word of
the conditional field in the joint chart is the counterflow's stop word **returned** through `R`: the boundary data
`x ↦ −g(−1/x) + a + l ℓ(x)` (`StripSysField.returnData`, `ℓ = −2π` on `ℝ₋`, `0` on `ℝ₊`). This file builds that word
explicitly and measurably.

* `midPt`, **`fn_ofMid`**: the word with sorted (not necessarily strictly) positions `p` and heights read from a
  function `g` at one point of each complementary interval represents `g` off the positions, whenever `g` is locally
  constant off them (the monotone form of `Restart.BoundaryWord.exists_fn_eq`'s construction);
* `nNeg`, `nPos`, `retPos`, `retCount`, **`retWord a l c`**: for a sorted word `c` the returned positions are the
  images `−1/p` of the positive positions (in order), then `0`, then the images of the negative positions (in order);
  `isSorted_retWord`, **`jumps_retWord`** (`= StripSysField.returnExcept c.jumps`), **`fn_retWord`**
  (`= returnData a l c.fn` off the jumps), **`measurable_retWord`**;
* **`isGFFWithBoundaryData_returnField_retWord`**: the return field of the word's GFF is the GFF of the returned word;
* **`integral_cexp_returnField_gffLaw`**: `∫ exp(i (returnField a l g, φ)) d(gffLaw c)(g) = gaussCF (retWord a l c) φ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE

namespace Theorem14

namespace GW2JointKernel

open Restart Sec7.StripSysField

/-! ### Words with monotone positions and midpoint heights -/

section Mid

/-- A point of the `j`-th complementary interval of the positions `p 0 ≤ ⋯ ≤ p (n − 1)`: left of `p 0`, a midpoint, or
right of `p (n − 1)`. -/
def midPt (n : ℕ) (p : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then p 0 - 1 else if j < n then (p (j - 1) + p j) / 2 else p (n - 1) + 1

/-- For monotone positions, the first `index y` positions are exactly those strictly left of `y`. -/
theorem lt_index_iff_of_monotone {c : BoundaryWord} (hmono : ∀ i j, i ≤ j → j < c.1 → c.2.1 i ≤ c.2.1 j)
    {y : ℝ} {i : ℕ} (hi : i < c.1) : i < c.index y ↔ c.2.1 i < y := by
  classical
  set D := (Finset.range c.1).filter fun j => c.2.1 j < y with hD
  have hdown : ∀ k ∈ D, ∀ j ≤ k, j ∈ D := by
    intro k hk j hjk
    rw [hD, Finset.mem_filter, Finset.mem_range] at hk ⊢
    exact ⟨lt_of_le_of_lt hjk hk.1, lt_of_le_of_lt (hmono j k hjk hk.1) hk.2⟩
  have hDr : D = Finset.range D.card := Exist.StagedLaw.eq_range_card_of_downward hdown
  have hidx : c.index y = D.card := rfl
  rw [hidx]
  constructor
  · intro h
    have hmem : i ∈ D := by rw [hDr]; exact Finset.mem_range.2 h
    rw [hD, Finset.mem_filter] at hmem
    exact hmem.2
  · intro h
    have hmem : i ∈ D := by rw [hD, Finset.mem_filter, Finset.mem_range]; exact ⟨hi, h⟩
    rw [hDr] at hmem
    exact Finset.mem_range.1 hmem

/-- **The word with midpoint heights represents its function off the positions.** For monotone positions `p` on
`[0, n)` and a function `g` locally constant off `p '' [0, n)`, the word `(n, p, j ↦ g (midPt n p j))` has boundary
function `g` off its jumps. -/
theorem fn_ofMid {n : ℕ} {p : ℕ → ℝ} (hmono : ∀ i j, i ≤ j → j < n → p i ≤ p j) {g : ℝ → ℝ}
    (hg : IsPiecewiseConstantBoundaryData g ((Finset.range n).image p)) {y : ℝ}
    (hy : y ∉ (Finset.range n).image p) :
    BoundaryWord.fn ((n, p, fun j => g (midPt n p j)) : BoundaryWord) y = g y := by
  set c : BoundaryWord := (n, p, fun j => g (midPt n p j)) with hc
  have hmono' : ∀ i j, i ≤ j → j < c.1 → c.2.1 i ≤ c.2.1 j := hmono
  have hpJ : ∀ i < n, p i ∈ (Finset.range n).image p := fun i hi =>
    Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩
  set k := c.index y with hk
  have hkn : k ≤ n := c.index_le y
  let I : Set ℝ := {z | (0 < k → p (k - 1) < z) ∧ (k < n → z < p k)}
  have hyI : y ∈ I := by
    refine ⟨fun hk0 => ?_, fun hkn' => ?_⟩
    · exact (lt_index_iff_of_monotone hmono' (show k - 1 < c.1 by simp only [c]; omega)).1 (by omega)
    · have hnot : ¬ c.2.1 k < y := fun hlt =>
        (lt_irrefl k) ((lt_index_iff_of_monotone hmono' (show k < c.1 from hkn')).2 hlt)
      have hne : y ≠ p k := fun he' => hy (he' ▸ hpJ k hkn')
      exact lt_of_le_of_ne (not_lt.1 hnot) hne
  have hsI : midPt n p k ∈ I := by
    by_cases hk0 : k = 0
    · refine ⟨fun h => absurd hk0 (Nat.pos_iff_ne_zero.1 h), fun _ => ?_⟩
      simp only [midPt, hk0, ↓reduceIte]
      linarith
    · by_cases hkn' : k < n
      · have hlt : p (k - 1) < p k := lt_trans (hyI.1 (Nat.pos_of_ne_zero hk0)) (hyI.2 hkn')
        simp only [midPt, hk0, hkn', ↓reduceIte]
        exact ⟨fun _ => by linarith, fun _ => by linarith⟩
      · have hkeq : k = n := le_antisymm hkn (not_lt.1 hkn')
        simp only [midPt, hk0, hkn', ↓reduceIte]
        refine ⟨fun _ => ?_, fun h => absurd h hkn'⟩
        rw [hkeq]
        linarith
  have hIJ : ∀ z ∈ I, z ∉ (Finset.range n).image p := by
    intro z hz hzJ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hzJ
    rw [Finset.mem_range] at hi
    by_cases hik : i < k
    · have hle : p i ≤ p (k - 1) := hmono i (k - 1) (by omega) (by omega)
      exact absurd (lt_of_le_of_lt hle (hz.1 (by omega))) (lt_irrefl _)
    · have hkn' : k < n := lt_of_le_of_lt (not_lt.1 hik) hi
      have hle : p k ≤ p i := hmono k i (not_lt.1 hik) hi
      exact absurd (lt_of_lt_of_le (hz.2 hkn') hle) (lt_irrefl _)
  have hIc : IsPreconnected I := by
    refine OrdConnected.isPreconnected ⟨fun a ha a' ha' z hz => ?_⟩
    exact ⟨fun h => lt_of_lt_of_le (ha.1 h) hz.1, fun h => lt_of_le_of_lt hz.2 (ha'.2 h)⟩
  exact eq_of_germ_isConstant_on (fun z hz => ⟨g z, hg z (hIJ z hz)⟩) hIc hsI hyI

end Mid

/-! ### The returned word -/

section Ret

/-- The number of negative positions of a word. -/
def nNeg (c : BoundaryWord) : ℕ := ((Finset.range c.1).filter fun i => c.2.1 i < 0).card

/-- The number of nonpositive positions of a word. -/
def nNP (c : BoundaryWord) : ℕ := ((Finset.range c.1).filter fun i => c.2.1 i ≤ 0).card

/-- The number of positive positions of a word. -/
def nPos (c : BoundaryWord) : ℕ := c.1 - nNP c

/-- **The returned positions**: `−1/p` for the positive positions `p` (in order), then `0`, then `−1/p` for the
negative positions (in order). -/
def retPos (c : BoundaryWord) (k : ℕ) : ℝ :=
  if k < nPos c then -(c.2.1 (nNP c + k))⁻¹ else if k = nPos c then 0 else -(c.2.1 (k - nPos c - 1))⁻¹

/-- The number of returned positions. -/
def retCount (c : BoundaryWord) : ℕ := nPos c + 1 + nNeg c

/-- **The returned word** of `c`: the positions `retPos c`, and the heights of the return data
`x ↦ −c.fn (−1/x) + a + l ℓ(x)` at one point of each complementary interval. -/
def retWord (a l : ℝ) (c : BoundaryWord) : BoundaryWord :=
  (retCount c, retPos c, fun j => returnData a l c.fn (midPt (retCount c) (retPos c) j))

variable {c : BoundaryWord}

theorem neg_lt_iff (hc : c.IsSorted) {i : ℕ} (hi : i < c.1) : c.2.1 i < 0 ↔ i < nNeg c := by
  classical
  set D := (Finset.range c.1).filter fun j => c.2.1 j < 0 with hD
  have hdown : ∀ k ∈ D, ∀ j ≤ k, j ∈ D := by
    intro k hk j hjk
    rw [hD, Finset.mem_filter, Finset.mem_range] at hk ⊢
    exact ⟨lt_of_le_of_lt hjk hk.1, lt_of_le_of_lt (hc j k hjk hk.1) hk.2⟩
  have hDr : D = Finset.range D.card := Exist.StagedLaw.eq_range_card_of_downward hdown
  change c.2.1 i < 0 ↔ i < D.card
  constructor
  · intro h
    have hmem : i ∈ D := by rw [hD, Finset.mem_filter, Finset.mem_range]; exact ⟨hi, h⟩
    rw [hDr] at hmem
    exact Finset.mem_range.1 hmem
  · intro h
    have hmem : i ∈ D := by rw [hDr]; exact Finset.mem_range.2 h
    rw [hD, Finset.mem_filter] at hmem
    exact hmem.2

theorem nonpos_iff (hc : c.IsSorted) {i : ℕ} (hi : i < c.1) : c.2.1 i ≤ 0 ↔ i < nNP c := by
  classical
  set D := (Finset.range c.1).filter fun j => c.2.1 j ≤ 0 with hD
  have hdown : ∀ k ∈ D, ∀ j ≤ k, j ∈ D := by
    intro k hk j hjk
    rw [hD, Finset.mem_filter, Finset.mem_range] at hk ⊢
    exact ⟨lt_of_le_of_lt hjk hk.1, (hc j k hjk hk.1).trans hk.2⟩
  have hDr : D = Finset.range D.card := Exist.StagedLaw.eq_range_card_of_downward hdown
  change c.2.1 i ≤ 0 ↔ i < D.card
  constructor
  · intro h
    have hmem : i ∈ D := by rw [hD, Finset.mem_filter, Finset.mem_range]; exact ⟨hi, h⟩
    rw [hDr] at hmem
    exact Finset.mem_range.1 hmem
  · intro h
    have hmem : i ∈ D := by rw [hDr]; exact Finset.mem_range.2 h
    rw [hD, Finset.mem_filter] at hmem
    exact hmem.2

theorem nNP_le (c : BoundaryWord) : nNP c ≤ c.1 :=
  (Finset.card_filter_le _ _).trans (Finset.card_range _).le

theorem nNeg_le_nNP (c : BoundaryWord) : nNeg c ≤ nNP c :=
  Finset.card_le_card fun i hi => by
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2.le⟩

theorem nPos_add_nNP (c : BoundaryWord) : nPos c + nNP c = c.1 := by
  have := nNP_le c
  unfold nPos
  omega

theorem pos_of_nNP_le (hc : c.IsSorted) {i : ℕ} (hi : i < c.1) (h : nNP c ≤ i) : 0 < c.2.1 i :=
  lt_of_not_ge fun h' => absurd ((nonpos_iff hc hi).1 h') (not_lt.2 h)

theorem retPos_of_lt {k : ℕ} (hk : k < nPos c) : retPos c k = -(c.2.1 (nNP c + k))⁻¹ := by
  simp only [retPos, hk, ↓reduceIte]

theorem retPos_nPos : retPos c (nPos c) = 0 := by
  simp only [retPos, lt_irrefl, ↓reduceIte]

theorem retPos_of_gt {k : ℕ} (hk : nPos c < k) : retPos c k = -(c.2.1 (k - nPos c - 1))⁻¹ := by
  simp only [retPos, not_lt.2 hk.le, hk.ne', ↓reduceIte]

/-- The positive block of the returned positions is negative. -/
theorem retPos_neg_of_lt (hc : c.IsSorted) {k : ℕ} (hk : k < nPos c) : retPos c k < 0 := by
  rw [retPos_of_lt hk]
  have hpos := pos_of_nNP_le hc (show nNP c + k < c.1 by have := nPos_add_nNP c; omega) (by omega)
  exact neg_neg_of_pos (inv_pos.2 hpos)

/-- The negative block of the returned positions is positive. -/
theorem retPos_pos_of_gt (hc : c.IsSorted) {k : ℕ} (hk : nPos c < k) (hk' : k < retCount c) :
    0 < retPos c k := by
  rw [retPos_of_gt hk]
  have hlt : k - nPos c - 1 < nNeg c := by unfold retCount at hk'; omega
  have hneg := (neg_lt_iff hc (show k - nPos c - 1 < c.1 by
    have := nNeg_le_nNP c; have := nNP_le c; omega)).2 hlt
  exact neg_pos.2 (inv_lt_zero.2 hneg)

/-- **The returned word is sorted.** -/
theorem isSorted_retWord (hc : c.IsSorted) (a l : ℝ) : (retWord a l c).IsSorted := by
  intro i j hij hj
  change retPos c i ≤ retPos c j
  change j < retCount c at hj
  have hsum := nPos_add_nNP c
  have hnn := nNeg_le_nNP c
  rcases lt_trichotomy j (nPos c) with hjp | hjp | hjp
  · -- both in the positive block
    have hip : i < nPos c := lt_of_le_of_lt hij hjp
    rw [retPos_of_lt hip, retPos_of_lt hjp, neg_le_neg_iff]
    have hpi := pos_of_nNP_le hc (show nNP c + i < c.1 by omega) (by omega)
    exact inv_anti₀ hpi (hc _ _ (by omega) (by omega))
  · rcases lt_or_eq_of_le hij with hij' | hij'
    · rw [hjp, retPos_nPos]
      exact (retPos_neg_of_lt hc (show i < nPos c by omega)).le
    · rw [hij']
  · rcases lt_trichotomy i (nPos c) with hip | hip | hip
    · exact ((retPos_neg_of_lt hc hip).trans (retPos_pos_of_gt hc hjp hj)).le
    · rw [hip, retPos_nPos]
      exact (retPos_pos_of_gt hc hjp hj).le
    · rw [retPos_of_gt hip, retPos_of_gt hjp, neg_le_neg_iff]
      have hjlt : j - nPos c - 1 < nNeg c := by unfold retCount at hj; omega
      have hneg := (neg_lt_iff hc (show j - nPos c - 1 < c.1 by omega)).2 hjlt
      have hij2 : c.2.1 (i - nPos c - 1) ≤ c.2.1 (j - nPos c - 1) :=
        hc (i - nPos c - 1) (j - nPos c - 1) (by omega) (by omega)
      exact (inv_le_inv_of_neg hneg (lt_of_le_of_lt hij2 hneg)).2 hij2

/-- **The jumps of the returned word** are `0` and the images `−1/p` of the jumps of `c`. -/
theorem jumps_retWord (hc : c.IsSorted) (a l : ℝ) : (retWord a l c).jumps = returnExcept c.jumps := by
  classical
  have hsum := nPos_add_nNP c
  have hnn := nNeg_le_nNP c
  ext y
  change y ∈ (Finset.range (retCount c)).image (retPos c) ↔
    y ∈ insert 0 (((Finset.range c.1).image c.2.1).image fun w => -w⁻¹)
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_insert]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rcases lt_trichotomy k (nPos c) with hkp | hkp | hkp
    · right
      exact ⟨c.2.1 (nNP c + k), ⟨nNP c + k, by omega, rfl⟩, (retPos_of_lt hkp).symm⟩
    · left
      rw [hkp, retPos_nPos]
    · right
      have hklt : k - nPos c - 1 < nNeg c := by unfold retCount at hk; omega
      exact ⟨c.2.1 (k - nPos c - 1), ⟨k - nPos c - 1, by omega, rfl⟩, (retPos_of_gt hkp).symm⟩
  · rintro (rfl | ⟨w, ⟨i, hi, rfl⟩, rfl⟩)
    · exact ⟨nPos c, by unfold retCount; omega, retPos_nPos⟩
    · rcases lt_trichotomy (c.2.1 i) 0 with hneg | hzero | hpos
      · have hin := (neg_lt_iff hc hi).1 hneg
        refine ⟨nPos c + 1 + i, by unfold retCount; omega, ?_⟩
        rw [retPos_of_gt (by omega), show nPos c + 1 + i - nPos c - 1 = i by omega]
      · refine ⟨nPos c, by unfold retCount; omega, ?_⟩
        rw [retPos_nPos, hzero, inv_zero, neg_zero]
      · have hin : nNP c ≤ i := not_lt.1 fun h => absurd ((nonpos_iff hc hi).2 h) (not_le.2 hpos)
        refine ⟨i - nNP c, by unfold retCount; omega, ?_⟩
        rw [retPos_of_lt (by omega), show nNP c + (i - nNP c) = i by omega]

/-- **The boundary function of the returned word** is the return data off its jumps. -/
theorem fn_retWord (hc : c.IsSorted) (a l : ℝ) {y : ℝ} (hy : y ∉ (retWord a l c).jumps) :
    (retWord a l c).fn y = returnData a l c.fn y := by
  have hJ := jumps_retWord hc a l
  have hmono : ∀ i j, i ≤ j → j < retCount c → retPos c i ≤ retPos c j := isSorted_retWord hc a l
  have hg : IsPiecewiseConstantBoundaryData (returnData a l c.fn)
      ((Finset.range (retCount c)).image (retPos c)) := by
    have h := isPiecewiseConstant_returnData a l c.isPiecewiseConstantBoundaryData
    rw [← hJ] at h
    exact h
  exact fn_ofMid hmono hg hy

end Ret

/-! ### Measurability -/

section Meas

variable {α : Type*} [MeasurableSpace α]

theorem measurable_card_filter_lt (n : ℕ) {f : α → ℕ → ℝ} {y : α → ℝ} (hf : ∀ i, Measurable fun x => f x i)
    (hy : Measurable y) : Measurable fun x => ((Finset.range n).filter fun i => f x i < y x).card := by
  simp_rw [Finset.card_filter]
  exact Finset.measurable_sum _ fun i _ =>
    Measurable.ite (measurableSet_lt (hf i) hy) measurable_const measurable_const

theorem measurable_card_filter_le (n : ℕ) {f : α → ℕ → ℝ} {y : α → ℝ} (hf : ∀ i, Measurable fun x => f x i)
    (hy : Measurable y) : Measurable fun x => ((Finset.range n).filter fun i => f x i ≤ y x).card := by
  simp_rw [Finset.card_filter]
  exact Finset.measurable_sum _ fun i _ =>
    Measurable.ite (measurableSet_le (hf i) hy) measurable_const measurable_const

/-- Every function on `ℕ × ℕ` is measurable. -/
theorem measurable_nat_prod {β : Type*} [MeasurableSpace β] (g : ℕ × ℕ → β) : Measurable g :=
  measurable_from_prod_countable_left fun _ => measurable_from_nat

/-- A coordinate of a measurable sequence at a measurable index is measurable. -/
theorem measurable_apply_index {x : α → ℕ → ℝ} (hx : ∀ i, Measurable fun a => x a i) {m : α → ℕ}
    (hm : Measurable m) : Measurable fun a => x a (m a) := by
  have h : Measurable fun p : α × ℕ => x p.1 p.2 := measurable_from_prod_countable_left fun j => hx j
  exact h.comp (measurable_id.prodMk hm)

/-- **The boundary function of a word with fixed length and measurable entries, at a measurable point.** -/
theorem measurable_fn_comp (n : ℕ) {x : α → (ℕ → ℝ) × (ℕ → ℝ)} (hx : Measurable x) {y : α → ℝ}
    (hy : Measurable y) : Measurable fun a => BoundaryWord.fn ((n, x a) : BoundaryWord) (y a) := by
  have h1 : ∀ i, Measurable fun a => (x a).1 i := fun i =>
    (measurable_pi_apply i).comp (measurable_fst.comp hx)
  have h2 : ∀ i, Measurable fun a => (x a).2 i := fun i =>
    (measurable_pi_apply i).comp (measurable_snd.comp hx)
  exact measurable_apply_index h2 (measurable_card_filter_lt n h1 hy)

theorem measurable_liftBoundary : Measurable liftBoundary :=
  Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const

/-- The returned positions with the counts given as parameters. -/
def retPosAux (n m : ℕ) (p : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k < n - m then -(p (m + k))⁻¹ else if k = n - m then 0 else -(p (k - (n - m) - 1))⁻¹

theorem retPos_eq_aux (c : BoundaryWord) : retPos c = retPosAux c.1 (nNP c) c.2.1 := rfl

theorem measurable_retPosAux_apply (n m k : ℕ) : Measurable fun p : ℕ → ℝ => retPosAux n m p k := by
  unfold retPosAux
  split_ifs
  · exact ((measurable_pi_apply _).inv).neg
  · exact measurable_const
  · exact ((measurable_pi_apply _).inv).neg

variable (n : ℕ)

theorem measurable_nNP_mk : Measurable fun x : (ℕ → ℝ) × (ℕ → ℝ) => nNP ((n, x) : BoundaryWord) :=
  measurable_card_filter_le n (fun i => (measurable_pi_apply i).comp measurable_fst) measurable_const

theorem measurable_nNeg_mk : Measurable fun x : (ℕ → ℝ) × (ℕ → ℝ) => nNeg ((n, x) : BoundaryWord) :=
  measurable_card_filter_lt n (fun i => (measurable_pi_apply i).comp measurable_fst) measurable_const

theorem measurable_retCount_mk : Measurable fun x : (ℕ → ℝ) × (ℕ → ℝ) => retCount ((n, x) : BoundaryWord) := by
  have h := (measurable_nat_prod fun q : ℕ × ℕ => n - q.1 + 1 + q.2).comp
    ((measurable_nNP_mk n).prodMk (measurable_nNeg_mk n))
  exact h

theorem measurable_retPos_mk (k : ℕ) :
    Measurable fun x : (ℕ → ℝ) × (ℕ → ℝ) => retPos ((n, x) : BoundaryWord) k := by
  have h : Measurable fun q : ((ℕ → ℝ) × (ℕ → ℝ)) × ℕ => retPosAux n q.2 q.1.1 k :=
    measurable_from_prod_countable_left fun m => (measurable_retPosAux_apply n m k).comp measurable_fst
  have h2 := h.comp (measurable_id.prodMk (measurable_nNP_mk n))
  exact h2

theorem measurable_midPt_mk (j : ℕ) : Measurable fun x : (ℕ → ℝ) × (ℕ → ℝ) =>
    midPt (retCount ((n, x) : BoundaryWord)) (retPos ((n, x) : BoundaryWord)) j := by
  have h : Measurable fun q : ((ℕ → ℝ) × (ℕ → ℝ)) × ℕ => midPt q.2 (retPos ((n, q.1) : BoundaryWord)) j := by
    refine measurable_from_prod_countable_left fun N => ?_
    change Measurable fun x : (ℕ → ℝ) × (ℕ → ℝ) => midPt N (retPos ((n, x) : BoundaryWord)) j
    unfold midPt
    split_ifs with h0 hN
    · exact (measurable_retPos_mk n 0).sub measurable_const
    · exact ((measurable_retPos_mk n _).add (measurable_retPos_mk n _)).div_const _
    · exact (measurable_retPos_mk n _).add measurable_const
  have h2 := h.comp (measurable_id.prodMk (measurable_retCount_mk n))
  exact h2

theorem measurable_returnData_fn_mk (a l : ℝ) {y : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ} (hy : Measurable y) :
    Measurable fun x : (ℕ → ℝ) × (ℕ → ℝ) => returnData a l (BoundaryWord.fn ((n, x) : BoundaryWord)) (y x) := by
  have h1 : Measurable fun x : (ℕ → ℝ) × (ℕ → ℝ) => BoundaryWord.fn ((n, x) : BoundaryWord) (-(y x)⁻¹) :=
    measurable_fn_comp n measurable_id hy.inv.neg
  have h2 : Measurable fun x : (ℕ → ℝ) × (ℕ → ℝ) => liftBoundary (y x) := measurable_liftBoundary.comp hy
  exact (h1.neg.add_const a).add (h2.const_mul l)

/-- **The returned word is a measurable function of the word.** -/
theorem measurable_retWord (a l : ℝ) : Measurable (retWord a l) := by
  set G : ((ℕ → ℝ) × (ℕ → ℝ)) × ℕ → BoundaryWord := fun q => retWord a l (q.2, q.1) with hG
  have hGm : Measurable G := by
    refine measurable_from_prod_countable_left fun n => ?_
    have hh : ∀ j, Measurable fun x : (ℕ → ℝ) × (ℕ → ℝ) =>
        returnData a l (BoundaryWord.fn ((n, x) : BoundaryWord))
          (midPt (retCount ((n, x) : BoundaryWord)) (retPos ((n, x) : BoundaryWord)) j) := fun j =>
      measurable_returnData_fn_mk n a l (measurable_midPt_mk n j)
    exact (measurable_retCount_mk n).prodMk
      ((measurable_pi_iff.2 (measurable_retPos_mk n)).prodMk (measurable_pi_iff.2 hh))
  exact hGm.comp (measurable_snd.prodMk measurable_fst)

end Meas

/-! ### The returned GFF and its characteristic functional -/

section Law

variable {c : BoundaryWord}

/-- **The return field of the word's GFF is the GFF of the returned word.** -/
theorem isGFFWithBoundaryData_returnField_retWord (hc : c.IsSorted) (a l : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y : Ω → DistOn upperHalfPlaneOpens} (hY : IsGFFWithBoundaryData P Y c.fn c.jumps) :
    IsGFFWithBoundaryData P (fun ω => returnField a l (Y ω)) (retWord a l c).fn (retWord a l c).jumps := by
  have h := isGFFWithBoundaryData_returnField a l ⟨c.mean, c.isBoundedHarmonicExtension_mean hc⟩ hY
  rw [jumps_retWord hc a l]
  refine (isGFFWithBoundaryData_congr P _ fun y hy => ?_).2 h
  refine fn_retWord hc a l ?_
  rw [jumps_retWord hc a l]
  exact_mod_cast hy

/-- **The characteristic functional of the returned GFF** is the Gaussian one of the returned word. -/
theorem integral_cexp_returnField_gffLaw (hc : c.IsSorted) (a l : ℝ) (φ : TestOn upperHalfPlaneOpens) :
    ∫ g, Complex.exp (Complex.I * (returnField a l g φ : ℂ)) ∂c.gffLaw = gaussCF (retWord a l c) φ :=
  Exist.StagedLaw.integral_cexp_eq_gaussCF (Y := fun g => returnField a l (id g)) (isSorted_retWord hc a l)
    (isGFFWithBoundaryData_returnField_retWord hc a l (c.isGFFWithBoundaryData_gffLaw hc)) φ

/-- **The Gaussian characteristic value of the returned word** in terms of that of the word:
`gaussCF (retWord a l c) φ = exp(i (a ∫ φ + l ∫ ℓ φ)) · gaussCF c (−φ̃)`, `φ̃` the return-chart transport of `φ`. -/
theorem gaussCF_retWord (hc : c.IsSorted) (a l : ℝ) (φ : TestOn upperHalfPlaneOpens) :
    gaussCF (retWord a l c) φ =
      Complex.exp (Complex.I * ((a * (∫ w, φ w) + l * ∫ w, infinitySourceChart.2.2 w * φ w : ℝ) : ℂ)) *
        gaussCF c (-(Chart.pushTest isConformal_infinityReturnChart φ)) := by
  rw [← integral_cexp_returnField_gffLaw hc a l, gaussCF_eq_integral, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only [returnField_apply, map_neg]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end Law

end GW2JointKernel

end Theorem14

end InteractingSLE
