import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Dyadic squares, box counting and an upper bound for the Hausdorff dimension

Deterministic part of the proof of Aux. lemma 14 of the specification (`source/spec/p049-096.md`,
lines 850–854, p. 88): `N_δ` is the number of dyadic squares of side `δ = 2^{-n}` meeting a set,
and `N_δ ≤ δ^{-d}` for all small dyadic `δ` bounds the Hausdorff dimension by `d`.

* `dyadicSquare n k` is the closed square `[k₁, k₁+1] × [k₂, k₂+1] · 2^{-n}`, `dyadicCenter n k` its
  center, `dyadicHits n A` the set of indices of squares meeting `A` and `dyadicCount n A` its
  cardinality (`N_{2^{-n}}`).
* `dist_dyadicCenter_le`: a point of a square is within `2^{-n}` of its center.
* `dyadicHits_subset_box`, `dyadicHits_finite`: for a bounded set only finitely many squares, at most
  `(2M+2)²` with `M = ⌈R 2^n⌉`, meet it.
* `dimH_le_of_eventually_dyadicCount_le`: if eventually `N_{2^{-n}}(A) ≤ (2^n)^d`, then
  `dim_H A ≤ d` (covering by the hit squares, `hausdorffMeasure_le_liminf_tsum`).
-/

noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Dimension

/-- The closed dyadic square of side `2^{-n}` with lower-left corner `(k₁ + i k₂) 2^{-n}`. -/
def dyadicSquare (n : ℕ) (k : ℤ × ℤ) : Set ℂ :=
  {x | (k.1 : ℝ) / 2 ^ n ≤ x.re ∧ x.re ≤ ((k.1 : ℝ) + 1) / 2 ^ n ∧
    (k.2 : ℝ) / 2 ^ n ≤ x.im ∧ x.im ≤ ((k.2 : ℝ) + 1) / 2 ^ n}

/-- The center of `dyadicSquare n k`. -/
def dyadicCenter (n : ℕ) (k : ℤ × ℤ) : ℂ :=
  ⟨((k.1 : ℝ) + 1 / 2) / 2 ^ n, ((k.2 : ℝ) + 1 / 2) / 2 ^ n⟩

/-- The indices of the dyadic squares of side `2^{-n}` meeting `A`. -/
def dyadicHits (n : ℕ) (A : Set ℂ) : Set (ℤ × ℤ) := {k | (dyadicSquare n k ∩ A).Nonempty}

/-- `N_{2^{-n}}(A)`: the number of dyadic squares of side `2^{-n}` meeting `A` (`0` if infinitely
many do; see `dyadicHits_finite`). -/
def dyadicCount (n : ℕ) (A : Set ℂ) : ℕ := (dyadicHits n A).ncard

theorem dyadicHits_mono {n : ℕ} {A A' : Set ℂ} (h : A ⊆ A') : dyadicHits n A ⊆ dyadicHits n A' :=
  fun _ hk => hk.mono (inter_subset_inter_right _ h)

theorem two_pow_pos (n : ℕ) : (0 : ℝ) < 2 ^ n := pow_pos two_pos n

/-- Every point lies in the dyadic square indexed by the floors of its scaled coordinates. -/
theorem mem_dyadicSquare_floor (n : ℕ) (x : ℂ) :
    x ∈ dyadicSquare n (⌊x.re * 2 ^ n⌋, ⌊x.im * 2 ^ n⌋) := by
  have h2 := two_pow_pos n
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ h2]; exact Int.floor_le _
  · rw [le_div_iff₀ h2]; exact (Int.lt_floor_add_one _).le
  · rw [div_le_iff₀ h2]; exact Int.floor_le _
  · rw [le_div_iff₀ h2]; exact (Int.lt_floor_add_one _).le

/-- A point of a dyadic square is within `2^{-n}` of its center. -/
theorem dist_dyadicCenter_le {n : ℕ} {k : ℤ × ℤ} {x : ℂ} (hx : x ∈ dyadicSquare n k) :
    dist x (dyadicCenter n k) ≤ 1 / 2 ^ n := by
  have h2 := two_pow_pos n
  obtain ⟨h1, h1', h3, h3'⟩ := hx
  have hre : |x.re - (dyadicCenter n k).re| ≤ 1 / 2 / 2 ^ n := by
    simp only [dyadicCenter]
    rw [abs_le]
    constructor
    · have : ((k.1 : ℝ) + 1 / 2) / 2 ^ n - (k.1 : ℝ) / 2 ^ n = 1 / 2 / 2 ^ n := by ring
      linarith
    · have : ((k.1 : ℝ) + 1) / 2 ^ n - ((k.1 : ℝ) + 1 / 2) / 2 ^ n = 1 / 2 / 2 ^ n := by ring
      linarith
  have him : |x.im - (dyadicCenter n k).im| ≤ 1 / 2 / 2 ^ n := by
    simp only [dyadicCenter]
    rw [abs_le]
    constructor
    · have : ((k.2 : ℝ) + 1 / 2) / 2 ^ n - (k.2 : ℝ) / 2 ^ n = 1 / 2 / 2 ^ n := by ring
      linarith
    · have : ((k.2 : ℝ) + 1) / 2 ^ n - ((k.2 : ℝ) + 1 / 2) / 2 ^ n = 1 / 2 / 2 ^ n := by ring
      linarith
  rw [dist_eq_norm]
  calc ‖x - dyadicCenter n k‖ ≤ |(x - dyadicCenter n k).re| + |(x - dyadicCenter n k).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |x.re - (dyadicCenter n k).re| + |x.im - (dyadicCenter n k).im| := by
        rw [Complex.sub_re, Complex.sub_im]
    _ ≤ 1 / 2 / 2 ^ n + 1 / 2 / 2 ^ n := add_le_add hre him
    _ = 1 / 2 ^ n := by ring

/-- Two points of a dyadic square of side `2^{-n}` are within `2 · 2^{-n}`. -/
theorem dist_le_of_mem_dyadicSquare {n : ℕ} {k : ℤ × ℤ} {x y : ℂ} (hx : x ∈ dyadicSquare n k)
    (hy : y ∈ dyadicSquare n k) : dist x y ≤ 2 / 2 ^ n := by
  calc dist x y ≤ dist x (dyadicCenter n k) + dist y (dyadicCenter n k) := dist_triangle_right _ _ _
    _ ≤ 1 / 2 ^ n + 1 / 2 ^ n := add_le_add (dist_dyadicCenter_le hx) (dist_dyadicCenter_le hy)
    _ = 2 / 2 ^ n := by ring

theorem ediam_dyadicSquare_le (n : ℕ) (k : ℤ × ℤ) :
    ediam (dyadicSquare n k) ≤ ENNReal.ofReal (2 / 2 ^ n) :=
  ediam_le_of_forall_dist_le fun _ hx _ hy => dist_le_of_mem_dyadicSquare hx hy

/-- The finite box of indices that contains every square meeting `closedBall 0 R`. -/
def dyadicBox (n : ℕ) (R : ℝ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(⌈R * 2 ^ n⌉ : ℤ) - 1) ⌈R * 2 ^ n⌉ ×ˢ Finset.Icc (-(⌈R * 2 ^ n⌉ : ℤ) - 1) ⌈R * 2 ^ n⌉

theorem mem_Icc_of_mem_square_aux {n : ℕ} {R a x : ℝ} (hxR : |x| ≤ R)
    (h1 : a / 2 ^ n ≤ x) (h2 : x ≤ (a + 1) / 2 ^ n) :
    -(⌈R * 2 ^ n⌉ : ℝ) - 1 ≤ a ∧ a ≤ ⌈R * 2 ^ n⌉ := by
  have h2n := two_pow_pos n
  rw [div_le_iff₀ h2n] at h1
  rw [le_div_iff₀ h2n] at h2
  have hc := Int.le_ceil (R * 2 ^ n)
  have hxR' := abs_le.1 hxR
  constructor
  · have : -(R * 2 ^ n) ≤ x * 2 ^ n := by nlinarith
    linarith
  · have : x * 2 ^ n ≤ R * 2 ^ n := by nlinarith
    linarith

/-- The squares meeting a set inside `closedBall 0 R` have indices in `dyadicBox n R`. -/
theorem dyadicHits_subset_box {n : ℕ} {A : Set ℂ} {R : ℝ} (hA : A ⊆ closedBall 0 R) :
    dyadicHits n A ⊆ dyadicBox n R := by
  rintro ⟨k₁, k₂⟩ ⟨x, hxS, hxA⟩
  have hxR : ‖x‖ ≤ R := by simpa using hA hxA
  have hre : |x.re| ≤ R := (Complex.abs_re_le_norm x).trans hxR
  have him : |x.im| ≤ R := (Complex.abs_im_le_norm x).trans hxR
  obtain ⟨h1, h2, h3, h4⟩ := hxS
  obtain ⟨a1, a2⟩ := mem_Icc_of_mem_square_aux hre h1 h2
  obtain ⟨b1, b2⟩ := mem_Icc_of_mem_square_aux him h3 h4
  dsimp only at a1 a2 b1 b2
  rw [Finset.mem_coe, dyadicBox, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  exact ⟨⟨by exact_mod_cast a1, by exact_mod_cast a2⟩, ⟨by exact_mod_cast b1, by exact_mod_cast b2⟩⟩

theorem card_dyadicBox {R : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    ((dyadicBox n R).card : ℝ) = (2 * (⌈R * 2 ^ n⌉ : ℝ) + 2) ^ 2 := by
  have hM : (0 : ℤ) ≤ ⌈R * 2 ^ n⌉ := Int.ceil_nonneg (mul_nonneg hR (two_pow_pos n).le)
  rw [dyadicBox, Finset.card_product, Int.card_Icc]
  have h : (⌈R * 2 ^ n⌉ + 1 - (-⌈R * 2 ^ n⌉ - 1)) = 2 * ⌈R * 2 ^ n⌉ + 2 := by ring
  rw [h]
  have h2 : (0 : ℤ) ≤ 2 * ⌈R * 2 ^ n⌉ + 2 := by omega
  push_cast
  rw [← sq]
  congr 1
  have := Int.toNat_of_nonneg h2
  exact_mod_cast this

/-- The number of squares meeting `closedBall 0 R` is `O(4^n)`. -/
theorem card_dyadicBox_le {R : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    ((dyadicBox n R).card : ℝ) ≤ (2 * R + 4) ^ 2 * 4 ^ n := by
  rw [card_dyadicBox hR]
  have h2 := two_pow_pos n
  have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hc : (⌈R * 2 ^ n⌉ : ℝ) ≤ R * 2 ^ n + 1 := (Int.ceil_lt_add_one _).le
  have hc0 : (0 : ℝ) ≤ ⌈R * 2 ^ n⌉ := by
    exact_mod_cast Int.ceil_nonneg (mul_nonneg hR h2.le)
  have h4 : (4 : ℝ) ^ n = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  nlinarith

/-- A bounded set meets only finitely many dyadic squares. -/
theorem dyadicHits_finite {n : ℕ} {A : Set ℂ} (hA : Bornology.IsBounded A) :
    (dyadicHits n A).Finite := by
  obtain ⟨R, hR⟩ := hA.subset_closedBall 0
  exact (dyadicBox n R).finite_toSet.subset (dyadicHits_subset_box hR)

/-- Every set is covered by the squares meeting it. -/
theorem subset_iUnion_dyadicHits (n : ℕ) (A : Set ℂ) :
    A ⊆ ⋃ k : ℤ × ℤ, ⋃ (_ : k ∈ dyadicHits n A), dyadicSquare n k := by
  intro x hx
  refine mem_iUnion₂.2 ⟨(⌊x.re * 2 ^ n⌋, ⌊x.im * 2 ^ n⌋), ⟨x, mem_dyadicSquare_floor n x, hx⟩, ?_⟩
  exact mem_dyadicSquare_floor n x

/-- `(2^n)^d (2 / 2^n)^{d'} = 2^{d'} (2^d / 2^{d'})^n`. -/
theorem two_pow_rpow_mul_rpow_eq (n : ℕ) (d d' : ℝ) :
    ((2 : ℝ) ^ n) ^ d * (2 / 2 ^ n) ^ d' = 2 ^ d' * ((2 : ℝ) ^ d / 2 ^ d') ^ n := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have e1 : ((2 : ℝ) ^ n) ^ d = ((2 : ℝ) ^ d) ^ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h2, mul_comm, Real.rpow_mul_natCast h2]
  have e2 : ((2 : ℝ) ^ n) ^ d' = ((2 : ℝ) ^ d') ^ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h2, mul_comm, Real.rpow_mul_natCast h2]
  rw [Real.div_rpow h2 (two_pow_pos n).le, e1, e2, div_pow]
  have : (0 : ℝ) < ((2 : ℝ) ^ d') ^ n := pow_pos (Real.rpow_pos_of_pos two_pos _) n
  field_simp

theorem tendsto_two_pow_rpow_mul_rpow {d d' : ℝ} (h : d < d') :
    Tendsto (fun n : ℕ => ((2 : ℝ) ^ n) ^ d * (2 / 2 ^ n) ^ d') atTop (𝓝 0) := by
  simp_rw [two_pow_rpow_mul_rpow_eq]
  have hq0 : (0 : ℝ) ≤ (2 : ℝ) ^ d / 2 ^ d' := by positivity
  have hq1 : (2 : ℝ) ^ d / 2 ^ d' < 1 := by
    rw [div_lt_one (Real.rpow_pos_of_pos two_pos _)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul ((2 : ℝ) ^ d')

/-- **Box counting bounds the Hausdorff dimension.** If eventually only finitely many dyadic squares
of side `2^{-n}` meet `A` and `N_{2^{-n}}(A) ≤ (2^n)^d`, then `dim_H A ≤ d`. -/
theorem dimH_le_of_eventually_dyadicCount_le {A : Set ℂ} {d : ℝ} (hd : 0 ≤ d)
    (h : ∀ᶠ n in atTop, (dyadicHits n A).Finite ∧ (dyadicCount n A : ℝ) ≤ ((2 : ℝ) ^ n) ^ d) :
    dimH A ≤ ENNReal.ofReal d := by
  refine dimH_le fun d' hd' => ?_
  by_contra hlt
  rw [not_le] at hlt
  have hdd' : d < (d' : ℝ) := by
    have := (ENNReal.ofReal_lt_iff_lt_toReal hd ENNReal.coe_ne_top).1 hlt
    simpa using this
  have hd'0 : 0 < (d' : ℝ) := hd.trans_lt hdd'
  set t : ℕ → ℤ × ℤ → Set ℂ := fun n k => ⋃ (_ : k ∈ dyadicHits n A), dyadicSquare n k with ht
  have htend : Tendsto (fun n : ℕ => ENNReal.ofReal (2 / 2 ^ n)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have : (fun n : ℕ => (2 : ℝ) / 2 ^ n) = fun n => 2 * (1 / 2) ^ n := by
      funext n; rw [one_div_pow]; ring
    rw [this]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (2 : ℝ)
  have hdiam : ∀ n k, ediam (t n k) ≤ ENNReal.ofReal (2 / 2 ^ n) := fun n k =>
    (ediam_mono (iUnion_subset fun _ => subset_rfl)).trans (ediam_dyadicSquare_le n k)
  have hμ := Measure.hausdorffMeasure_le_liminf_tsum (d' : ℝ) A
    (fun n : ℕ => ENNReal.ofReal (2 / 2 ^ n)) htend t (Eventually.of_forall fun n k => hdiam n k)
    (Eventually.of_forall fun n => subset_iUnion_dyadicHits n A)
  have hsum : ∀ᶠ n in atTop, ∑' k, ediam (t n k) ^ (d' : ℝ)
      ≤ ENNReal.ofReal (((2 : ℝ) ^ n) ^ d * (2 / 2 ^ n) ^ (d' : ℝ)) := by
    filter_upwards [h] with n ⟨hfin, hcount⟩
    have hzero : ∀ k ∉ hfin.toFinset, ediam (t n k) ^ (d' : ℝ) = 0 := by
      intro k hk
      have hk' : k ∉ dyadicHits n A := by simpa using hk
      have : t n k = ∅ := by simp only [ht, hk', iUnion_false]
      rw [this, ediam_empty, ENNReal.zero_rpow_of_pos hd'0]
    rw [tsum_eq_sum hzero]
    have hle : ∀ k ∈ hfin.toFinset, ediam (t n k) ^ (d' : ℝ)
        ≤ ENNReal.ofReal (2 / 2 ^ n) ^ (d' : ℝ) := fun k _ =>
      ENNReal.rpow_le_rpow (hdiam n k) hd'0.le
    refine (Finset.sum_le_card_nsmul _ _ _ hle).trans ?_
    rw [nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin,
      ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg (by positivity) hd'0.le]
    gcongr
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hcount
  have hT : Tendsto (fun n : ℕ => ENNReal.ofReal (((2 : ℝ) ^ n) ^ d * (2 / 2 ^ n) ^ (d' : ℝ)))
      atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (tendsto_two_pow_rpow_mul_rpow hdd')
  have hlim0 : liminf (fun n => ∑' k, ediam (t n k) ^ (d' : ℝ)) atTop = 0 := by
    refine le_antisymm ?_ zero_le
    calc liminf (fun n => ∑' k, ediam (t n k) ^ (d' : ℝ)) atTop
        ≤ liminf (fun n : ℕ => ENNReal.ofReal (((2 : ℝ) ^ n) ^ d * (2 / 2 ^ n) ^ (d' : ℝ)))
          atTop := liminf_le_liminf hsum
      _ = 0 := hT.liminf_eq
  rw [hlim0, nonpos_iff_eq_zero] at hμ
  rw [hμ] at hd'
  exact ENNReal.zero_ne_top hd'

end InteractingSLE.Dimension
