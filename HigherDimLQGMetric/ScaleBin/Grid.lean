import HigherDimLQGMetric.ScaleBin.Point

/-!
# Finite lattice boxes at a given scale

A centre in `B(0,5R)` at spacing `r/(100d)` has integer coordinates bounded
by `500dR/r`. This module packages the finite box and its cardinality.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric.ScaleBin

open HigherDimLFPP (Rd)
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

private def gridIndexBox (d N : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ : Fin d => Finset.Icc (-(N : ℤ)) N

private def gridPoint (d : ℕ) (r : ℝ) (m : Fin d → ℤ) : Rd d :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => r / (100 * d) * m i)

private theorem gridIndexBox_card (d N : ℕ) :
    (gridIndexBox d N).card = (2 * N + 1) ^ d := by
  classical
  have hI : (Finset.Icc (-(N : ℤ)) N).card = 2 * N + 1 := by
    rw [Int.card_Icc]
    omega
  simp only [gridIndexBox, Fintype.card_piFinset_const, hI]

private theorem gridIndexBox_contains {d : ℕ} (hd : 1 ≤ d)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (z : Rd d) (hz : ‖z‖ < 5 * R)
    (m : Fin d → ℤ)
    (hm : EuclideanSpace.equiv (Fin d) ℝ z = fun i => r / (100 * d) * m i) :
    m ∈ gridIndexBox d ⌈500 * d * R / r⌉₊ := by
  classical
  rw [gridIndexBox, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hc : 0 < r / (100 * (d : ℝ)) := by positivity
  have hcoord : |(EuclideanSpace.equiv (Fin d) ℝ z) i| ≤ ‖z‖ := by
    change |z.ofLp i| ≤ ‖z‖
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le z i)
  rw [hm] at hcoord
  have hmul : r / (100 * (d : ℝ)) * |(m i : ℝ)| < 5 * R := by
    rw [abs_mul, abs_of_pos hc] at hcoord
    exact hcoord.trans_lt hz
  have hfactor : r / (100 * (d : ℝ)) * (500 * d * R / r) = 5 * R := by
    field_simp
    ring
  have hmi : |(m i : ℝ)| ≤ 500 * d * R / r := by
    by_contra h
    have hlt : 500 * d * R / r < |(m i : ℝ)| := lt_of_not_ge h
    have := mul_lt_mul_of_pos_left hlt hc
    linarith
  have hceil : 500 * d * R / r ≤ (⌈500 * d * R / r⌉₊ : ℝ) := Nat.le_ceil _
  have hbound : |(m i : ℝ)| ≤ (⌈500 * d * R / r⌉₊ : ℝ) := hmi.trans hceil
  constructor
  · exact_mod_cast (abs_le.mp hbound).1
  · exact_mod_cast (abs_le.mp hbound).2

private theorem gridPoint_eq {d : ℕ} {r : ℝ} (z : Rd d) (m : Fin d → ℤ)
    (hm : EuclideanSpace.equiv (Fin d) ℝ z = fun i => r / (100 * d) * m i) :
    z = gridPoint d r m := by
  apply (EuclideanSpace.equiv (Fin d) ℝ).injective
  simpa only [gridPoint, ContinuousLinearEquiv.apply_symm_apply] using hm

/-- The Gaussian point tail wins four powers of `r/R` after paying for the grid. -/
theorem grid_count_factor_le {d : ℕ} (hd : 2 ≤ d) {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    2 * (2 * (⌈500 * d * R / r⌉₊ : ℝ) + 1) ^ d *
        (r / R) ^ (2 * (d + 2)) ≤
      2 * (1004 * (d : ℝ)) ^ d * (r / R) ^ 4 := by
  have hR : 0 < R := hr.trans_le hrR
  let t : ℝ := r / R
  let A : ℝ := 2 * (⌈500 * d * R / r⌉₊ : ℝ) + 1
  let C : ℝ := 1004 * d
  have ht0 : 0 ≤ t := (div_pos hr hR).le
  have ht1 : t ≤ 1 := (div_le_one hR).2 hrR
  have hratio : 1 ≤ R / r := (one_le_div hr).2 hrR
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd.trans' (by omega : 1 ≤ 2)
  have hX : 0 ≤ 500 * (d : ℝ) * R / r := by positivity
  have hceil := Nat.ceil_lt_add_one hX
  have hproduct : (R / r) * t = 1 := by
    dsimp [t]
    field_simp
  have hAt : A * t ≤ C := by
    have hkey : (A - C * (R / r)) < 0 := by
      dsimp [A, C]
      have hx : 500 * (d : ℝ) * R / r = 500 * ((d : ℝ) * (R / r)) := by ring
      rw [hx] at hceil
      rw [hx]
      have hy : 1 ≤ (d : ℝ) * (R / r) := by nlinarith [hratio]
      nlinarith only [hceil, hy]
    have hA : A ≤ C * (R / r) := le_of_lt (sub_neg.mp hkey)
    calc
      A * t ≤ (C * (R / r)) * t := mul_le_mul_of_nonneg_right hA ht0
      _ = C := by rw [mul_assoc, hproduct, mul_one]
  have hpow : A ^ d * t ^ d ≤ C ^ d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity : 0 ≤ A * t) hAt d
  have htd : t ^ d ≤ 1 := pow_le_one₀ ht0 ht1
  have hdecomp : t ^ (2 * (d + 2)) = t ^ d * t ^ d * t ^ 4 := by
    rw [show 2 * (d + 2) = d + d + 4 by omega, pow_add, pow_add]
  change 2 * A ^ d * t ^ (2 * (d + 2)) ≤ 2 * C ^ d * t ^ 4
  rw [hdecomp]
  calc
    2 * A ^ d * (t ^ d * t ^ d * t ^ 4) =
        2 * (A ^ d * t ^ d) * (t ^ d * t ^ 4) := by ring
    _ ≤ 2 * C ^ d * (t ^ d * t ^ 4) := by gcongr
    _ ≤ 2 * C ^ d * (1 * t ^ 4) := by gcongr
    _ = 2 * C ^ d * t ^ 4 := by ring

/-- The bad event at one radius is a finite union, with no measurability assumption on
the event itself. -/
theorem scale_point_bad_le {d : ℕ} (hd : 2 ≤ d) {D : ℝ}
    (hvar : ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d},
      IsWholeSpaceLGF h P → ∀ {r R : ℝ}, 0 < r → r ≤ R →
      ∀ z : Rd d, ‖z‖ < 5 * R →
        Var[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) (8 * R) 0; P] ≤
          D * (1 + Real.log (R / r)))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    P {ω | ∃ z : Rd d, ‖z‖ < 5 * R ∧
      (∃ m : Fin d → ℤ, EuclideanSpace.equiv (Fin d) ℝ z =
        fun i => r / (100 * d) * m i) ∧
      (D + (d : ℝ) + 2) * (1 + Real.log (R / r)) ≤
        |sphereAvg (h ω) r z - sphereAvg (h ω) (8 * R) 0|} ≤
      ENNReal.ofReal (2 * (2 * (⌈500 * d * R / r⌉₊ : ℝ) + 1) ^ d *
        (r / R) ^ (2 * (d + 2))) := by
  classical
  let N : ℕ := ⌈500 * d * R / r⌉₊
  let box : Finset (Fin d → ℤ) := gridIndexBox d N
  let bad : (Fin d → ℤ) → Set Ω := fun m =>
    {ω | ‖gridPoint d r m‖ < 5 * R ∧
      (D + (d : ℝ) + 2) * (1 + Real.log (R / r)) ≤
        |sphereAvg (h ω) r (gridPoint d r m) - sphereAvg (h ω) (8 * R) 0|}
  have hsub : {ω | ∃ z : Rd d, ‖z‖ < 5 * R ∧
      (∃ m : Fin d → ℤ, EuclideanSpace.equiv (Fin d) ℝ z =
        fun i => r / (100 * d) * m i) ∧
      (D + (d : ℝ) + 2) * (1 + Real.log (R / r)) ≤
        |sphereAvg (h ω) r z - sphereAvg (h ω) (8 * R) 0|} ⊆
      ⋃ m ∈ box, bad m := by
    intro ω hω
    obtain ⟨z, hz, ⟨m, hm⟩, htail⟩ := hω
    have hmBox : m ∈ box := gridIndexBox_contains (by omega : 1 ≤ d)
      hr (hr.trans_le hrR) z hz m hm
    have hzEq : z = gridPoint d r m := gridPoint_eq z m hm
    exact Set.mem_iUnion₂.mpr ⟨m, hmBox, by simpa only [bad, Set.mem_ofPred_eq, ← hzEq] using
      (show ‖z‖ < 5 * R ∧ _ from ⟨hz, htail⟩)⟩
  have hpoint : ∀ m ∈ box, P (bad m) ≤
      ENNReal.ofReal (2 * (r / R) ^ (2 * (d + 2))) := by
    intro m hm
    by_cases hz : ‖gridPoint d r m‖ < 5 * R
    · have hsubset : bad m ⊆ {ω | (D + (d : ℝ) + 2) * (1 + Real.log (R / r)) ≤
          |sphereAvg (h ω) r (gridPoint d r m) - sphereAvg (h ω) (8 * R) 0|} :=
        fun _ hω => hω.2
      have htail := point_tail_le hd hvar hh hr hrR (gridPoint d r m) hz
      calc
        P (bad m) ≤ P {ω | (D + (d : ℝ) + 2) * (1 + Real.log (R / r)) ≤
            |sphereAvg (h ω) r (gridPoint d r m) - sphereAvg (h ω) (8 * R) 0|} :=
          measure_mono hsubset
        _ = ENNReal.ofReal (P.real {ω | (D + (d : ℝ) + 2) * (1 + Real.log (R / r)) ≤
            |sphereAvg (h ω) r (gridPoint d r m) - sphereAvg (h ω) (8 * R) 0|}) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
        _ ≤ ENNReal.ofReal (2 * (r / R) ^ (2 * (d + 2))) :=
          ENNReal.ofReal_le_ofReal htail
    · have hempty : bad m = ∅ := by
        ext ω
        simp only [bad, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hω => hz hω.1
      rw [hempty, measure_empty]
      exact bot_le
  calc
    P {ω | ∃ z : Rd d, ‖z‖ < 5 * R ∧
      (∃ m : Fin d → ℤ, EuclideanSpace.equiv (Fin d) ℝ z =
        fun i => r / (100 * d) * m i) ∧
      (D + (d : ℝ) + 2) * (1 + Real.log (R / r)) ≤
        |sphereAvg (h ω) r z - sphereAvg (h ω) (8 * R) 0|}
        ≤ P (⋃ m ∈ box, bad m) := measure_mono hsub
    _ ≤ ∑ m ∈ box, P (bad m) := measure_biUnion_finset_le box bad
    _ ≤ box.card • ENNReal.ofReal (2 * (r / R) ^ (2 * (d + 2))) :=
      Finset.sum_le_card_nsmul box _ _ hpoint
    _ = ENNReal.ofReal (2 * (2 * (N : ℝ) + 1) ^ d *
          (r / R) ^ (2 * (d + 2))) := by
      rw [← ENNReal.ofReal_nsmul, gridIndexBox_card]
      congr 1
      ring

end HigherDimLQGMetric.ScaleBin
