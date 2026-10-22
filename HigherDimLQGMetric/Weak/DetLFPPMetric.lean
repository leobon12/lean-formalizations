import HigherDimLQGMetric.Weak.DetLFPP

/-!
# Continuous LFPP metrics on `ℝ^d`

Port of the local metric estimates in LQGMetric/LFPP/ContMetric.lean,
using HigherDimLFPP's real-valued LFPP distance.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {ξ : ℝ} {φ : Rd d → ℝ}

theorem fieldLfpp_eq_lfppDistOn (hφ : Continuous φ) (p : Rd d × Rd d) :
    fieldLfpp ξ φ p = HigherDimLFPP.lfppDistOn ξ φ univ p.1 p.2 := by
  rw [fieldLfpp, fieldLfppE_eq_ofReal_lfppDistOn hφ]
  exact ENNReal.toReal_ofReal (HigherDimLFPP.lfppDistOn_nonneg ξ φ univ p.1 p.2)

theorem exists_exp_le_on_closedBall (hφ : Continuous φ) (z : Rd d) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ closedBall z R, Real.exp (ξ * φ x) ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall z R).exists_bound_of_continuousOn
    (Real.continuous_exp.comp (continuous_const.mul hφ)).continuousOn
  exact ⟨max B 0, le_max_right _ _, fun x hx =>
    (Real.le_norm_self _).trans ((hB x hx).trans (le_max_left _ _))⟩

/-- LFPP is locally bounded above by Euclidean distance on a closed ball. -/
theorem lfppDistOn_le_mul_on_closedBall (hφ : Continuous φ) (z : Rd d) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ closedBall z R, ∀ y ∈ closedBall z R,
      HigherDimLFPP.lfppDistOn ξ φ univ x y ≤ B * ‖y - x‖ := by
  obtain ⟨B, hB0, hB⟩ := exists_exp_le_on_closedBall (ξ := ξ) hφ z R
  refine ⟨B, hB0, fun x hx y hy => ?_⟩
  exact HigherDimLFPP.lfppDistOn_le_of_segment hφ
    (HigherDimLFPP.mapsTo_segPath (convex_closedBall z R) hx hy |>.mono_right
      (subset_univ _))
    (fun t ht => hB _ (HigherDimLFPP.mapsTo_segPath (convex_closedBall z R) hx hy ht))

theorem fieldLfpp_triangle (hφ : Continuous φ) (x y z : Rd d) :
    fieldLfpp ξ φ (x, z) ≤ fieldLfpp ξ φ (x, y) + fieldLfpp ξ φ (y, z) := by
  simp only [fieldLfpp_eq_lfppDistOn hφ]
  exact HigherDimLFPP.lfppDistOn_triangle hφ
    (HigherDimLFPP.PcwJoined.of_convex convex_univ (mem_univ x) (mem_univ y))
    (HigherDimLFPP.PcwJoined.of_convex convex_univ (mem_univ y) (mem_univ z))

/-- The pairwise LFPP distance is continuous in both endpoints. -/
theorem continuous_fieldLfpp (hφ : Continuous φ) : Continuous (fieldLfpp ξ φ) := by
  rw [Metric.continuous_iff]
  rintro ⟨z₀, w₀⟩ ε hε
  set R : ℝ := ‖z₀‖ + ‖w₀‖ + 1
  obtain ⟨B, hB0, hB⟩ := lfppDistOn_le_mul_on_closedBall (ξ := ξ) hφ 0 R
  refine ⟨min 1 (ε / (2 * (B + 1))), lt_min one_pos (by positivity), ?_⟩
  rintro ⟨z, w⟩ hd
  have hd1 := hd.trans_le (min_le_left _ _)
  have hd2 := hd.trans_le (min_le_right _ _)
  rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hd1 hd2
  simp only at hd1 hd2
  have mem : ∀ x : Rd d, ‖x‖ ≤ R → x ∈ closedBall (0 : Rd d) R :=
    fun x hx => by rwa [mem_closedBall, dist_zero_right]
  have hz : ‖z‖ ≤ R := by
    dsimp [R]
    linarith [norm_le_norm_add_norm_sub' z z₀, norm_nonneg w₀]
  have hw : ‖w‖ ≤ R := by
    dsimp [R]
    linarith [norm_le_norm_add_norm_sub' w w₀, norm_nonneg z₀]
  have hz₀ : ‖z₀‖ ≤ R := by dsimp [R]; linarith [norm_nonneg w₀]
  have hw₀ : ‖w₀‖ ≤ R := by dsimp [R]; linarith [norm_nonneg z₀]
  have e1 := hB z (mem z hz) z₀ (mem z₀ hz₀)
  have e2 := hB z₀ (mem z₀ hz₀) z (mem z hz)
  have e3 := hB w (mem w hw) w₀ (mem w₀ hw₀)
  have e4 := hB w₀ (mem w₀ hw₀) w (mem w hw)
  rw [← fieldLfpp_eq_lfppDistOn hφ (z, z₀)] at e1
  rw [← fieldLfpp_eq_lfppDistOn hφ (z₀, z)] at e2
  rw [← fieldLfpp_eq_lfppDistOn hφ (w, w₀)] at e3
  rw [← fieldLfpp_eq_lfppDistOn hφ (w₀, w)] at e4
  have t1 := fieldLfpp_triangle (ξ := ξ) hφ z z₀ w
  have t2 := fieldLfpp_triangle (ξ := ξ) hφ z₀ w₀ w
  have t3 := fieldLfpp_triangle (ξ := ξ) hφ z₀ z w₀
  have t4 := fieldLfpp_triangle (ξ := ξ) hφ z w w₀
  rw [norm_sub_rev z₀ z] at e1
  rw [norm_sub_rev w₀ w] at e3
  have hBε : B * (2 * (ε / (2 * (B + 1)))) < ε := by
    rw [mul_div_assoc', mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hd2.1.le hB0,
    mul_le_mul_of_nonneg_left hd2.2.le hB0]

theorem toCMapRd_apply_of_continuous {f : Rd d × Rd d → ℝ} (hf : Continuous f)
    (p : Rd d × Rd d) : toCMapRd f p = f p := by
  simp only [toCMapRd, dite_eq_left hf, ContinuousMap.coe_mk]

theorem fieldLfppE_eq_ofReal_fieldLfpp (hφ : Continuous φ) (z w : Rd d) :
    fieldLfppE ξ φ z w = ENNReal.ofReal (fieldLfpp ξ φ (z, w)) := by
  rw [fieldLfppE_eq_ofReal_lfppDistOn hφ,
    fieldLfpp_eq_lfppDistOn hφ (z, w)]

theorem exists_exponent_lower_on_closedBall (hφ : Continuous φ) (z : Rd d) (r : ℝ)
    (hr : 0 ≤ r) :
    ∃ a : ℝ, ∀ x ∈ closedBall z r, a ≤ ξ * φ x := by
  obtain ⟨x₀, -, hx₀⟩ := (isCompact_closedBall z r).exists_isMinOn
    ⟨z, mem_closedBall_self hr⟩ (continuous_const.mul hφ).continuousOn
  exact ⟨ξ * φ x₀, fun x hx => hx₀ hx⟩

theorem fieldLfpp_euclidean_of_small (hφ : Continuous φ) (z : Rd d) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ w, fieldLfpp ξ φ (z, w) < δ → ‖z - w‖ < ε := by
  obtain ⟨a, ha⟩ := exists_exponent_lower_on_closedBall (ξ := ξ) hφ z ε hε.le
  refine ⟨Real.exp a * ε, by positivity, fun w hw => ?_⟩
  set r := min ε ‖w - z‖
  have hr0 : 0 ≤ r := le_min hε.le (norm_nonneg _)
  have hrw : r ≤ ‖w - z‖ := min_le_right _ _
  have hrε : r ≤ ε := min_le_left _ _
  have hlow := HigherDimLFPP.exp_mul_le_lfppDistOn (ζ := ξ) (φ := φ) (V := univ)
    (x := z) (y := w) hφ
    (HigherDimLFPP.PcwJoined.of_convex convex_univ (mem_univ z) (mem_univ w))
    hrw (fun x hx => ha x (closedBall_subset_closedBall hrε hx))
  rw [← fieldLfpp_eq_lfppDistOn hφ (z, w)] at hlow
  have hr : r < ε := by
    have := lt_of_le_of_lt hlow hw
    exact (lt_of_mul_lt_mul_left this (Real.exp_nonneg _))
  rw [norm_sub_rev]
  rcases min_lt_iff.1 hr with h | h
  · exact absurd h (lt_irrefl _)
  · exact h

/-- LFPP of a continuous field is a continuous metric inducing Euclidean topology. -/
theorem isContinuousMetric_fieldLfpp (hφ : Continuous φ) :
    IsContinuousMetric (⟨fieldLfpp ξ φ, continuous_fieldLfpp hφ⟩ :
      C(Rd d × Rd d, ℝ)) := by
  refine ⟨{
    self_eq_zero := fun x => ?_
    eq_of_eq_zero := fun x y h => ?_
    symm := fun x y => ?_
    triangle := fieldLfpp_triangle hφ
  }, fieldLfpp_euclidean_of_small hφ⟩
  · change fieldLfpp ξ φ (x, x) = 0
    rw [fieldLfpp_eq_lfppDistOn hφ]
    exact HigherDimLFPP.lfppDistOn_self ξ φ univ x
  · by_contra hxy
    obtain ⟨a, ha⟩ := exists_exponent_lower_on_closedBall (ξ := ξ) hφ x 1 zero_le_one
    have hr : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hxy))
    have hlow := HigherDimLFPP.exp_mul_le_lfppDistOn (ζ := ξ) (φ := φ) (V := univ)
      (x := x) (y := y) hφ
      (HigherDimLFPP.PcwJoined.of_convex convex_univ (mem_univ x) (mem_univ y))
      (min_le_right (1 : ℝ) ‖y - x‖)
      (fun z hz => ha z (closedBall_subset_closedBall (min_le_left _ _) hz))
    rw [← fieldLfpp_eq_lfppDistOn hφ (x, y)] at hlow
    exact (not_le_of_gt (mul_pos (Real.exp_pos _) (lt_min zero_lt_one hr)))
      (hlow.trans_eq h)
  · change fieldLfpp ξ φ (x, y) = fieldLfpp ξ φ (y, x)
    rw [fieldLfpp_eq_lfppDistOn hφ (x, y), fieldLfpp_eq_lfppDistOn hφ (y, x)]
    exact HigherDimLFPP.lfppDistOn_comm ξ φ univ x y

/-- The LFPP continuous metric associated with a continuous field. -/
def fieldLfppMetric (ξ : ℝ) (φ : C(Rd d, ℝ)) : ContMetric d :=
  ⟨⟨fieldLfpp ξ φ, continuous_fieldLfpp φ.continuous⟩,
    isContinuousMetric_fieldLfpp φ.continuous⟩

theorem fieldLfppMetric_apply (ξ : ℝ) (φ : C(Rd d, ℝ)) (p : Rd d × Rd d) :
    (fieldLfppMetric ξ φ).1 p = fieldLfpp ξ φ p := rfl

theorem fieldLfppMetric_edist (ξ : ℝ) (φ : C(Rd d, ℝ)) (z w : Rd d) :
    edist ((fieldLfppMetric ξ φ).pt z) ((fieldLfppMetric ξ φ).pt w) =
      fieldLfppE ξ φ z w := by
  rw [ContMetric.edist_pt, fieldLfppMetric_apply,
    ← fieldLfppE_eq_ofReal_fieldLfpp φ.continuous]

/-- A subpath's LFPP distance is bounded by its integrated density. -/
theorem fieldLfppE_le_lintegral {P : ℝ → Rd d} {z w : Rd d}
    (hP : IsPiecewiseC1Path P z w) (hφ : Continuous φ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    fieldLfppE ξ φ (P s) (P t) ≤
      ∫⁻ τ in Ioc s t, ENNReal.ofReal (HigherDimLFPP.lfppIntegrand ξ φ P τ) := by
  have hsub := hP.subPath hs hst ht
  have hD : fieldLfppE ξ φ (P s) (P t) ≤
      ENNReal.ofReal (HigherDimLFPP.lfppLength ξ φ (HigherDimLFPP.subPath P s t)) := by
    rw [fieldLfppE_eq_ofReal_lfppDistOn hφ]
    exact ENNReal.ofReal_le_ofReal (HigherDimLFPP.lfppDistOn_le_lfppLength hsub
      (fun _ _ => mem_univ _))
  have hi : IntegrableOn (HigherDimLFPP.lfppIntegrand ξ φ P) (Ioc s t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).1
      (HigherDimLFPP.intervalIntegrable_of_sub
        (hP.intervalIntegrable_lfppIntegrand hφ ξ) hs hst ht)
  have hn : 0 ≤ᵐ[volume.restrict (Ioc s t)] HigherDimLFPP.lfppIntegrand ξ φ P :=
    Filter.Eventually.of_forall (HigherDimLFPP.lfppIntegrand_nonneg ξ φ P)
  rw [HigherDimLFPP.lfppLength_subPath ξ φ P hst,
    intervalIntegral.integral_of_le hst] at hD
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn]
  exact hD

/-- The metric length of a piecewise C¹ path is at most its LFPP cost. -/
theorem fieldLfppMetric_len_le_lfppLen (φ : C(Rd d, ℝ))
    {P : ℝ → Rd d} {z w : Rd d} (hP : IsPiecewiseC1Path P z w)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    (fieldLfppMetric ξ φ).len P a b ≤
      ∫⁻ τ in Icc a b, ENNReal.ofReal (HigherDimLFPP.lfppIntegrand ξ φ P τ) := by
  change eVariationOn ((fieldLfppMetric ξ φ).pt ∘ P) (Icc a b) ≤ _
  refine LQGMetric.MetricGeometry.eVariationOn_le_lintegral fun s t hs hst ht => ?_
  change edist ((fieldLfppMetric ξ φ).pt (P s))
    ((fieldLfppMetric ξ φ).pt (P t)) ≤ _
  rw [fieldLfppMetric_edist]
  exact fieldLfppE_le_lintegral hP φ.continuous (ha.trans hs) hst (ht.trans hb)

/-- Whole-space LFPP of a continuous field is a length metric. -/
theorem fieldLfppMetric_isLength (ξ : ℝ) (φ : C(Rd d, ℝ)) :
    (fieldLfppMetric ξ φ).IsLength := by
  rw [ContMetric.isLength_iff_curves]
  intro z w ε hε
  have hfin : fieldLfppE ξ φ z w ≠ ∞ := by
    rw [fieldLfppE_eq_ofReal_lfppDistOn φ.continuous]
    exact ENNReal.ofReal_ne_top
  have hlt : fieldLfppE ξ φ z w < fieldLfppE ξ φ z w + ENNReal.ofReal ε :=
    ENNReal.lt_add_right hfin (by simpa using hε)
  unfold fieldLfppE at hlt
  obtain ⟨P, hPcost⟩ := iInf_lt_iff.1 hlt
  refine ⟨P.1, P.2.continuousOn, P.2.source, P.2.target, ?_⟩
  have hlen : (fieldLfppMetric ξ φ).len P.1 0 1 ≤ lfppLen ξ φ P.1 :=
    fieldLfppMetric_len_le_lfppLen (ξ := ξ) φ P.2 le_rfl le_rfl
  rw [fieldLfppMetric_apply, ← fieldLfppE_eq_ofReal_fieldLfpp φ.continuous]
  exact hlen.trans hPcost.le

end HigherDimLQGMetric
