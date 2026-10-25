import SupercriticalLQGUniqueness.B2.PfeAxioms.ScaledAcrossUpperTail
import SupercriticalLQGUniqueness.B2.PfeAxioms.Section4AcrossFixed

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem scaled_across_upper_tail_of_section4
    (hS : DG20Section4)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (A : EuclideanAnnulus) :
    ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ (r c : Ioi (0 : ℝ)),
        Tendsto (fun n => (r : ℝ) *
          (m ⟨(ε n : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩ : ℝ) /
          (m (ε n) : ℝ)) atTop (𝓝 (c : ℝ)) →
        P {ω | ENNReal.ofReal (2 * M) <
          acrossDist (B2.LscTop.smulMetric
            ⟨(c : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
              Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c.property) (Real.exp_pos _))⟩
            (B2.LscTop.dilate r (D (h ω)))) A} ≤ ENNReal.ofReal η := by
  let R : ℝ := A.outerRadius + 1
  let V : TopologicalSpace.Opens ℂ :=
    ⟨Metric.ball A.center R, Metric.isOpen_ball⟩
  have hR : 0 < R := by
    dsimp [R]
    linarith [A.innerRadius_pos, A.innerRadius_lt_outerRadius]
  have hVcompact : IsCompact (closure (V : Set ℂ)) :=
    (isCompact_closedBall A.center R).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall
  let x : V := ⟨A.center + (A.innerRadius : ℂ), by
    change dist (A.center + (A.innerRadius : ℂ)) A.center < R
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos A.innerRadius_pos]
    dsimp [R]
    linarith [A.innerRadius_lt_outerRadius]⟩
  let y : V := ⟨A.center + (A.outerRadius : ℂ), by
    change dist (A.center + (A.outerRadius : ℂ)) A.center < R
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (A.innerRadius_pos.trans A.innerRadius_lt_outerRadius)]
    dsimp [R]
    linarith⟩
  have hx : (x : ℂ) ∈ A.innerBoundary := by
    change dist (A.center + (A.innerRadius : ℂ)) A.center = A.innerRadius
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos A.innerRadius_pos]
  have hy : (y : ℂ) ∈ A.outerBoundary := by
    change dist (A.center + (A.outerRadius : ℂ)) A.center = A.outerRadius
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (A.innerRadius_pos.trans A.innerRadius_lt_outerRadius)]
  exact scaled_across_upper_tail_of_section4_buffered
    hS ξ Q hQ m hm ε hε D hD P h hh X hX A V
    (Metric.isConnected_ball hR) hVcompact x y hx hy

end SupercriticalLQGUniqueness.B2.PfeAxioms
