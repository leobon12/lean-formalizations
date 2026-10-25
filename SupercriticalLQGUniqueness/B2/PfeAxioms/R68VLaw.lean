import SupercriticalLQGUniqueness.B2.PfeAxioms.R68VAroundLower
import SupercriticalLQGUniqueness.B2.PfeAxioms.NormalizedLaw

 





set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set LQGMetric LQGMetric.DFGPS
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 
def r68vScaledLimitMetric (ξ r c' : Ioi (0 : ℝ))
    (g : DistC) (D : LSCMetric) : LSCMetric :=
  B2.LscTop.smulMetric
    ⟨(c' : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg g r 0),
      Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c'.property) (Real.exp_pos _))⟩
    (B2.LscTop.dilate r D)

 
theorem measurable_r68vScaledLimitMetric
    (ξ r c' : Ioi (0 : ℝ)) (Φ : DistC → LSCMetric) (hΦ : Measurable Φ) :
    Measurable (fun g => r68vScaledLimitMetric ξ r c' g (Φ g)) := by
  have hC : Measurable (fun g : DistC =>
      (⟨(c' : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg g r 0),
        Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c'.property) (Real.exp_pos _))⟩ :
        Ioi (0 : ℝ))) := by
    apply Measurable.subtype_mk
    exact measurable_const.mul (Real.measurable_exp.comp
      ((LQGMetric.measurable_circleAvg_left r 0).const_mul (-(ξ : ℝ))))
  have hD : Measurable (fun g : DistC => B2.LscTop.dilate r (Φ g)) :=
    B2.LscTop.measurable_dilate.comp (measurable_const.prodMk hΦ)
  exact B2.LscTop.measurable_smulMetric.comp (hC.prodMk hD)

 

theorem r68v_measure_scaled_cost_lt_eq_of_coupling
    {ξ : Ioi (0 : ℝ)} {Q : ℝ} {m : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
    {e : ℕ → Ioi (0 : ℝ)} {c : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
    {V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {h' : Ω' → DistC} {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L)
    (Φ : DistC → LSCMetric) (hΦ : Measurable Φ)
    (hII : ∀ᵐ ω ∂P', L ω = Φ (h' ω))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (r c' : Ioi (0 : ℝ)) (cost : LSCMetric → ℝ≥0∞)
    (hcost : Measurable cost) (t : ℝ≥0∞) :
    P {ω | cost (r68vScaledLimitMetric ξ r c' (h ω) (Φ (h ω))) < t} =
      P' {ω | cost (r68vScaledLimitMetric ξ r c' (h' ω) (L ω)) < t} := by
  have hS : MeasurableSet {g : DistC |
      cost (r68vScaledLimitMetric ξ r c' g (Φ g)) < t} :=
    measurableSet_lt (hcost.comp (measurable_r68vScaledLimitMetric ξ r c' Φ hΦ))
      measurable_const
  have hLaw : P.map h = P'.map h' :=
    (normGFFLaw_eq_of_normalized P h hh).symm.trans
      (normGFFLaw_eq_of_normalized P' h' hB.limit_field)
  have h1 : P {ω | cost (r68vScaledLimitMetric ξ r c' (h ω) (Φ (h ω))) < t} =
      (P.map h) {g | cost (r68vScaledLimitMetric ξ r c' g (Φ g)) < t} := by
    rw [Measure.map_apply hh.1.measurable hS]
    rfl
  have h2 : P' {ω | cost (r68vScaledLimitMetric ξ r c' (h' ω) (Φ (h' ω))) < t} =
      (P'.map h') {g | cost (r68vScaledLimitMetric ξ r c' g (Φ g)) < t} := by
    rw [Measure.map_apply hB.limit_field.1.measurable hS]
    rfl
  have h3 : P' {ω | cost (r68vScaledLimitMetric ξ r c' (h' ω) (L ω)) < t} =
      P' {ω | cost (r68vScaledLimitMetric ξ r c' (h' ω) (Φ (h' ω))) < t} := by
    apply measure_congr
    filter_upwards [hII] with ω hω
    simp only [hω]
  rw [h1, h3, h2, hLaw]

end SupercriticalLQGUniqueness.B2.PfeAxioms
