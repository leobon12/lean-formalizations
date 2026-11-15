/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2TermEndpoint

/-! # The original flow line stops at a bad physical incident height -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

namespace InteractingSLE.Restart.FCPlumb
open PiecewiseConstantBoundaryData FlowStopIdentLL Sec2
universe u

/-- Every finite positive original lifetime ends on the real boundary at
a bad incident height on the corresponding side of the original seed.
This is simultaneous in the lifetime and allows original boundary jumps. -/
theorem ae_original_terminal_bad_incident {κ θ x : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {H : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hη : IsFlowLine κ b J x θ P H η ζ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
      (η ω T).im = 0 ∧
        (((η ω T).re ≤ x ∧ sleLambda κ ≤ leftLim b (η ω T).re + θ * chiC κ) ∨
          (x ≤ (η ω T).re ∧ rightLim b (η ω T).re + θ * chiC κ ≤ -sleLambda κ)) := by
  obtain ⟨H', 𝓕, W, VL, VR, B, -, hC, hgen⟩ := hη
  filter_upwards [hC.1.ae_isIntegratedSLEPath, hC.1.ae_tendsto_threshold hκ, hgen]
    with ω hp hlim hg T hT hζ
  obtain ⟨w₀, vL₀, vR₀, hlim, -⟩ := hlim T hT hζ
  let D : ℝ → ℝ := FiniteEndpoint.extDriver (W · ω) T w₀
  have hset : {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} = Iio T := by
    rw [← hζ]
    exact setOf_lt_coe_eq_Iio T
  have hc : ContinuousOn (W · ω) (Iio T) := hset ▸ hp.isForcePath.continuousOn_w
  have hD : Continuous D :=
    FiniteEndpoint.continuous_extDriver hc ((continuous_fst.tendsto _).comp hlim)
  have hD0 : D 0 = 0 := by
    dsimp only [D]
    rw [FiniteEndpoint.extDriver_of_lt le_rfl (NNReal.coe_pos.2 hT)]
    simpa only [Real.toNNReal_zero] using hp.isForcePath.w_zero
  have hDw : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ ω → D s = W s ω := by
    intro s hs
    dsimp only [D]
    rw [FiniteEndpoint.extDriver_of_lt s.coe_nonneg]
    · rw [Real.toNNReal_coe]
    · exact_mod_cast (hζ ▸ hs)
  have hgeom := tendsto_state_imageState (hp.isSLEPathUpTo le_rfl) hD hD0 hDw hζ
  have hthr := hp.isForcePath.threshold_of_tendsto hT hζ hgeom
  exact bad_incident_of_threshold_geometric_seed hκ hb hg hT hζ.le hD hD0
    (fun s hs => hDw s (hζ ▸ ENNReal.coe_lt_coe.2 hs)) hthr

end InteractingSLE.Restart.FCPlumb
