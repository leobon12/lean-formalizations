/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2CapTerminal

/-!
# Endpoint access for the actual measurable boundary word

The deterministic criterion includes time zero, so the source endpoint input
does not acquire a separate positive-lifetime hypothesis.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Restart.FCPlumb
open PiecewiseConstantBoundaryData FlowStopIdentLL MartChar.RealFlow RetAux79

/-- The accessed-side criterion also holds at zero, without a seed
admissibility or positive-lifetime premise. -/
theorem threshold_geom_iff_accessed_incident_height_le {κ θ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {W : ℝ≥0 → ℝ} {U : ℝ≥0∞} {γ : ℝ≥0 → ℂ} {t : ℝ≥0}
    (hc : Continuous W) (h0 : W 0 = 0) (hg : IsGeneratingTrace W U γ)
    (htU : (t : ℝ≥0∞) ≤ U) :
    ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) (W t)
      (fun i => -rightImg (fun s : ℝ => -W s.toNNReal) (-flowLineXL b J 0 i) t)
      (fun j => rightImg (fun s : ℝ => W s.toNNReal) (flowLineXR b J 0 j) t) ↔
    (rightImg (fun s : ℝ => -W s.toNNReal) 0 t = -W t ∧
      sleLambda κ ≤ leftLim b (γ t).re + θ * chiC κ) ∨
    (rightImg (fun s : ℝ => W s.toNNReal) 0 t = W t ∧
      rightLim b (γ t).re + θ * chiC κ ≤ -sleLambda κ) := by
  by_cases ht : t = 0
  · subst t
    let D : ℝ → ℝ := fun s => W s.toNNReal
    let E : ℝ → ℝ := fun s => -W s.toNNReal
    have hD : Continuous D := hc.comp continuous_real_toNNReal
    have hE : Continuous E := (hc.comp continuous_real_toNNReal).neg
    have hD0 : D 0 = 0 := by simpa only [D, Real.toNNReal_zero] using h0
    have hE0 : E 0 = 0 := by simp only [E, Real.toNNReal_zero, h0, neg_zero]
    have hzE : rightImg (fun s : ℝ => -W s.toNNReal) 0 0 = 0 :=
      rightImg_zero hE hE0 (le_refl 0)
    have hzD : rightImg (fun s : ℝ => W s.toNNReal) 0 0 = 0 :=
      rightImg_zero hD hD0 (le_refl 0)
    have hL (i) : -rightImg E (-flowLineXL b J 0 i) 0 = flowLineXL b J 0 i := by
      rw [rightImg_zero hE hE0 (neg_nonneg.2 (flowLineXL_nonpos_seed b J 0 i)), neg_neg]
    have hR (i) : rightImg D (flowLineXR b J 0 i) 0 = flowLineXR b J 0 i :=
      rightImg_zero hD hD0 (flowLineXR_nonneg_seed b J 0 i)
    have eL := sum_collisionL_eq_leftLim (θ := θ) hκ hb (y := 0) (w := 0)
      (le_refl 0) (vL := flowLineXL b J 0) (fun i =>
        ⟨fun hi => hi.ge, fun hi => le_antisymm (flowLineXL_nonpos_seed b J 0 i) hi⟩)
    have eR := sum_collisionR_eq_rightLim (θ := θ) hκ hb (y := 0) (w := 0)
      (le_refl 0) (vR := flowLineXR b J 0) (fun i =>
        ⟨fun hi => hi.le, fun hi => le_antisymm hi (flowLineXR_nonneg_seed b J 0 i)⟩)
    change ForceWord.ThresholdCondition _ _ (W 0) (fun i => -rightImg E _ 0)
      (fun j => rightImg D _ 0) ↔ _
    simp only [NNReal.coe_zero, ForceWord.ThresholdCondition, hL, hR, h0, hg.1, Complex.zero_re,
      hzE, hzD,
      neg_zero, true_and, eL, eR]
    exact or_congr (by rw [← not_lt, cumWeightLeft_gt_iff hκ, not_lt])
      (by rw [← not_lt, cumWeightRight_gt_iff hκ, not_lt])
  · exact threshold_geom_iff_accessed_incident_height hκ hb hc h0 hg
      (pos_iff_ne_zero.2 ht) htU

/-- The criterion for each force-type reading of the supplied word. -/
theorem threshold_type_geom_iff_accessed_incident_height {κ θ : ℝ} (hκ : 0 < κ)
    {c : BoundaryWord} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (htype : c ∈ FCDet.typeSet κ θ nL nR ρL ρR)
    {W : ℝ≥0 → ℝ} {U : ℝ≥0∞} {γ : ℝ≥0 → ℂ} {t : ℝ≥0}
    (hc : Continuous W) (h0 : W 0 = 0) (hg : IsGeneratingTrace W U γ)
    (htU : (t : ℝ≥0∞) ≤ U) :
    ForceWord.ThresholdCondition ρL ρR (W t)
      (fun i => -rightImg (fun s : ℝ => -W s.toNNReal) (-FCDet.typeXL κ θ nL nR ρL ρR c i) t)
      (fun j => rightImg (fun s : ℝ => W s.toNNReal) (FCDet.typeXR κ θ nL nR ρL ρR c j) t) ↔
    (rightImg (fun s : ℝ => -W s.toNNReal) 0 t = -W t ∧
      sleLambda κ ≤ leftLim c.fn (γ t).re + θ * chiC κ) ∨
    (rightImg (fun s : ℝ => W s.toNNReal) 0 t = W t ∧
      rightLim c.fn (γ t).re + θ * chiC κ ≤ -sleLambda κ) := by
  obtain ⟨eL, eR, hxL, hxR, hρL, hρR⟩ := FCDet.isFlowType_of_mem_typeSet htype
  subst nL nR
  change FCDet.typeXL κ θ _ _ ρL ρR c = flowLineXL c.fn c.jumps 0 at hxL
  change FCDet.typeXR κ θ _ _ ρL ρR c = flowLineXR c.fn c.jumps 0 at hxR
  change ρL = flowLineRhoL κ c.fn c.jumps 0 θ at hρL
  change ρR = flowLineRhoR κ c.fn c.jumps 0 θ at hρR
  rw [hxL, hxR, hρL, hρR]
  exact threshold_geom_iff_accessed_incident_height_le hκ c.isPiecewiseConstantBoundaryData
    hc h0 hg htU

/-- Named remaining finite-endpoint geometry: an accessed side has a bad
incident height of the actual mean-identifying word. This is not asserted
to follow from a real terminal tip alone. -/
def FCK2CapTerminalAccess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (κ θ : ℝ) (d : PairData Ω) (β : Ω → BoundaryWord) (U : Ω → ℝ≥0∞)
    (γ : Ω → ℝ≥0 → ℂ) (W : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ meetSet d → ∀ T : ℝ≥0, (T : ℝ≥0∞) = U ω →
    (rightImg (fun s : ℝ => -W s.toNNReal ω) 0 T = -W T ω ∧
      sleLambda κ ≤ leftLim (β ω).fn (γ ω T).re + θ * chiC κ) ∨
    (rightImg (fun s : ℝ => W s.toNNReal ω) 0 T = W T ω ∧
      rightLim (β ω).fn (γ ω T).re + θ * chiC κ ≤ -sleLambda κ)

/-- The accessed-height assertion supplies all finite terminal force checks.
The force type may depend on the sample. -/
theorem terminalInputs_of_fcCapTerminalAccess {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {κ θ : ℝ} (hκ : 0 < κ) {d : PairData Ω} {β : Ω → BoundaryWord}
    {U : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ} {W : ℝ≥0 → Ω → ℝ}
    (hc : ∀ ω, Continuous (W · ω)) (h0 : ∀ ω, W 0 ω = 0)
    (hg : ∀ᵐ ω ∂P, ω ∈ meetSet d → IsGeneratingTrace (W · ω) (U ω) (γ ω))
    (ha : FCK2CapTerminalAccess P κ θ d β U γ W) :
    FCK2FinalTerminalInputs P κ θ d β U W := by
  constructor
  intro a
  filter_upwards [hg, ha] with ω hgω haω hB T hT
  exact (threshold_type_geom_iff_accessed_incident_height (c := β ω) (W := fun s => W s ω)
    (γ := γ ω) (U := U ω) hκ hB.2 (hc ω) (h0 ω) (hgω hB.1) hT.le).2
      (haω hB.1 T hT)

end InteractingSLE.Restart.FCPlumb
