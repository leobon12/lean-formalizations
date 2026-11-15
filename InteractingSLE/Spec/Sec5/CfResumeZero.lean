/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfResumeMemberLaw
import InteractingSLE.Spec.Supplement.GW2aContStepAux
import InteractingSLE.Spec.Jordan.Coupling
import InteractingSLE.Spec.Coupling.WholeField9Mean

/-!
# The record field at prefix time zero

Packet PROVE-CFCHART2, continuation. A zero-time record has the identity chart on the
upper half-plane, regardless of its terminal flag. Its image field is the original
counterflow parameter field, so its pairings are integrable without a random-chart estimate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn TestOn)
open QuantumZipper (H chiC)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CfResume

open CfGiven Exist Exist.Staged Exist.StagedLaw

/-- At time zero the record chart transports the field to itself. The terminal flag
does not enter the chart. -/
theorem recField_eq_of_rtime_zero {r : RecData} (hr : rtime r = 0)
    (κ : ℝ) (f : DistOn upperHalfPlaneOpens) : recField κ r f = f := by
  have ht := isChartTransport_recField κ r f
  rw [recChart_eq, hr] at ht
  exact IsChartTransport.eq_of_id
    ((Theorem14.GW2aCont.isChartTransport_loewner_zero_iff
      (continuous_rdrv r) (rdrv_zero r)).1 ht)

/-- Every time-zero record has zero capacity, including immediately killed records. -/
theorem rtime_recOf_zero (e : (ℝ≥0 → ℝ) × ℝ≥0∞) : rtime (recOf 0 e) = 0 := by
  rw [rtime_recOf_coe, min_eq_left (zero_le : (0 : ℝ≥0∞) ≤ e.2),
    ENNReal.toNNReal_zero, NNReal.coe_zero]

/-- Reading a field through any time-zero record leaves it unchanged. -/
theorem recField_recOf_zero (κ : ℝ) (e : (ℝ≥0 → ℝ) × ℝ≥0∞)
    (f : DistOn upperHalfPlaneOpens) : recField κ (recOf 0 e) f = f :=
  recField_eq_of_rtime_zero (rtime_recOf_zero e) κ f

/-- The record inverse is the identity on the upper half-plane at time zero. -/
theorem recChart_recOf_zero_inv (e : (ℝ≥0 → ℝ) × ℝ≥0∞) {z : ℂ} (hz : z ∈ H) :
    (recChart (recOf 0 e)).2.1 z = z := by
  rw [recChart_eq, rtime_recOf_zero]
  exact Theorem14.GW2aCont.loewner_zero_inv
    (continuous_rdrv (recOf 0 e)) (rdrv_zero (recOf 0 e)) hz

/-- The time-zero image field equals any parameter field satisfying the original
counterflow transport rule. -/
theorem imgField_recOf_zero_eq {κ : ℝ} (e : (ℝ≥0 → ℝ) × ℝ≥0∞)
    {f g : DistOn upperHalfPlaneOpens}
    (ht : IsChartTransport infinitySourceChart (-1) (-(π * chiC κ))
      (chiC (16 / κ)) f g) : imgField κ (recOf 0 e) f = g := by
  have hi := isChartTransport_imgField κ (recOf 0 e) f
  rw [recField_recOf_zero] at hi
  exact IsChartTransport.unique Chart.isConformal_infinitySourceChart hi ht

/-- Time-zero image-field integrability is already supplied by the given counterflow
coupling; no estimate for a field-dependent test is needed at this time. -/
theorem integrable_imgField_recOf_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W ζ)
    (D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (φ : TestOn upperHalfPlaneOpens) :
    Integrable (fun ω => imgField κ (recOf 0 (D ω)) (h ω) φ) P := by
  obtain ⟨b, J, g, _, htr, g', 𝓕, VL, VR, B, hshift, hC⟩ := hcf
  have he : ∀ ω, imgField κ (recOf 0 (D ω)) (h ω) = g' ω := by
    intro ω
    rw [imgField_recOf_zero_eq (D ω) (htr ω)]
    exact (Markov.eq_of_isTranslateAddConst_zero (by simpa only [zero_mul] using hshift ω)).symm
  simpa only [he] using WholeField.integrable_pairing hC φ

/-- At prefix time zero the physical clock is the identity. The interior-trace
condition remains an explicit geometric hypothesis. -/
theorem exists_physical_clock_zero (e : (ℝ≥0 → ℝ) × ℝ≥0∞) {η : ℝ≥0 → ℂ}
    (hH : ∀ u : ℝ≥0, 0 < u → WangWu.negInv (η u) ∈ H) :
    ∃ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ ∧ StrictMono ℓ ∧ ℓ 0 = 0 ∧
      ∀ u : ℝ≥0, 0 < u → WangWu.negInv (η u) ∈ H ∧
        WangWu.negInv (η (ℓ u)) =
          (recChart (recOf 0 e)).2.1 (WangWu.negInv (η u)) := by
  refine ⟨id, continuous_id, strictMono_id, rfl, fun u hu => ⟨hH u hu, ?_⟩⟩
  exact (recChart_recOf_zero_inv e (hH u hu)).symm

end InteractingSLE.Sec5.CfResume
