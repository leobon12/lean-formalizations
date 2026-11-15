/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfResumeLocal

/-!
# The time-zero clock and record under the strip hypotheses

Packet PROVE-CFCHART2, continuation. Reuse the good-history conclusion of the existing
positive-time construction at time one to obtain an interior counterflow trace and an
infinite flow lifetime. These facts discharge the time-zero clock and record enlargement.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn)
open QuantumZipper (H chiC)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CfResume

open CfChart CfConv CfGiven LawUnique Exist Exist.Staged Exist.StagedLaw
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47

section Strip

variable {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u}
  [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {W' W : ℝ≥0 → Ω → ℝ}
  {ζ' ζ : Ω → ℝ≥0∞} {η : Ω → ℝ≥0 → ℂ}

/-- The original positive-time good-history theorem already gives the two path facts
needed at prefix time zero. The time one construction is used only to obtain its good set. -/
theorem ae_top_and_interior_of_strip
    (hA : PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J →
      b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J →
      sleLambda κ ≤ b y + a * chiC κ)
    (hθ : θ ∈ Icc (-(π / 2)) (π / 2))
    (hD : IsFlowLineDriver κ b J θ P h W ζ)
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) :
    (∀ᵐ ω ∂P, ζ ω = ⊤) ∧
      ∀ᵐ ω ∂P, ∀ u : ℝ≥0, 0 < u → WangWu.negInv (η ω u) ∈ H := by
  obtain ⟨h', 𝓕, VL, VR, B, N, E, hι, _, _, _, _, _, hEg, _, hEae, _⟩ :=
    CfChart.exists_chartCanon_omega hA href hκ hκ4 hb hcf hleft hright hθ hD
      (s := 1) zero_lt_one
  constructor
  · filter_upwards [hEae] with ω hω
    exact (hEg _ hω).1.1
  · filter_upwards [hEae, ae_histLine_cfHistory_eq hcf hζ' hη] with ω hω he u hu
    have hm := histLine_mem_H (hEg _ hω) (show (0 : ℝ) < u from hu)
    rw [he] at hm
    exact WangWu.negInv_mem_H (by simpa only [Real.toNNReal_coe] using hm)

end Strip

/-- The samples and capacity of a time-zero record are constant. Its terminal flag
still records whether the lifetime is zero; it must not be silently discarded. -/
theorem recOf_zero {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) :
    recOf 0 e = (fun _ => 0, 0, decide (e.2 ≤ 0)) := by
  refine Prod.ext (funext fun q => ?_) (Prod.ext ?_ rfl)
  · change e.1 (min _ (min 0 e.2)).toNNReal = 0
    rw [min_eq_left (zero_le : (0 : ℝ≥0∞) ≤ e.2),
      min_eq_right (zero_le : (0 : ℝ≥0∞) ≤ _), ENNReal.toNNReal_zero]
    exact he.2.1
  · change min 0 e.2 = 0
    exact min_eq_left zero_le

/-- A positive flow lifetime makes the time-zero record the same deterministic datum. -/
theorem recOf_zero_of_pos {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    (hζ : 0 < e.2) : recOf 0 e = (fun _ => 0, 0, false) := by
  rw [recOf_zero he, decide_eq_false (not_le_of_gt hζ)]

/-- The time-zero record can be added to any filtration when the flow lifetime is
almost surely positive, even if the terminal flag varies on a null set. -/
theorem recordSigma_zero_le_aeSigma {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hDreg : ∀ ω, IsRegularDriver (D ω)) (hζ : ∀ᵐ ω ∂P, 0 < (D ω).2)
    (𝓐 : Filtration ℝ≥0 mΩ) (t : ℝ≥0) :
    MeasurableSpace.comap (fun ω => recOf 0 (D ω)) inferInstance ≤ aeSigma P (𝓐 t) :=
  comap_le_aeSigma (g := fun _ => (fun _ => 0, 0, false)) measurable_const
    (hζ.mono fun ω hω => recOf_zero_of_pos (hDreg ω) hω)

/-- The strip good-history theorem discharges the geometric premise of the zero-time
clock at almost every sample. -/
theorem ae_physical_clock_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) {η : Ω → ℝ≥0 → ℂ}
    (hH : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, 0 < u → WangWu.negInv (η ω u) ∈ H) :
    ∀ᵐ ω ∂P, ∃ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ ∧ StrictMono ℓ ∧ ℓ 0 = 0 ∧
      ∀ u : ℝ≥0, 0 < u → WangWu.negInv (η ω u) ∈ H ∧
        WangWu.negInv (η ω (ℓ u)) =
          (recChart (recOf 0 (D ω))).2.1 (WangWu.negInv (η ω u)) :=
  hH.mono fun ω hω => exists_physical_clock_zero (D ω) hω

end InteractingSLE.Sec5.CfResume
