/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLawMain
import InteractingSLE.Spec.Exist.StagedLaw2Run
import InteractingSLE.Spec.Exist.StagedLawPast
import InteractingSLE.Spec.Sec7.Aux122Disint
import InteractingSLE.GFF.Pushforward

/-!
# Two stage witnesses have the same boundary data off finite sets

Packet PROVE-GW2-SDE (round 19, decision D45 item 2). The launch word of a staged history is fixed by the frozen
stage law only through the conditional law of the field read in the launch chart: a stage witness `(β, Y)` says that,
under the regular conditional law given the retained past, `Y` (the chart transport of the field) is a GFF with the
data of `β ω₀`. So two witnesses of the same staged history at the same instruction have the same data off their
jumps at almost every launch (`SB.Lv.ae_eq_off_of_stageWitness`'s argument, for any schedule):

* **`ae_fn_eq_of_stageWitness`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Sdt

open Exist Exist.Staged Exist.StagedLaw Restart

/-- **Two stage witnesses have the same data off their jumps** at almost every launch. -/
theorem ae_fn_eq_of_stageWitness {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (hEm : ∀ j < k, Measurable (E j)) (hreg : ∀ j < k, ∀ ω, IsRegularDriver (E j ω))
    {β β' : Ω → BoundaryWord} {Y Y' : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h spec E k β Y) (hW' : IsStageWitness κ b jumps P h spec E k β' Y') :
    ∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none →
      ∀ y ∉ (β ω₀).jumps ∪ (β' ω₀).jumps, (β ω₀).fn y = (β' ω₀).fn y := by
  have h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ := by
    rw [pastSigma_eq_comap]
    exact (measurable_pastMap runMeasStatement hb spec hEm hreg k le_rfl).comap_le
  have hrun := ae_ae_run_eq (κ := κ) runMeasStatement hb spec hEm hreg (P := P)
  have hTk := Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hW.2.2.1
  have hTk' := Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hW'.2.2.1
  filter_upwards [hW.2.2.1, hW.2.2.2, hW'.2.2.2, hrun, hTk, hTk'] with ω₀ hT₀ hG₀ hG₀' hr₀ hTk₀ hTk₀' hF
  obtain ⟨hconf, -, -⟩ := hT₀ hF
  have hae : Y' =ᵐ[condExpKernel P (pastSigma κ b jumps spec E k) ω₀] Y := by
    filter_upwards [hr₀, hTk₀, hTk₀'] with ω hω hTω hTω'
    have hl : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none := by
      rw [launches_run_succ_of_run_eq (κ := κ) (b := b) (jumps := jumps) spec hω]
      exact hF
    obtain ⟨-, -, hTY⟩ := hTω hl
    obtain ⟨-, -, hTY'⟩ := hTω' hl
    rw [hω] at hTY hTY'
    exact hTY'.unique hconf hTY
  have hG'' : IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) Y
      (β' ω₀).fn (β' ω₀).jumps :=
    isGFFWithBoundaryData_congr_ae (hG₀' hF) hW.2.1 hae
  exact eq_of_isGFFWithBoundaryData (β ω₀).isPiecewiseConstantBoundaryData
    (β' ω₀).isPiecewiseConstantBoundaryData (hG₀ hF) hG''

end InteractingSLE.Theorem14.GW2Sdt
