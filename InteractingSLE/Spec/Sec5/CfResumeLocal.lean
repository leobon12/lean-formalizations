/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfResumeZero

/-!
# Locality for the exact filtration and driver of the chart conversion

Packet PROVE-CFCHART2, continuation. The remaining physical locality input is the member
identity for the raw image process. Given that input, every null modification and record
enlargement in `CfConv.exists_converted_chart` is discharged here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfResume

open CfGiven CfChart CfConv LawUnique Exist Exist.Staged Exist.StagedLaw
open Restart.DomainMarkov.K2 CrossRestart.KernelQ CrossRestart.KernelQ.Kill47

/-- Freeze the driver off a conull event, replace an almost surely infinite lifetime
by infinity, and retain the record. All member identities survive these changes. -/
theorem hasSafeMembers_regularize_top_record {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓐 : Filtration ℝ≥0 mΩ} {A : Set Ω}
    (hA : MeasurableSet A) (hAe : ∀ᵐ ω ∂P, ω ∈ A) {ζ : Ω → ℝ≥0∞}
    (hζ : ∀ ω ∈ A, ζ ω = ⊤) {W : ℝ≥0 → Ω → ℝ}
    {R : Type*} [MeasurableSpace R] {r : Ω → R} (hr : Measurable r)
    (hrec : ∀ t, MeasurableSpace.comap r inferInstance ≤ aeSigma P (𝓐 t))
    {X : Ω → DistOn upperHalfPlaneOpens} (h : HasSafeMembers P 𝓐 univ ζ W X) :
    HasSafeMembers P (recordFiltration (eventFiltration 𝓐 A hA) r hr)
      univ (fun _ => ⊤) (eventDriver A W) X := by
  have h₀ := hasSafeMembers_event_record hA hAe hr hrec h
  apply hasSafeMembers_congr_ae h₀ (ae_eq_refl _) (hAe.mono fun ω hω => hζ ω hω)
    (hAe.mono fun _ hω t => (eventDriver_eq hω t).symm) (ae_eq_refl _)

/-- Locality in the exact retained filtration used by the positive-time conversion.
`hmem` is the still-required physical locality theorem in raw image coordinates. -/
theorem hasSafeMembers_record_image {Z Ω : Type*} [MeasurableSpace Z]
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR mL mR : ℕ}
    {W : ℝ≥0 → Z → ℝ} {VL : Fin nL → ℝ≥0 → Z → ℝ}
    {VR : Fin nR → ℝ≥0 → Z → ℝ} {ζ : Z → ℝ≥0∞} {s : ℝ≥0}
    {xL : Fin mL → ℝ} {xR : Fin mR → ℝ} {E : Set (Z × HistorySpace 0 0)}
    {ι : Ω → Z × HistorySpace 0 0} (hι : Measurable ι)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p)
    (hEtop : ∀ p ∈ E, qT W VL VR ζ s E p = ⊤) (hEae : ∀ᵐ ω ∂P, ι ω ∈ E)
    {κ : ℝ} {h : Ω → DistOn upperHalfPlaneOpens} {R : Ω → RecData}
    (hR : Measurable R)
    (hReq : ∀ ω, R ω = recOf (s : ℝ≥0∞) ((fun t => W t (ι ω).1), ζ (ι ω).1))
    (hmem : HasSafeMembers P (Coupling.filtrationComap (qRaw xL xR W VL VR ζ s E) hι)
      univ (fun ω => qT W VL VR ζ s E (ι ω))
      (fun t ω => qW W VL VR ζ s E t (ι ω)) (fun ω => imgField κ (R ω) (h ω))) :
    HasSafeMembers P
      (recordFiltration
        (eventFiltration (Coupling.filtrationComap (qRaw xL xR W VL VR ζ s E) hι)
          (ι ⁻¹' E) (hι hE)) R hR)
      univ (fun _ => ⊤) (eventDriver (ι ⁻¹' E) (fun t ω => qW W VL VR ζ s E t (ι ω)))
      (fun ω => imgField κ (R ω) (h ω)) := by
  apply hasSafeMembers_regularize_top_record (hι hE) hEae (fun ω hω => hEtop (ι ω) hω) hR
    (fun t => ?_) hmem
  have heq : R = fun ω => recOf (s : ℝ≥0∞) ((fun r => W r (ι ω).1), ζ (ι ω).1) :=
    funext hReq
  rw [heq]
  exact recordSigma_le_aeSigma (xL := xL) (xR := xR) (E := E) hι hX
    (hEae.mono fun ω hω => hEg (ι ω) hω) t

end InteractingSLE.Sec5.CfResume
