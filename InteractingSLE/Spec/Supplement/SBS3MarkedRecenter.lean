/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3MarkedKernel
import InteractingSLE.Spec.Supplement.AStopSafePair

/-!
# S3: retained-law identification after a random real recentering

An entry coordinate measurable in the retained record is frozen by the
conditional kernel. The recentered field has the correspondingly shifted
word. Its chart relation uses exactly the inherited derivative lift.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.StagedLaw Restart

/-- A retained-measurable real recentering preserves the conditional word
law, for the actual sample-dependent translated field. -/
theorem ae_kernelWord_flowField {Ω : Type u} {𝒢 : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ)
    {Y : Ω → DistOn upperHalfPlaneOpens} (hY : Measurable Y)
    {β : Ω → BoundaryWord} {G : Set Ω} (hG : MeasurableSet[𝒢] G)
    (hsort : ∀ᵐ ω ∂P, ω ∈ G → (β ω).IsSorted)
    (hlaw : ∀ᵐ ω ∂P, ω ∈ G →
      IsGFFWithBoundaryData (condExpKernel P 𝒢 ω) Y (β ω).fn (β ω).jumps)
    {a : Ω → ℝ} (ha : Measurable[𝒢] a) :
    ∀ᵐ ω ∂P, ω ∈ G →
      IsGFFWithBoundaryData (condExpKernel P 𝒢 ω)
        (fun ω' => flowField (a ω') 0 (Y ω'))
        (BoundaryWord.shiftW (a ω) (β ω)).fn (BoundaryWord.shiftW (a ω) (β ω)).jumps := by
  have hZ : Measurable (fun ω => flowField (a ω) 0 (Y ω)) :=
    Measurable.comp (g := fun p : ℝ × DistOn upperHalfPlaneOpens => flowField p.1 0 p.2)
      (f := fun ω => (a ω, Y ω)) measurable_flowField_uncurry ((ha.mono h𝒢 le_rfl).prodMk hY)
  exact ae_isGFFWithBoundaryData_condExpKernel h𝒢
    (β := fun ω => BoundaryWord.shiftW (a ω) (β ω))
    (hsort.mono fun ω hs hω => BoundaryWord.isSorted_shiftW (hs hω) _) hZ
    (fun φ => RLC.AStopSafe.ae_condExp_cexp_flowField_eq_gaussCF_on h𝒢 hY hG
      (ae_condExp_gaussCF_of_kernel h𝒢 hY hsort hlaw) ha φ)

/-- The corresponding physical field is read in the recentered chart,
with no new constant or branch correction in its inherited argument lift. -/
theorem isChartTransport_recenter_word {c : Chart} (hc : c.IsConformal)
    (hlift : ContinuousOn (fun w => c.2.2 (c.2.1 w)) QuantumZipper.H)
    {χ : ℝ} {h Y : DistOn upperHalfPlaneOpens}
    (ht : IsChartTransport c 1 0 χ h Y) (a : ℝ) :
    IsChartTransport (c.recenter a) 1 0 χ h (flowField a 0 Y) := by
  rw [Chart.recenter_eq_trans]
  exact IsChartTransport.trans hc (isConformal_shiftChart a) hlift (continuousOn_shiftChart_lift a) ht
    (isChartTransport_shiftChart a _ _)

end InteractingSLE.Theorem14.SB.S3
