/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfNextRecord

/-!
# Strictly separated record marks under the original strip hypotheses

Packet PROVE-CFCHART2. The existing given-space good-history construction supplies
the interior flow trace. Strict side order is therefore proved for its actual records.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CfNext

open CfConv CfChart Exist Exist.Staged Exist.StagedLaw Restart LawUnique Lemma47Angle
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47

/-- Strict separation of the literal record marks follows from the original strip
hypotheses and the same two source inputs as the canonical chart construction. -/
theorem ae_record_strict_of_strip {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hA : PartAInputsSixteenDivOfClearance) (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ z : ℝ, z < 0 → z ∉ J → b z + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ z : ℝ, 0 < z → z ∉ J → sleLambda κ ≤ b z + a * chiC κ)
    (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hDreg : ∀ ω, IsRegularDriver (D ω))
    (hD : IsFlowLineDriver κ b J θ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2))
    {s : ℝ≥0} (hs : 0 < s) :
    let x := qxLT κ θ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0)
    let y := qxRT κ θ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0)
    ∀ᵐ ω ∂P, StrictAnti (recordXL s x (recOf (s : ℝ≥0∞) (D ω))) ∧
      StrictMono (recordXR s y (recOf (s : ℝ≥0∞) (D ω))) := by
  obtain ⟨h', 𝓕, VL, VR, B, N, E, hι, _, _, _, _, _, hEg, _, hEae, _⟩ :=
    CfChart.exists_chartCanon_omega hA href hκ hκ4 hb hcf hleft hright hθ hD hs
  dsimp only
  filter_upwards [hEae] with ω hω
  exact record_strict_of_good
    (fun i => (isOrderedForceWord_qx_angle κ θ _ _ _ _).2.1 i)
    (fun j => (isOrderedForceWord_qx_angle κ θ _ _ _ _).2.2.2 j)
    (strictAnti_qxL_angle κ θ _ _ _ _) (strictMono_qxR_angle κ θ _ _ _ _)
    (hEg _ hω) (hDreg ω) hs

end InteractingSLE.Sec5.CfNext
