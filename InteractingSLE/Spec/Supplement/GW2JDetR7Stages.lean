/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR7Threshold
import InteractingSLE.Spec.Supplement.GW2JDetR5Joint

/-! # Staged SDE availability throughout admissible boundary collisions -/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open LQGMetric (DistOn)
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE.Theorem14.GW2JDetR7

open Restart Exist Exist.Staged Exist.StagedLaw
open GW2JDetR5 GW2JointKernel GW2TipSystem GW2KM2

/-- A flow-line driver's continuation lifetime is infinite if every side
prefix is admissible. Contacts with the original real boundary are allowed. -/
theorem ae_lifetime_top_of_flow_prefixes {κ θ : ℝ} (hκ : 0 < κ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {b : ℝ → ℝ} {J : Finset ℝ} {h : Ω → DistOn upperHalfPlaneOpens}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hL : ∀ i : Fin (flowLineNL b J 0), -2 <
      ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), flowLineRhoL κ b J 0 θ j)
    (hR : ∀ i : Fin (flowLineNR b J 0), -2 <
      ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), flowLineRhoR κ b J 0 θ j)
    (hfl : IsFlowLineDriver κ b J θ P h W ζ) : ∀ᵐ ω ∂P, ζ ω = ⊤ := by
  obtain ⟨X, 𝓕, VL, VR, B, -, hC⟩ := hfl
  exact ae_lifetime_top_of_admissible_prefixes hκ
    (Theorem15.isOrderedForceWord_flowLine b J 0) hL hR hC.1

section Joint

variable {κ : ℝ} (hκ : 0 < κ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h)
    {b' : ℝ → ℝ} {J' : Finset ℝ} (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1)
      (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) {γ : Ω → ℝ≥0 → ℂ}
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (W · ω) ⊤ (γ ω))
    (s : ℝ≥0) {Hc : Ω → DistOn upperHalfPlaneOpens} (hHcm : Measurable Hc)
    (hHc : ∀ᵐ ω ∂P, γ ω s ∈ H →
      IsChartTransport (jointChart (Ito.rpath (W · ω)) s)
        1 (specOffset κ) (chiC κ) (h ω) (Hc ω))
    (c' : BoundaryWord) (hc'b : ∀ y ∉ J', c'.fn y = b' y)

include hκ hhm hb' hT hcf hζ hγ hHcm hHc hc'b in
/-- From the actual initial joint-chart law, every finite canonical stage
whose current side prefixes exceed `-2` remains available for all SDE times.
The complete recursive past is retained, including every earlier record. -/
theorem exists_joint_stage_infinite_of_admissible
    (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (θ : ℕ → ℝ)
    (τ : (n : ℕ) → Past RecData n → (ℝ≥0 → ℝ) × ℝ≥0∞ → ℝ≥0∞)
    (hτm : ∀ n, Measurable fun x : Past RecData n × ((ℝ≥0 → ℝ) × ℝ≥0∞) =>
      τ n x.1 x.2)
    (hτ : ∀ n (x : Past RecData n) (t : ℝ≥0),
      MeasurableSet[pathKilledSigma t] {e | τ n x e ≤ (t : ℝ≥0∞)}) :
    ∃ A : Set RecData, MeasurableSet A ∧
      (∀ᵐ ω ∂P, γ ω s ∈ H ↔ cfRec s W ζ ω ∈ A) ∧
      ∀ n, ∀ᵐ ω₀ ∂P,
        let st := stageState hκ h12p (jointWordOfRec (specOffset κ) κ c') θ τ
          (cfRec s W ζ) Hc n ω₀
        let c := stageWord (κ := κ) (jointWordOfRec (specOffset κ) κ c') θ n st.1
        st.1 ∈ finitePast A n →
        (∀ i : Fin (flowLineNL c.fn c.jumps 0), -2 <
          ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
            flowLineRhoL κ c.fn c.jumps 0 (θ n) j) →
        (∀ i : Fin (flowLineNR c.fn c.jumps 0), -2 <
          ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
            flowLineRhoR κ c.fn c.jumps 0 (θ n) j) →
        ∀ᵐ ω ∂(condExpKernel P (MeasurableSpace.comap
          (fun ω => (stageState hκ h12p (jointWordOfRec (specOffset κ) κ c') θ τ
            (cfRec s W ζ) Hc n ω).1) inferInstance) ω₀),
          (stagePiece hκ h12p (jointWordOfRec (specOffset κ) κ c') θ τ
            (cfRec s W ζ) Hc n ω).2 = ⊤ := by
  obtain ⟨A, hA, hev, hmodels⟩ := exists_joint_stage_couplings hκ hhm hb' hT hcf
    hζ hγ s hHcm hHc c' hc'b h12p h13 θ τ hτm hτ
  refine ⟨A, hA, hev, fun n => ?_⟩
  filter_upwards [hmodels n] with ω₀ hω₀
  dsimp only
  intro halive hL hR
  exact ae_lifetime_top_of_flow_prefixes hκ hL hR (hω₀ halive)

end Joint

end InteractingSLE.Theorem14.GW2JDetR7
