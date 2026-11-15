/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWRule
import InteractingSLE.Spec.Sec7.Lemma725RefMarksGerm

/-!
# The physical comparison union on the glued probability space

Packet PROVE-AUX61-SLITW. UNIONLOC applies to the rule `max T q` by the
Galmarino property proved in `Aux61SlitWRule`. The current marks are nested
in its marks, and a recorded smaller germ can then be retained by R69's lemma.
This file uses the original optional-hull coupling, with no determination input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open QuantumZipper (H chiC)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW

open Aux61ULoc WangWu LawUnique Cond44Ref CfRegQ WholeField LocalSets
open CrossCond.Theta
open Sec7.PocketStopWallsFin (regHull)

universe u

section Physical

variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
  {k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)} [IsMarkovKernel k]
  {u₀ : ℂ → ℝ}

/-- The larger union in SLIT's physical wiring is marked local at `max T q`
on the actual glued measure, with the larger stopped-record marks. -/
theorem isHistoryAvoidanceLocal_comparison_union
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hθb : CfThetaBounds κ θ ρL ρR xL xR)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (s q : ℝ≥0) {ρ : HistorySpace 0 0 × HistorySpace nL nR → ℝ≥0∞}
    (hρm : Measurable ρ) (hρ : IsGalmarinoRule stopRec ρ) :
    @IsHistoryAvoidanceLocal (Ω × HistorySpace 0 0)
      (ruleMarks stopRec (fun z => max (ρ z) (q : ℝ≥0∞))
        (fun p => stopRec s p.2) (fun p => killedHistory W VL VR ζ p.1))
      Prod.instMeasurableSpace
      (unionAt (fun p => GlueCond.cfHullQ s p.2) (fun r p => regHull W ζ r p.1)
        (fun p => max (ρ (stopRec s p.2, killedHistory W VL VR ζ p.1)) (q : ℝ≥0∞)))
      (fun p => centredField h u₀ p.1)
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) :=
  isHistoryAvoidanceLocal_unionAt_rule_cfGlueT hC hκ hζ hθb hcf hlaw hk hu₀ s
    (hρm.max measurable_const) (isGalmarinoRule_max hρ q)

end Physical

section Germ

variable {X : Type*} {ℳ ℋ : MeasurableSpace X} [mX : MeasurableSpace X]
  {μ : Measure X} [IsProbabilityMeasure μ]

/-- Adding the initial recorded germ to the larger union preserves locality
and also supplies the marks inclusion required by `SlitWiring`. -/
theorem comparison_union_with_retained_germ {h : X → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h μ) (hℳ : ℳ ≤ mX)
    {A₀ A' : X → Set ℂ} (hA'm : Measurable[mX, hittingSigma] A')
    (hloc : IsHistoryAvoidanceLocal ℳ A' h μ)
    (hA₀m : Measurable[ℳ, hittingSigma] A₀) (hsub : ∀ x, A₀ x ∩ H ⊆ A' x)
    (hℋ : ℋ ≤ ℳ) :
    IsHistoryAvoidanceLocal (ℳ ⊔ germSigma A₀ h) A' h μ ∧
      ℋ ⊔ germSigma A₀ h ≤ ℳ ⊔ germSigma A₀ h :=
  ⟨Sec7.Lemma725RefMarks.isHistoryAvoidanceLocal_sup_germSigma hh hℳ hA'm hloc hA₀m hsub,
    sup_le_sup_right hℋ _⟩

end Germ

end InteractingSLE.Sec5.Aux61SlitW
