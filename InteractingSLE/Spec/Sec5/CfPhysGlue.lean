/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfPhysLocal
import InteractingSLE.Spec.Sec5.CrossCondTheta

/-!
# Physical locality of the raw counterflow image on the glued space

Packet PROVE-CFCHART2. Instantiate the strict passage with the landed
history-marked union theorem. No chart-locality or member input remains in this
glued-space theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open LQGMetric (DistOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.CfPhys

open WangWu LawUnique GlueCond Cond44Ref CfRegQ Prop411Q Coupling WholeField
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47 CrossCond.Theta
open Restart.DomainMarkov.K2

variable {κ θ : ℝ} {nL nR mL mR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} [mΩ₂ : MeasurableSpace Ω₂] {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- The raw image has the projection-member identities under the actual glued
law. The hypotheses are the two original couplings and their conditional law;
the physical-line locality and the entire inverse-capacity passage are proved. -/
theorem hasSafeMembers_cfGlueT (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hreg₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    {s : ℝ≥0} {E : Set (Ω × HistorySpace 0 0)}
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p)
    (hgood : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
      ((measurable_cfFieldT κ θ).comp hC.2.1)), p ∈ E) (a kC : ℝ) :
    HasSafeMembers
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1))
      (qRaw xL' xR' W VL VR ζ s E) univ (fun p => qT W VL VR ζ s E p) (qW W VL VR ζ s E)
      (fun p => Chart.chartTransport
        (isConformal_fChart (W := W) (VL := VL) (VR := VR) (ζ := ζ) (s := s) p) 1 a kC (h p.1)) := by
  obtain ⟨u₀, hu₀⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR xL xR
  have he : (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) =
      centredField (fun p => h p.1) u₀ := funext fun p => cenTT_cfFieldT κ θ u₀ (h p.1)
  have hgff := isZeroBoundaryGFF_cenTT_glue (θ := θ) (k := k) hC hu₀
  rw [he] at hgff
  refine hasSafeMembers_fChart_of_unionLocal hC.2.2.2.1 hEg hgood
    (hC.2.1.comp measurable_fst) hu₀.1 hgff ?_ a kC
  intro n j
  have hloc := isHistoryAvoidanceLocal_cfGlueT hC hκ hζ hcf hreg₂ hlaw hk hu₀ s (WangWu.ChartConst.dyq n j)
  rwa [he] at hloc

end InteractingSLE.Sec5.CfPhys
