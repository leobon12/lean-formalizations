/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWGeometry
import InteractingSLE.Spec.Sec5.CrossCondThetaMean

/-!
# The comparison flow hulls and their physical means

Packet PROVE-AUX61-SLITW. Choose bounded harmonic extensions of the force data
at each rational own time. The existing optional-hull coupling and its flow
marginal on the glued space supply local-set means, their integral pairings,
and harmonicity of the physical coupling means. No regularity assumption on
the chosen family of harmonic extensions is needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW

open WangWu LawUnique GlueCond Cond44Ref LocalSets WholeField Coupling
open CrossCond.Theta

universe u

variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)} [IsMarkovKernel k]
  {u₀ : ℂ → ℝ}

/-- The comparison means at every rational own time exist on the actual glued
space and satisfy SLIT's local-mean, harmonicity and representation clauses. -/
theorem exists_rational_patch_means
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) :
    ∃ (uph : ℚ → Ω → ℂ → ℝ) (g : ℚ → Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens),
      (∀ j ω, IsBoundedHarmonicExtension
        (forceBoundaryData κ ρL ρR
          (fun i => VL i (rationalTime j) ω - W (rationalTime j) ω)
          (fun i => VR i (rationalTime j) ω - W (rationalTime j) ω))
        (forceJumpSet (fun i => VL i (rationalTime j) ω - W (rationalTime j) ω)
          (fun i => VR i (rationalTime j) ω - W (rationalTime j) ω)) (uph j ω)) ∧
      (∀ j, IsLocalSetMean
        (fun p : Ω × HistorySpace 0 0 => hullAt (rationalTime j) (killedHistory W VL VR ζ p.1))
        (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))
        (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) (g j)) ∧
      ∀ j, ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
          ((measurable_cfFieldT κ θ).comp hC.2.1)),
        InnerProductSpace.HarmonicOnNhd
          (couplingMean κ (fun s : ℝ => W s.toNNReal p.1) (rationalTime j) (uph j p.1))
          (H \ hullAt (rationalTime j) (killedHistory W VL VR ζ p.1)) ∧
        ∀ φ : TestOn upperHalfPlaneOpens,
          tsupport φ ⊆ H \ hullAt (rationalTime j) (killedHistory W VL VR ζ p.1) →
          g j p φ = ∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal p.1)
            (rationalTime j) (uph j p.1) z - u₀ z) * φ z := by
  classical
  have hex : ∀ (j : ℚ) (ω : Ω), ∃ u : ℂ → ℝ, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR
        (fun i => VL i (rationalTime j) ω - W (rationalTime j) ω)
        (fun i => VR i (rationalTime j) ω - W (rationalTime j) ω))
      (forceJumpSet (fun i => VL i (rationalTime j) ω - W (rationalTime j) ω)
        (fun i => VR i (rationalTime j) ω - W (rationalTime j) ω)) u :=
    fun j ω => Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR
      (fun i => VL i (rationalTime j) ω - W (rationalTime j) ω)
      (fun i => VR i (rationalTime j) ω - W (rationalTime j) ω)
  choose uph hu using hex
  have hexg := fun j => exists_isLocalSetMean_flowHull_glueT (θ := θ) (k := k)
    hC hκ hζ hu₀ (rationalTime j) (hu j)
  choose g hg hrep using hexg
  refine ⟨uph, g, hu, hg, fun j => ?_⟩
  have hXm : Measurable (fun ω => cfFieldT κ θ (h ω)) := (measurable_cfFieldT κ θ).comp hC.2.1
  have hgood := ae_glue_fst (μ := P) k hXm (Aux50Hit.ae_isGoodPath hC.1 hζ)
  filter_upwards [hgood, hrep j] with p hp hpair
  refine ⟨?_, hpair⟩
  have hK : hullAt (rationalTime j) (killedHistory W VL VR ζ p.1) =
      fwdHull (Ito.rpath (fun t => W t p.1)) (rationalTime j) :=
    Aux50Hit.regHull_stopHistory_cstop hp (rationalTime j)
  rw [hK]
  exact Sec7.SideHeight.harmonicOnNhd_couplingMean hp.continuous_rpath
    (rationalTime j).coe_nonneg (hu j p.1).1

end InteractingSLE.Sec5.Aux61SlitW
