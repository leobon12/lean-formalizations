/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondGenLawMean

/-!
# The stopped flow hull's own mean before a finite continuation threshold

PROVE-CROSSCOND-GEN. Reuse the optional hull coupling and `SideHeight` for any
stopping time strictly below the lifetime. Boundary contacts require no extra
non-hitting bounds. `A` is any hitting-measurable version of the actual stopped hull;
no identification of its filling with its trace is made.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.CrossCond.Gen

open LocalSets WholeField

section Flow

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {u₀ : ℂ → ℝ} {A : Ω → Set ℂ} {τ : Ω → WithTop ℝ≥0} {u : Ω → ℂ → ℝ}

/-- The own mean of a stopped boundary-hitting flow hull, with arbitrary finite
lifetime. This supplies the flow-side mean required by `cfGlueGen_union_inputs`. -/
theorem exists_isLocalSetMean_stoppedFlow
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    (hA : Measurable[mΩ, hittingSigma] A)
    (hAK : ∀ᵐ ω ∂P, A ω = fwdHull (Ito.rpath (W · ω)) ((τ ω).untopD 0 : ℝ≥0))
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun j => VR j ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun j => VR j ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) (u ω)) :
    IsLocalSet A (centredField h u₀) P ∧
    ∃ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A (centredField h u₀) P g ∧
      ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
        g ω φ = ∫ z, (couplingMean κ (Ito.rpath (W · ω)) ((τ ω).untopD 0 : ℝ≥0) (u ω) z - u₀ z) * φ z := by
  have htrans : ∀ ω, IsTranslateAddConst 0 0 (h ω) (h ω) :=
    fun ω => by simpa only [zero_mul] using Sec7.StripSysField.isTranslateAddConst_zero_self (h ω) 0
  have hrel : EqOn u₀ (fun z => u₀ (z + ((0 : ℝ) : ℂ)) + 0) H := by
    intro z _
    simp only [Complex.ofReal_zero, add_zero]
  have hAK' : ∀ᵐ ω ∂P, A ω =
      (fun z : ℂ => z + ((0 : ℝ) : ℂ)) '' fwdHull (Ito.rpath (W · ω)) ((τ ω).untopD 0 : ℝ≥0) := by
    simpa only [Complex.ofReal_zero, add_zero, image_id'] using hAK
  have hloc := Coupling.IsLocalSet.congr_set
    (Sec7.SideHeight.isLocalSet_flowHull hC htrans hu₀.1 hu₀ hrel hX hτ hτζ) hAK'
  have hF := isZeroBoundaryGFF_centredField hC hu₀
  obtain ⟨g, hg⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hF hA hloc
  have hid := Sec7.SideHeight.ae_apply_eq_of_isLocalSetMean_flowHull hC hκ htrans hF hu₀.1 hu₀ hrel
    hX hτ hτζ hA hAK' hg hu
  refine ⟨hloc, g, hg, ?_⟩
  filter_upwards [hid] with ω hω φ hφ
  change g ω φ = ∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω)
    ((τ ω).untopD 0 : ℝ≥0) (u ω) z - u₀ z) * φ z
  simpa only [Complex.ofReal_zero, sub_zero] using hω φ hφ

end Flow

end InteractingSLE.Sec5.CrossCond.Gen
