/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRBoundaryLimits
import InteractingSLE.Spec.Sec7.PocketSideInCensusVersions

/-!
# GW4: boundary limits need only one retained mean version

Pairing uniqueness on a countable bump family gives equality of the canonical
harmonic representatives throughout the active domain. Thus source reference
laws can use one chosen current mean, without an intersection over versions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdMapInv logDerivFwd)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open Restart Exist.StagedLaw Sec7.PhaseSel Sec7.Aux119Heights
  Supp8.Q3Stop LocalSets WholeField MartChar

/-- Canonical harmonic representatives of two local-set-mean versions agree
on the whole active domain, on one event for all physical points. -/
theorem ae_harmRep_eqOn_of_localSetMeans {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {A : Ω → Set ℂ}
    {h g g' : Ω → DistOn upperHalfPlaneOpens}
    (hA : Measurable[_, hittingSigma] A) (hh : Measurable h)
    (hOpen : ∀ ω, IsOpen (H \ A ω))
    (hg : IsLocalSetMean A h ν g) (hg' : IsLocalSetMean A h ν g') :
    ∀ᵐ ω ∂ν, EqOn (harmRep (g ω) (H \ A ω))
      (harmRep (g' ω) (H \ A ω)) (H \ A ω) := by
  filter_upwards [Sec7.PocketStopSide.ae_mean_apply_eq_on_compl hA hh hOpen hg hg',
    hg.2.1, hg'.2.1] with ω hEq hH hH'
  obtain ⟨hv, hrep⟩ := harmRep_spec hH
  obtain ⟨hv', hrep'⟩ := harmRep_spec hH'
  exact Sec6.eqOn_of_integral_mul_eq (hOpen ω) sdiff_subset hv hv'
    (fun φ hφ => (hrep φ hφ).symm.trans ((hEq φ hφ).trans (hrep' φ hφ)))

/-- The boundary-limit assertion at one physical line for one specified
current mean. Exceptions are physical and every incident fiber is retained. -/
def ComponentBoundaryLimitAt {Ω : Type*} [MeasurableSpace Ω]
    (k : ℝ) (c₀ : BoundaryWord) (F : Frame) (ν : Measure Ω)
    (X : Ω → DistOn upperHalfPlaneOpens) (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (u₀ : ℂ → ℝ)
    (B : ℝ≥0 → Ω → Set ℂ) (d : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ᵐ ω ∂ν, lineClock F Wd GT V t ω < V ω →
    let q := (lineClock F Wd GT V t ω).toNNReal
    let inv := fwdMapInv (wpath R ω) q
    let vL := fun i => componentVL k c₀ X R V i q ω - R q ω
    let vR := fun j => componentVR k c₀ X R V j q ω - R q ω
    ∃ E : Set ℂ, E.Finite ∧ ∀ x : ℝ, x ∉ forceJumpSet vL vR →
      extendFrom H inv (x : ℂ) ∉ E →
      Tendsto (fun y => harmRep (g ω) (H \ B t ω) (inv y) + u₀ (inv y) +
          chiC k * (logDerivFwd (wpath R ω) q (inv y)).im)
        (𝓝[H] (x : ℂ))
        (𝓝 (phaseData k (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀))
          vL vR (d q ω) x))

/-- One version at each physical line suffices for the unchanged boundary
input, which quantifies over every version. No uncountable null-set union
over either versions, boundary accesses or test functions is used. -/
theorem componentBoundaryLimits_of_oneVersion {Ω : Type*} [MeasurableSpace Ω]
    {k : ℝ} {c₀ : BoundaryWord} {F : Frame} {ν : Measure Ω} [IsProbabilityMeasure ν]
    {X : Ω → DistOn upperHalfPlaneOpens} {Wd R : ℝ≥0 → Ω → ℝ}
    {GT : Set Ω} {V : Ω → ℝ≥0∞} {hWm : ∀ r, Measurable (Wd r)}
    {u₀ : ℂ → ℝ} {ℋ : ℝ≥0 → MeasurableSpace Ω} {B : ℝ≥0 → Ω → Set ℂ}
    {d : ℝ≥0 → Ω → ℝ}
    (hX : IsGFFWithBoundaryData ν X c₀.fn c₀.jumps)
    (hloc : ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B)
    (hR0 : ∀ ω, R 0 ω = 0) (hRc : ∀ ω, Continuous (R · ω))
    (hOne : ∀ t, ∃ g : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (B t) (centredField X u₀) ν g ∧
        ComponentBoundaryLimitAt k c₀ F ν X Wd GT R V u₀ B d t g) :
    ComponentBoundaryLimits k c₀ F ν X Wd GT R V u₀ B d := by
  obtain ⟨hu₀, -, -, hBm, hBc, -, hshape⟩ := hloc
  have hzero := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hX hu₀
  intro t g hg
  obtain ⟨g₀, hg₀, hlim⟩ := hOne t
  filter_upwards [ae_harmRep_eqOn_of_localSetMeans (hBm t) hzero.measurable
    (fun ω => (hBc t ω).2) hg hg₀, hlim, hshape t] with ω heq hs hdom hlt
  obtain ⟨E, hE, hside⟩ := hs hlt
  refine ⟨E, hE, fun x hx hxE => (hside x hx hxE).congr' ?_⟩
  refine eventually_nhdsWithin_of_forall fun y hy => ?_
  have hy' := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull
    ((hRc ω).comp continuous_real_toNNReal)
    (by simpa only [Function.comp_apply, Real.toNNReal_zero] using hR0 ω)
    (lineClock F Wd GT V t ω).toNNReal.coe_nonneg hy
  have hyB : fwdMapInv (wpath R ω) (lineClock F Wd GT V t ω).toNNReal y ∈
      H \ B t ω := by
    rw [hdom hlt]
    exact hy'
  dsimp only
  rw [heq hyB]

end InteractingSLE.Theorem14.GW4Fix
