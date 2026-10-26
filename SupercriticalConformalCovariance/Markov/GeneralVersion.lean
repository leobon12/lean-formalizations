import SupercriticalConformalCovariance.ZBConformal.HarmonicRepresentative
import LQGMetric.Field.MarkovAsmB

/-!
# Arbitrary-domain consequences of a distribution version of the Markov projection

These lemmas require only `ZBAdmissible V`, not a normalization circle. The existence of the
distribution-valued version itself is a separate analytic problem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace Laplacian
open InnerProductSpace
open LQGMetric LQGMetric.MarkovZB LQGMetric.MarkovHarm LQGMetric.MarkovExt
open LQGMetric.MarkovAsm LQGMetric.MarkovWeyl3 LQGMetric.MarkovGerm

namespace SupercriticalConformalCovariance.Markov

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC} {V : Opens ℂ}

/-- Any distribution version of the canonical zero extension restricts to a zero-boundary GFF. -/
theorem isZeroBoundaryGFF_restrict_of_version (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V) {hz : Ω → DistC} (hzm : Measurable hz)
    (hzae : ∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P] zbExt hh V φ) :
    IsZeroBoundaryGFF V (fun ω => restrictTo V (hz ω)) P := by
  refine ⟨(measurable_restrictTo V).comp hzm,
    isZBGFFProcess_congr (isZBGFFProcess_zbProc hh hV)
      (fun φ => (measurable_distOn_apply φ).comp ((measurable_restrictTo V).comp hzm))
      fun φ => ?_⟩
  filter_upwards [hzae (extC V φ), zbExt_ae_eq_zbProc hh φ] with ω h1 h2
  rw [← h2, ← h1]
  rfl

/-- The complement of any global version is simultaneously harmonic on all of `V`. -/
theorem ae_harmonic_sub_of_version (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V) {hz : Ω → DistC}
    (hzae : ∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P] zbExt hh V φ) :
    ∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, HarmonicOnNhd g (V : Set ℂ) ∧
      ∀ φ : TestOn V, restrictTo V (h ω - hz ω) φ = ∫ x, g x * φ x := by
  have key : ∀ f : zsSub (V : Set ℂ),
      ∀ᵐ ω ∂P, restrictTo V (h ω - hz ω) (cmTestOn f) = 0 := fun f => by
    filter_upwards [hzae (extC V (cmTestOn f)), zbExt_ae_eq_zbProc hh (cmTestOn f),
      zbProc_cmTestOn_ae hh hV f] with ω h1 h2 h3
    change (h ω - hz ω) (extC V (cmTestOn f)) = 0
    rw [sub_apply, h1, h2, h3, extC_cmTestOn, sub_self]
  have hall : ∀ᵐ ω ∂P, ∀ j : ℕ × ℕ,
      restrictTo V (h ω - hz ω) (cmTestOn (toZs (distGen V j))) = 0 :=
    ae_all_iff.2 fun j => key _
  filter_upwards [hall] with ω hω
  set T := restrictTo V (h ω - hz ω)
  have hT0 : T.comp (lapV V) = 0 := by
    apply injective_distOn_pairings V
    funext j
    show T (lapV V (distGen V j)) = 0
    rw [← cmTestOn_toZs]
    exact hω j
  refine exists_harmonic_of_laplacian_eq_zero T fun f => ?_
  rw [← toZs_ofZs f, cmTestOn_toZs]
  exact congrArg (fun S : DistOn V => S (ofZs f)) hT0

/-- A jointly measurable representative of the complement, canonical from its distribution. -/
theorem exists_joint_harmonic_of_version (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V) {hz : Ω → DistC} (hzm : Measurable hz)
    (hzae : ∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P] zbExt hh V φ) :
    ∃ H : Ω → ℂ → ℝ,
      Measurable (fun p : Ω × ℂ => H p.1 p.2) ∧
      (∀ᵐ ω ∂P, HarmonicOnNhd (H ω) (V : Set ℂ) ∧
        ∀ φ : TestOn V,
          restrictTo V (h ω - hz ω) φ = ∫ x, H ω x * φ x) := by
  let G : Ω → DistC := fun ω => h ω - hz ω
  have hG : Measurable G := measurable_distOn_iff.2 fun φ =>
    ((measurable_distOn_apply φ).comp hh.measurable).sub
      ((measurable_distOn_apply φ).comp hzm)
  refine ⟨fun ω x => SupercriticalConformalCovariance.ZBConformal.canonicalHarmExt V (G ω) x,
    (SupercriticalConformalCovariance.ZBConformal.measurable_canonicalHarmExt V).comp
      (Measurable.prodMk (hG.comp measurable_fst) measurable_snd), ?_⟩
  filter_upwards [ae_harmonic_sub_of_version hh hV hzae] with ω ⟨g, hg, hp⟩
  refine ⟨SupercriticalConformalCovariance.ZBConformal.canonicalHarmExt_harmonic V hg hp, fun φ => ?_⟩
  exact SupercriticalConformalCovariance.ZBConformal.canonicalHarmExt_pair V hg hp φ

end SupercriticalConformalCovariance.Markov
