import HigherDimLQGMetric.Markov.Gauss
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable

/-!
# Measurable versions of projected interior Gaussian variables

The `Lp` subspace of random variables measurable for `σ(h|_V)` is closed. Thus every orthogonal
projection onto the closed span of interior LGF pairings has a version measurable for that sigma
algebra. This is the measurable part of the D-M projection construction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped RealInnerProductSpace

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistRd d}

omit [IsProbabilityMeasure P] in
/-- The interior restriction sigma algebra is contained in the sample-space sigma algebra. -/
theorem markov_fieldSigmaRd_le (hh : IsWholeSpaceLGF h P) (V : Opens (Rd d))
    {ρ : TestRd d} (hρ : ∫ x, ρ x = 1) :
    fieldSigmaRd (fun ω => recenter ρ (h ω)) V ≤ (inferInstance : MeasurableSpace Ω) := by
  have hr : Measurable (fun ω => recenter ρ (h ω)) :=
    ((measurable_recenter_sigma0 hρ).mono sigma0_le le_rfl).comp hh.measurable
  exact ((measurable_restrictTo V).comp hr).comap_le

omit [IsProbabilityMeasure P] in
/-- An interior `L²` generator has a version measurable from the restricted recentered field. -/
theorem markov_insideVec_aestronglyMeasurable (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) {ρ : TestRd d} (hρ : ∫ x, ρ x = 1) (φ : TestOn V) :
    AEStronglyMeasurable[fieldSigmaRd (fun ω => recenter ρ (h ω)) V]
      (markovInsideVec hh V hρ φ : Ω → ℝ) P := by
  have hm : Measurable[fieldSigmaRd (fun ω => recenter ρ (h ω)) V]
      (fun ω => restrictTo V (recenter ρ (h ω)) φ) :=
    (measurable_distOn_apply φ).comp (comap_measurable _)
  have hae : (markovInsideVec hh V hρ φ : Ω → ℝ) =ᵐ[P]
      (fun ω => restrictTo V (recenter ρ (h ω)) φ) := by
    filter_upwards [(markov_memLp_pair hh (markovInsideTest V hρ φ)).coeFn_toLp]
      with ω hω
    change ((markov_memLp_pair hh (markovInsideTest V hρ φ)).toLp
      (markovPair h (markovInsideTest V hρ φ)) : Ω → ℝ) ω = _
    rw [hω, restrictTo_apply, recenter_apply]
    rfl
  exact hm.aestronglyMeasurable.congr hae.symm

omit [IsProbabilityMeasure P] in
/-- Closedness of measurable `L²` random variables puts the entire interior Gaussian space
inside that measurable subspace. -/
theorem markov_insideSpace_le_lpMeas (hh : IsWholeSpaceLGF h P) (V : Opens (Rd d))
    {ρ : TestRd d} (hρ : ∫ x, ρ x = 1) :
    markovInsideSpace hh V hρ ≤
      lpMeas ℝ ℝ (fieldSigmaRd (fun ω => recenter ρ (h ω)) V) 2 P := by
  unfold markovInsideSpace
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro u ⟨φ, rfl⟩
    exact mem_lpMeas_iff_aestronglyMeasurable.mpr
      (markov_insideVec_aestronglyMeasurable hh V hρ φ)
  · change IsClosed {f : Lp ℝ 2 P |
      AEStronglyMeasurable[fieldSigmaRd (fun ω => recenter ρ (h ω)) V] f P}
    exact isClosed_aestronglyMeasurable (markov_fieldSigmaRd_le hh V hρ)

omit [IsProbabilityMeasure P] in
/-- Every projected exterior pairing has a measurable interior version. -/
theorem markov_projection_aestronglyMeasurable (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) {ρ : TestRd d} (hρ : ∫ x, ρ x = 1)
    (ψ : TestOn (extOpen V)) :
    AEStronglyMeasurable[fieldSigmaRd (fun ω => recenter ρ (h ω)) V]
      ((markovInsideSpace hh V hρ).starProjection
        (markovOutsideVec hh (extOpen V) hρ ψ) : Ω → ℝ) P := by
  exact mem_lpMeas_iff_aestronglyMeasurable.mp
    (markov_insideSpace_le_lpMeas hh V hρ
      ((markovInsideSpace hh V hρ).starProjection_apply_mem _))

end HigherDimLQGMetric
