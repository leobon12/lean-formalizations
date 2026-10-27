import MatedCRTHarmonic.GMS4c.Defs
import MatedCRTHarmonic.GMSAppA.LemmaA1A2

/-!
# The local data of [18] Lemma 4.3

For an open set `V`, this module records the restricted LQG area measure, the restricted field,
and the Lebesgue-parametrized SLE excursion segments at rational points. The measure space is
Mathlib's Giry measurable space on `Measure ℂ`; the field and segment factors carry their
existing product measurable spaces. The excursion coordinate is zero outside `V`, since the
frozen S7 locality clause only specifies segments at rational points inside `V`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open LQGMetric LQGMetric.Blueprint

namespace MatedCRTHarmonic.GMS4c

attribute [local instance] Classical.propDecidable

/-- The source local configuration `(μ_h|_V, h|_V, η_L` excursions`) of [18] Lemma 4.3.
The product measurable space uses Giry evaluation for the measure component, the Borel space
of distributions on `V`, and the product space of rationally indexed curves. -/
abbrev LocalConfiguration (V : TopologicalSpace.Opens ℂ) : Type :=
  (Measure ℂ × DistOn V) × (ℚ × ℚ → ℝ → ℂ)

/-- The measure restriction, as a map between Giry measurable spaces. -/
theorem measurable_measureRestrict (V : TopologicalSpace.Opens ℂ) :
    Measurable fun μ : Measure ℂ => μ.restrict V := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [Measure.restrict_apply hs]
  exact Measure.measurable_coe (hs.inter V.isOpen.measurableSet)

/-- The local configuration map from a measure, field and continuous space-filling curve. -/
def localConfiguration (V : TopologicalSpace.Opens ℂ) (μ : Measure ℂ) (h : DistC)
    (ηL : C(ℝ, ℂ)) : LocalConfiguration V :=
  ((μ.restrict V, restrictTo V h),
    fun q => if ratPt q ∈ V then MatedCRT.excursionSegment ηL V (ratPt q) else 0)

/-- The same map with excursion segments supplied by a measurable locality witness (S7). -/
def localConfigurationFromSegments (V : TopologicalSpace.Opens ℂ) (μ : Measure ℂ)
    (h : DistC) (segments : ℚ × ℚ → ℝ → ℂ) : LocalConfiguration V :=
  ((μ.restrict V, restrictTo V h), fun q => if ratPt q ∈ V then segments q else 0)

/-- The S7 segment witness identifies the actual local configuration at every sample where
its rational-point equality holds. -/
theorem localConfiguration_eq_fromSegments (V : TopologicalSpace.Opens ℂ)
    (μ : Measure ℂ) (h : DistC) (ηL : C(ℝ, ℂ)) (segments : ℚ × ℚ → ℝ → ℂ)
    (hseg : ∀ q, ratPt q ∈ V → MatedCRT.excursionSegment ηL V (ratPt q) = segments q) :
    localConfiguration V μ h ηL = localConfigurationFromSegments V μ h segments := by
  unfold localConfiguration localConfigurationFromSegments
  congr 1
  funext q
  split_ifs with hq
  · exact hseg q hq
  · rfl

/-- A measurable S7 excursion witness and measurable area/field laws give a measurable local
configuration. This isolates the measurable-space part of [18] Lemma 4.3. -/
theorem measurable_localConfigurationFromSegments {Ω : Type*} [MeasurableSpace Ω]
    (V : TopologicalSpace.Opens ℂ) {μ : Ω → Measure ℂ} {h : Ω → DistC}
    {segments : Ω → ℚ × ℚ → ℝ → ℂ} (hμ : Measurable μ) (hh : Measurable h)
    (hseg : Measurable segments) :
    Measurable fun ω => localConfigurationFromSegments V (μ ω) (h ω) (segments ω) := by
  refine ((measurable_measureRestrict V).comp hμ |>.prodMk
    ((measurable_restrictTo V).comp hh)).prodMk ?_
  refine measurable_pi_iff.mpr fun q => ?_
  by_cases hq : ratPt q ∈ V
  · simpa only [localConfigurationFromSegments, hq, ↓reduceIte, Function.comp_def] using
      (measurable_pi_apply q).comp hseg
  · simp only [hq, ↓reduceIte]
    exact measurable_const

/-- The frozen S7 locality witness identifies the corrected local configuration almost
surely. Its measure and field coordinates agree by construction. -/
theorem ae_localConfiguration_eq_fromSegments {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (V : TopologicalSpace.Opens ℂ)
    (μ : Ω → Measure ℂ) (h : Ω → DistC) (ηL : Ω → C(ℝ, ℂ))
    (segments : Ω → ℚ × ℚ → ℝ → ℂ)
    (hS7 : ∀ᵐ ω ∂P, ∀ q, ratPt q ∈ V →
      MatedCRT.excursionSegment (ηL ω) V (ratPt q) = segments ω q) :
    (fun ω => localConfiguration V (μ ω) (h ω) (ηL ω)) =ᵐ[P]
      fun ω => localConfigurationFromSegments V (μ ω) (h ω) (segments ω) := by
  filter_upwards [hS7] with ω hω
  exact localConfiguration_eq_fromSegments V (μ ω) (h ω) (ηL ω) (segments ω) hω

end MatedCRTHarmonic.GMS4c
