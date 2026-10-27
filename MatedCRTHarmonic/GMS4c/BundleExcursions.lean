import MatedCRTHarmonic.GMS4c.LocalCircleProcess
import MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling

/-!
# Bundle S7 excursion reconstruction from the restricted IG field

This converts the bundle's S7 circle-process witness to a measurable function
of the IG field restricted to a thickening of the excursion region and its
additive constant. The area-measure and quantum-cell reconstruction of Lemma
4.3 are separate steps.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped NNReal

namespace MatedCRTHarmonic.GMS4c

attribute [local instance] Classical.propDecidable

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The excursion coordinate of the actual coupling factors measurably
through the IG field restricted to a thickening, together with its constant.
The equality is simultaneous for every rational point in the region. -/
theorem ae_bundle_excursions_from_localIG
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ F : (LQGMetric.DistOn
        (⟨thickening δ (V : Set ℂ), isOpen_thickening⟩ : TopologicalSpace.Opens ℂ) × ℝ) →
          (ℚ × ℚ → ℝ → ℂ),
      Measurable F ∧ ∀ᵐ ω ∂P, ∀ q : ℚ × ℚ, ratPt q ∈ V →
        excursionSegment (ηL ω) V (ratPt q) =
          F (LQGMetric.restrictTo
              (⟨thickening δ (V : Set ℂ), isOpen_thickening⟩ : TopologicalSpace.Opens ℂ)
              (hIG₀ ω), U ω) q := by
  obtain ⟨_Φ, _hΦ, _hpos, _hη, hrest⟩ := D.igMap
  obtain ⟨g, hg, hseg⟩ := hrest.2 V V.isOpen hVb δ hδ
  let W : TopologicalSpace.Opens ℂ := ⟨thickening δ (V : Set ℂ), isOpen_thickening⟩
  refine ⟨fun x => g (localIGCircleProcess W x),
    hg.comp (measurable_localIGCircleProcess W), ?_⟩
  filter_upwards [hseg] with ω hω
  intro q hq
  simpa [ratPt, W, localIGCircleProcess_restrictTo] using hω q hq

/-- Assemble the three configuration coordinates when the local area and
field coordinates and the IG excursion reconstruction are given. -/
def reconstructLocalConfiguration
    (V : TopologicalSpace.Opens ℂ)
    {W : TopologicalSpace.Opens ℂ}
    (F : (LQGMetric.DistOn W × ℝ) → (ℚ × ℚ → ℝ → ℂ))
    (x : (Measure ℂ × LQGMetric.DistOn V) × (LQGMetric.DistOn W × ℝ)) :
    LocalConfiguration V :=
  (x.1, fun q => if ratPt q ∈ V then F x.2 q else 0)

theorem measurable_reconstructLocalConfiguration
    (V : TopologicalSpace.Opens ℂ)
    {W : TopologicalSpace.Opens ℂ}
    {F : (LQGMetric.DistOn W × ℝ) → (ℚ × ℚ → ℝ → ℂ)}
    (hF : Measurable F) : Measurable (reconstructLocalConfiguration V F) := by
  refine measurable_fst.prodMk (measurable_pi_iff.mpr fun q => ?_)
  by_cases hq : ratPt q ∈ V
  · simpa [reconstructLocalConfiguration, hq, Function.comp_def] using
      (measurable_pi_apply q).comp (hF.comp measurable_snd)
  · simp [hq]

/-- Exact configuration equality with the restricted area and field
coordinates supplied as data. S7 supplies the IG excursion coordinate. The
remaining Lemma 4.3 step is to reconstruct the area coordinate from the local
field alone. -/
theorem ae_bundle_localConfiguration_from_localAreaIG
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    (δ : ℝ) (hδ : 0 < δ)
    (μ : Ω → Measure ℂ) (h : Ω → LQGMetric.DistC) :
    ∃ F : ((Measure ℂ × LQGMetric.DistOn V) ×
        (LQGMetric.DistOn
          (⟨thickening δ (V : Set ℂ), isOpen_thickening⟩ : TopologicalSpace.Opens ℂ) × ℝ)) →
            LocalConfiguration V,
      Measurable F ∧ ∀ᵐ ω ∂P,
        F (( (μ ω).restrict V, LQGMetric.restrictTo V (h ω)),
            (LQGMetric.restrictTo
              (⟨thickening δ (V : Set ℂ), isOpen_thickening⟩ : TopologicalSpace.Opens ℂ)
              (hIG₀ ω), U ω)) =
          localConfiguration V (μ ω) (h ω) (ηL ω) := by
  obtain ⟨g, hg, hseg⟩ := ae_bundle_excursions_from_localIG D V hVb δ hδ
  refine ⟨reconstructLocalConfiguration V g,
    measurable_reconstructLocalConfiguration V hg, ?_⟩
  filter_upwards [hseg] with ω hω
  unfold reconstructLocalConfiguration localConfiguration
  congr 1
  funext q
  by_cases hq : ratPt q ∈ V
  · simpa [hq] using (hω q hq).symm
  · simp [hq]

end MatedCRTHarmonic.GMS4c
