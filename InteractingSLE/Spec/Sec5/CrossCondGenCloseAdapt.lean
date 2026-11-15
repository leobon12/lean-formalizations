/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondGenCloseForce
import InteractingSLE.Spec.Sec7.PocketPhaseMeans
import InteractingSLE.Spec.Sec7.Aux122DisintEvol

/-!
# Adapted geometric marks before a finite image lifetime

PROVE-CROSSCOND-GEN. The geometric force coordinates are constructed from the
driver and the initial marks. Their adaptedness is inherited from the existing
killed-driver theorem, including paths that have already hit the real boundary.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.Gen

open Ito MartChar Sec7.PocketTraversal Sec7.PocketPhaseMeans Sec7.Aux122Disint
open Sec7.Lemma71D

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {T : Ω → WithTop ℝ≥0} {n : ℕ}

/-- The killed geometric right marks are strongly adapted. No separation from
the driver is needed for this measurable construction. -/
theorem stronglyAdapted_imageGeomR
    (hc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω})
    (hWa : AdaptedBefore 𝓖 (fun ω => (T ω : ℝ≥0∞)) W)
    {x : Ω → Fin n → ℝ} (hx : Measurable[𝓖 0] x) (i : Fin n) :
    StronglyAdapted 𝓖 (imageGeomR W T x i) := by
  intro t
  have ha := adaptedBefore_geomRW (T := fun ω => (T ω : ℝ≥0∞)) hc hWa hx i
  exact (measurable_killAt_of_adaptedBefore ha t).stronglyMeasurable

/-- The reflected killed geometric left marks are strongly adapted. -/
theorem stronglyAdapted_imageGeomL
    (hc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω})
    (hWa : AdaptedBefore 𝓖 (fun ω => (T ω : ℝ≥0∞)) W)
    {x : Ω → Fin n → ℝ} (hx : Measurable[𝓖 0] x) (i : Fin n) :
    StronglyAdapted 𝓖 (imageGeomL W T x i) := by
  intro t
  have ha := adaptedBefore_geomLW (T := fun ω => (T ω : ℝ≥0∞)) hc hWa hx i
  exact (measurable_killAt_of_adaptedBefore ha t).stronglyMeasurable

/-- Assemble the image filtration data with the actual geometric force marks.
The remaining inputs concern the image driver, lifetime and initial chart;
force-coordinate construction and contact-word properties are proved here. -/
theorem imageWordFiltrationHypothesis_of_geometric
    {P : Measure Ω} {𝓐 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    {σ : ℕ → Ω → ℝ≥0} {c : Ω → Chart}
    (hc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω})
    (hW0 : ∀ ω, W 0 ω = 0)
    (hL : ∀ ω, Antitone (xL ω)) (hR : ∀ ω, Monotone (xR ω))
    (hxL : Measurable[usualAugmentation 𝓐 P 0] xL)
    (hxR : Measurable[usualAugmentation 𝓐 P 0] xR)
    (hWa : StronglyAdapted (usualAugmentation 𝓐 P) W)
    (hT : ∀ t : ℝ≥0, MeasurableSet[usualAugmentation 𝓐 P t]
      {ω | (T ω : ℝ≥0∞) ≤ t})
    (hσ : Coupling.IsAnnouncingSeq (usualAugmentation 𝓐 P) P
      (fun ω => (T ω : ℝ≥0∞)) σ)
    (hconf : ∀ ω, (c ω).IsConformal)
    (hlift : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hdom : ∀ z, MeasurableSet[usualAugmentation 𝓐 P 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[usualAugmentation 𝓐 P 0]
      ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[usualAugmentation 𝓐 P 0]
      ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) :
    ImageWordFiltrationHypothesis P 𝓐 W (imageGeomL W T xL) (imageGeomR W T xR) T σ c := by
  have hWa' := adaptedBefore_of_stronglyAdapted hT hWa
  exact ⟨isContactWord_imageGeom hc hW0 hL hR, hWa,
    fun i => stronglyAdapted_imageGeomL hc hWa' hxL i,
    fun j => stronglyAdapted_imageGeomR hc hWa' hxR j,
    hT, hσ, hconf, hlift, hdom, hfwd, hliftm⟩

end InteractingSLE.Sec5.CrossCond.Gen
