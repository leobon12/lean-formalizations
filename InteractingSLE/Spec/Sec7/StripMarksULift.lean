/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BRLeafLift
import InteractingSLE.Spec.Sec7.Lemma725Det

/-!
# Lemma 7.25's determination reference in every universe

Packet PROVE-STRIPMARKS. The frozen Theorem 1.2 lives in an arbitrary universe `u` and its wiring asks for Lemma 7.25's
determination reference `Aux50Hit.Lemma725DetReferenceStatement.{u}` (one coupling of the two-seed word whose killed
driving history is a Borel function of the field). The strip system and the pocket-word objects of Theorem 1.2's
wiring live in `Type`. A reference in `Type` gives one in every universe: read the coupling through the first factor of
`Ω × ULift PUnit` (`Theorem14.BRLeaf.isOptionalHullCoupling_fstU`, PROVE-T14-BR); the field determination is an almost
sure statement about the first factor.

* **`lemma725DetReferenceStatement_ulift`**: `Lemma725DetReferenceStatement.{v} → Lemma725DetReferenceStatement.{max
    v w}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

universe v w

namespace InteractingSLE.Sec7.StripMarks

/-- **A determination reference lifts to every larger universe** (the coupling read through the first factor of
`Ω × ULift PUnit`, whose law is the image of `P` under `ω ↦ (ω, ⋆)`). -/
theorem lemma725DetReferenceStatement_ulift (h : Aux50Hit.Lemma725DetReferenceStatement.{v}) :
    Aux50Hit.Lemma725DetReferenceStatement.{max v w} := by
  intro κ hκ rL rR hL hLd hR hRd
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hf, hC, Ψ, hΨ, hdet⟩ := h κ hκ rL rR hL hLd hR hRd
  let ι : Ω → Ω × ULift.{w} PUnit.{1} := fun ω => (ω, ULift.up PUnit.unit)
  have hι : Measurable ι := measurable_id.prodMk measurable_const
  let μ : Measure (Ω × ULift.{w} PUnit.{1}) := P.map ι
  have hμP : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hι.aemeasurable).2 hP
  have hμ : μ.map Prod.fst = P := by
    rw [Measure.map_map measurable_fst hι]
    exact Measure.map_id
  refine ⟨Ω × ULift.{w} PUnit.{1}, inferInstance, μ, hμP, Coupling.filtrationFst 𝓕 (ULift.{w} PUnit.{1}),
    fun t p => W t p.1, fun i t p => VL i t p.1, fun j t p => VR j t p.1, fun t p => B t p.1, fun p => ζ p.1,
    fun p => hf p.1, Theorem14.BRLeaf.isOptionalHullCoupling_fstU hμ hC, Ψ, hΨ, ?_⟩
  have hdet' : ∀ᵐ ω ∂(μ.map Prod.fst), (Ψ (hf ω)).1 = ζ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
      (Ψ (hf ω)).2.1 t = W t ω ∧ (∀ i, (Ψ (hf ω)).2.2.1 i t = VL i t ω) ∧
        ∀ i, (Ψ (hf ω)).2.2.2 i t = VR i t ω := by
    rw [hμ]
    exact hdet
  exact ae_of_ae_map measurable_fst.aemeasurable hdet'

end InteractingSLE.Sec7.StripMarks
