/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkRetarget
import InteractingSLE.Spec.Sec5.Aux65NegReference
import InteractingSLE.Spec.Zhan.TargetChangeProcessWord

/-!
# A conditional first-mark target-change route for negative-side R5

`FirstMarkRetargetUpToStatement` is an unproved stochastic transport input.
It asks for the canonical retargeted processes of the landed target-change API,
at the first mark, for an announced local evolution. It includes the finite
target-separation endpoint needed by this packet. Theorems in this file are
explicitly conditional on that input; `TwoMarkLowUpToStatement` and R5 are
not asserted unconditionally.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
universe u

namespace InteractingSLE.Sec5.TwoMark

open Zhan.Retarget

/-- **Unproved input:** first-mark target change at an announced local stop,
including transport of an interval visit at the target-separation endpoint.
The driver and force coordinates are the canonical `newW`, `newVL`, `newVR`,
not arbitrary processes with a convenient law. The horizon may be chosen as
a measurable version, and may be zero on a null exceptional set. -/
def FirstMarkRetargetUpToStatement : Prop :=
  ∀ (κ a b r : ℝ), 0 < κ → κ < 4 → 0 < a → a < b → r ≤ κ / 2 - 4 →
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (W B : ℝ≥0 → Ω → ℝ)
    (xL ρL : Fin 0 → ℝ) (VL : Fin 0 → ℝ≥0 → Ω → ℝ)
    (VR : Fin 2 → ℝ≥0 → Ω → ℝ) (e : Ω → ℝ≥0∞),
    Sec2.IsSLEEvolutionUpTo κ xL ![a, b] ρL ![r, -r] P 𝓕 W VL VR B e →
    (∀ ω, Continuous (W · ω)) → (∀ i ω, Continuous (VR i · ω)) →
    ∀ (T : ℕ → Ω → ℝ≥0), Coupling.IsAnnouncingSeq 𝓕 P e T →
    ∀ η : Ω → ℝ≥0 → ℂ,
      (∀ᵐ ω ∂P, IsGeneratingTrace (W · ω) (e ω) (η ω)) →
      (∀ᵐ ω ∂P, InjOn (η ω) {t | (t : ℝ≥0∞) ≤ e ω}) →
      let W' : ℝ≥0 → Ω × Ω → ℝ := fun s p =>
        newW (j := 0) (m := 1) ![a, b] (W · p.1) (fun i t => VR i t p.1) s
      let VL' : Fin 2 → ℝ≥0 → Ω × Ω → ℝ := fun i s p =>
        newVL (j := 0) (m := 1) ![a, b] (W · p.1)
          (fun i t => VL i t p.1) (fun i t => VR i t p.1) i s
      let VR' : Fin 0 → ℝ≥0 → Ω × Ω → ℝ := fun i s p =>
        newVR (j := 0) (m := 1) ![a, b] (W · p.1) (fun i t => VR i t p.1) i s
      ∃ (𝓘 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω)))
        (β : ℝ≥0 → Ω × Ω → ℝ) (τ : Ω × Ω → ℝ≥0∞)
        (S : ℕ → Ω × Ω → ℝ≥0) (Γ : Ω × Ω → ℝ≥0 → ℂ),
        Sec2.IsSLEEvolutionUpTo κ ![-1, Sec7.targetChangeReal a b] xL
          ![κ - 6, -r] ρL (P.prod P) 𝓘 W' VL' VR' β τ ∧
        (∀ p, ContinuousOn (W' · p) {s | (s : ℝ≥0∞) < τ p}) ∧
        (∀ i p, ContinuousOn (VL' i · p) {s | (s : ℝ≥0∞) < τ p}) ∧
        Coupling.IsAnnouncingSeq 𝓘 (P.prod P) τ S ∧
        (∀ᵐ p ∂(P.prod P), IsGeneratingTrace (W' · p) (τ p) (Γ p)) ∧
        (∀ᵐ p ∂(P.prod P), InjOn (Γ p) {s | (s : ℝ≥0∞) ≤ τ p}) ∧
        (∀ᵐ p ∂(P.prod P), ∀ s : ℝ≥0, (s : ℝ≥0∞) = τ p →
          ContinuousOn (fun t => (W' t p, fun i => VL' i t p, fun j => VR' j t p)) (Iic s)) ∧
        ∀ᵐ p ∂(P.prod P), ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e p.1 →
          ∀ y ∈ Ioo a b, η p.1 t = (y : ℂ) →
            ∃ s : ℝ≥0, (s : ℝ≥0∞) ≤ τ p ∧ Γ p s = Sec7.targetChange a (η p.1 t)

/-- **Conditional:** the stopped two-mark exclusion follows from the canonical
first-mark transport, by the proved stopped left-ray barrier. -/
theorem twoMarkLowUpToStatement_of_firstMarkRetargetUpTo
    (hR : FirstMarkRetargetUpToStatement.{u}) : Aux65Neg.TwoMarkLowUpToStatement.{u} := by
  intro κ a b r hκ hκ4 ha hab hr Ω mΩ P hP 𝓕 W B xL ρL VL VR e hE hW hVR T hT η hη hinj
  obtain ⟨𝓘, β, τ, S, Γ, hE', hW', hVL', hS, hΓ, hinj', hc, htrans⟩ :=
    hR κ a b r hκ hκ4 ha hab hr P 𝓕 W B xL ρL VL VR e hE hW hVR T hT η hη hinj
  have hav := ae_avoid_left_ray hκ hκ4.le ha hab hr hE' hW' hVL' hS hΓ hinj' hc
  apply Restart.ConverseBefore.ae_of_ae_fst (P₀ := P)
  filter_upwards [hav, htrans] with p hp hpt t ht y hy he
  obtain ⟨s, hs, he'⟩ := hpt t ht y hy he
  apply hp s hs (Sec7.targetChangeReal a y) (targetChangeReal_lt_of_mem ha hy)
  rw [he', he, Sec7.targetChange_ofReal]

/-- **Conditional:** the first-mark transport supplies precisely the two-mark
input of the landed negative-reference adapter. -/
theorem r5NegStatement_of_firstMarkRetargetUpTo (hR : FirstMarkRetargetUpToStatement.{u}) :
    Aux61Cov.R5NegStatement.{u} :=
  Aux65Neg.r5NegStatement_of_twoMarkLowUpTo
    (twoMarkLowUpToStatement_of_firstMarkRetargetUpTo hR)

end InteractingSLE.Sec5.TwoMark
