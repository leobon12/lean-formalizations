/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma77Close
import InteractingSLE.Spec.Supplement.S10Main
import InteractingSLE.Spec.Sec4.Aux25Term

/-!
# Lemma 7.7 from Lemma 7.6 and Aux. lemma 70

Packet PROVE-LEMMA77 (specification §7.2, Lemma 7.7, p. 282, `source/spec/p241-288.md#lem-7.7`).

The pathwise Lemma 7.7 (`Supp10.Lemma77Statement`: common first point and confinement, `Tᵢ = ζᵢ`) follows the
source's proof:

* *A common first contact*: at each integer truncation, Aux. lemma 70 (`Aux70Statement`) excludes a reverse common
  arc and Aux. lemma 72 excludes two adjacent minimal contacts with distinct points; Aux. lemma 68 (landed) then gives
  one least contact (`Sec7.exists_isFirstContact_of_truncations`). Aux. lemma 72 is **proved here** from Lemma 7.6
  (`Lemma76Statement`) at every lens whose arrival corners are points of `ℍ` (`Lemma77Lens.lean`).
* *Confinement*: Aux. lemmas 73–75 with Lemma 7.6, **proved here** at every common first contact in `ℍ`
  (`Lemma77Conf.lean`, `Lemma77Close.lean`).
* Aux. lemma 25 (simplicity) is the landed `Theorem15.aux25Statement`.

The cases where the relevant corner is a real point (the "physical real junction" cases of Aux. lemmas 71–72 and 74,
"interpreted through its incident prime end") are not proved; each is isolated as one deterministic proposition,
`RealCornerLensExclusion` and `RealContactConfinement` (pure planar statements about two good paths satisfying the
pathwise Lemma 7.6 at all rational stops). `lemma77Statement_of_lemma76` is the resulting conditional helper.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Sec7

open Restart

/-! ### The real-corner cases (deterministic propositions, not proved) -/

/-- **Aux. lemma 72 at a lens with a real corner** (pathwise): two good paths from `x₁ > x₂` satisfying Lemma 7.6's
conclusion at every pair of rational stops (both halves) have no two adjacent minimal contacts `(a, b)`, `(c, d)`,
`a < c`, at a truncation, one of whose corners `α(a)`, `α(c)` is real. The interior case is
`false_of_adjacent_minimalContacts_of_mem_H`. -/
def RealCornerLensExclusion : Prop :=
  ∀ (α β : ℝ≥0 → ℂ) (ζ₁ ζ₂ : ℝ≥0∞) (x₁ x₂ : ℝ), IsPathGood α ζ₁ x₁ → IsPathGood β ζ₂ x₂ → x₂ < x₁ →
    ∀ A B : ℝ≥0, (A : ℝ≥0∞) ≤ ζ₁ → (B : ℝ≥0∞) ≤ ζ₂ →
    ∀ a b c d : ℝ≥0, (a, b) ∈ Sec7.minimalContacts α A β B → (c, d) ∈ Sec7.minimalContacts α A β B → a < c →
      (∀ p ∈ Sec7.minimalContacts α A β B, p.1 ∉ Ioo a c) → (α a ∉ H ∨ α c ∉ H) →
      (∀ q q' : ℚ, FirstExitBarrier α (truncAt ζ₁ (q : ℝ).toNNReal) β ζ₂ (truncAt ζ₂ (q' : ℝ).toNNReal)
        (lowerArc x₂ x₁)) →
      (∀ q q' : ℚ, FirstExitBarrier β (truncAt ζ₂ (q : ℝ).toNNReal) α ζ₁ (truncAt ζ₁ (q' : ℝ).toNNReal)
        (lowerArc x₂ x₁)) → False

/-- **Aux. lemmas 74–75 at a real common first contact** (pathwise): for two good paths from `x₁ > x₂` satisfying
Lemma 7.6's conclusion at every pair of rational stops (both halves), at a common first contact `α(a) = β(b) ∉ ℍ`
both continuations lie in the closure of the active domain. The interior case is `conf_of_barrier_of_mem_H`. -/
def RealContactConfinement : Prop :=
  ∀ (α β : ℝ≥0 → ℂ) (ζ₁ ζ₂ : ℝ≥0∞) (x₁ x₂ : ℝ), IsPathGood α ζ₁ x₁ → IsPathGood β ζ₂ x₂ → x₂ < x₁ →
    ∀ a b : ℝ≥0, IsFirstContact α ζ₁ β ζ₂ a b → α a ∉ H →
      (∀ q q' : ℚ, FirstExitBarrier α (truncAt ζ₁ (q : ℝ).toNNReal) β ζ₂ (truncAt ζ₂ (q' : ℝ).toNNReal)
        (lowerArc x₂ x₁)) →
      (∀ q q' : ℚ, FirstExitBarrier β (truncAt ζ₂ (q : ℝ).toNNReal) α ζ₁ (truncAt ζ₁ (q' : ℝ).toNNReal)
        (lowerArc x₂ x₁)) →
      (∀ s : ℝ≥0, a ≤ s → (s : ℝ≥0∞) ≤ ζ₁ → α s ∈ closure (activeDomain α a β b)) ∧
        ∀ t : ℝ≥0, b ≤ t → (t : ℝ≥0∞) ≤ ζ₂ → β t ∈ closure (activeDomain α a β b)

/-! ### Pathwise assembly -/

/-- **Aux. lemma 72, pathwise**, from Lemma 7.6's conclusion at all rational stops (interior corners) and the
real-corner proposition. -/
theorem noAdjacentMinimalContacts_of_barrier (hRL : RealCornerLensExclusion) {α β : ℝ≥0 → ℂ}
    {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂) (hx : x₂ < x₁)
    {A B : ℝ≥0} (hA : (A : ℝ≥0∞) ≤ ζ₁) (hB : (B : ℝ≥0∞) ≤ ζ₂)
    (hbar₁ : ∀ q q' : ℚ, FirstExitBarrier α (truncAt ζ₁ (q : ℝ).toNNReal) β ζ₂ (truncAt ζ₂ (q' : ℝ).toNNReal)
      (lowerArc x₂ x₁))
    (hbar₂ : ∀ q q' : ℚ, FirstExitBarrier β (truncAt ζ₂ (q : ℝ).toNNReal) α ζ₁ (truncAt ζ₁ (q' : ℝ).toNNReal)
      (lowerArc x₂ x₁)) : NoAdjacentMinimalContacts α A β B := by
  rintro ⟨a, b, c, d, hab, hcd, hac, -, hgap⟩
  by_cases hreal : α a ∉ H ∨ α c ∉ H
  · exact hRL α β ζ₁ ζ₂ x₁ x₂ hp₁ hp₂ hx A B hA hB a b c d hab hcd hac hgap hreal hbar₁ hbar₂
  · push Not at hreal
    exact false_of_adjacent_minimalContacts_of_mem_H hp₁ hp₂ hx hA hB hab hcd hac hgap hreal.1 hreal.2
      hbar₁ hbar₂

/-- **Lemma 7.7's confinement, pathwise**, at every common first contact. -/
theorem conf_of_barrier (hRC : RealContactConfinement) {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ}
    (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂) (hx : x₂ < x₁) {a b : ℝ≥0}
    (hfc : IsFirstContact α ζ₁ β ζ₂ a b)
    (hbar₁ : ∀ q q' : ℚ, FirstExitBarrier α (truncAt ζ₁ (q : ℝ).toNNReal) β ζ₂ (truncAt ζ₂ (q' : ℝ).toNNReal)
      (lowerArc x₂ x₁))
    (hbar₂ : ∀ q q' : ℚ, FirstExitBarrier β (truncAt ζ₂ (q : ℝ).toNNReal) α ζ₁ (truncAt ζ₁ (q' : ℝ).toNNReal)
      (lowerArc x₂ x₁)) :
    (∀ s : ℝ≥0, a ≤ s → (s : ℝ≥0∞) ≤ ζ₁ → α s ∈ closure (activeDomain α a β b)) ∧
      ∀ t : ℝ≥0, b ≤ t → (t : ℝ≥0∞) ≤ ζ₂ → β t ∈ closure (activeDomain α a β b) := by
  by_cases hwH : α a ∈ H
  · exact conf_of_barrier_of_mem_H hp₁ hp₂ hx hfc hwH hbar₁ hbar₂
  · exact hRC α β ζ₁ ζ₂ x₁ x₂ hp₁ hp₂ hx a b hfc hwH hbar₁ hbar₂

/-! ### The almost-sure statements -/

/-- Lemma 7.6 at all rational stops, almost surely (a countable intersection). -/
theorem ae_barrier_of_lemma76 (h76 : Lemma76Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ}
    {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁)
    (hθ : θ₁ < θ₂ + Real.pi) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, (∀ q q' : ℚ, FirstExitBarrier (η₁ ω) (truncAt (ζ₁ ω) (q : ℝ).toNNReal) (η₂ ω) (ζ₂ ω)
        (truncAt (ζ₂ ω) (q' : ℝ).toNNReal) (lowerArc x₂ x₁)) ∧
      ∀ q q' : ℚ, FirstExitBarrier (η₂ ω) (truncAt (ζ₂ ω) (q : ℝ).toNNReal) (η₁ ω) (ζ₁ ω)
        (truncAt (ζ₁ ω) (q' : ℝ).toNNReal) (lowerArc x₂ x₁) := by
  have h := fun q q' : ℚ => h76 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    (q : ℝ).toNNReal (q' : ℝ).toNNReal
  have hall : ∀ᵐ ω ∂P, ∀ q q' : ℚ, _ := ae_all_iff.2 fun q => ae_all_iff.2 fun q' => h q q'
  filter_upwards [hall] with ω hω
  exact ⟨fun q q' => (hω q q').1, fun q q' => (hω q' q).2⟩

/-- **Lemma 7.7** (`Supp10.Lemma77Statement`), from Aux. lemma 70, Lemma 7.6 (both named §7.2 inputs) and the two
real-corner propositions (a conditional helper: the latter are the deterministic gap left by this packet). -/
theorem lemma77Statement_of_lemma76 (h70 : Aux70Statement.{u}) (h76 : Lemma76Statement.{u})
    (hRL : RealCornerLensExclusion) (hRC : RealContactConfinement) : Supp10.Lemma77Statement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  have hg₁ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁
  have hg₂ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂
  have hbar := ae_barrier_of_lemma76 h76 hκ hκ4 hb hx hθ hh hη₁ hη₂
  have h70' := ae_all_iff.2 (h70 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂)
  filter_upwards [hg₁, hg₂, hbar, h70'] with ω hp₁ hp₂ hω h70ω hmeet
  obtain ⟨hbar₁, hbar₂⟩ := hω
  have h72ω : ∀ m : ℕ, NoAdjacentMinimalContacts (η₁ ω) (truncTime (ζ₁ ω) m) (η₂ ω) (truncTime (ζ₂ ω) m) :=
    fun m => noAdjacentMinimalContacts_of_barrier hRL hp₁ hp₂ hx (coe_truncTime_le _ m)
      (coe_truncTime_le _ m) hbar₁ hbar₂
  obtain ⟨s₀, t₀, hfc⟩ := exists_isFirstContact_of_truncations hp₁.continuousOn hp₂.continuousOn hp₁.1 hp₂.1
    h70ω h72ω hmeet
  exact ⟨s₀, t₀, hfc, conf_of_barrier hRC hp₁ hp₂ hx hfc hbar₁ hbar₂⟩

end Sec7

end InteractingSLE
