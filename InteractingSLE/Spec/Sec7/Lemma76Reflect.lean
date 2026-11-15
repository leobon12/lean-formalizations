/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.FlowReflectFlow
import InteractingSLE.Spec.Sec7.Lemma77Barrier

/-!
# Lemma 7.6: the swapped half by reflection

Packet PROVE-LEMMA76C (specification p. 270, end of the proof of Lemma 7.6: "Reflection and exchange of the path
labels gives its corresponding opposite-side form"). The named input `Lemma76Statement` (`Lemma77Barrier.lean`) has
two conjuncts: the second path does not first exit through the right side of the first prefix, and the first path does
not first exit through the left side of the second prefix. Under `R(z) = −z̄` the two flow lines, exchanged, are again
two flow lines (`IsFlowLine.reflect`: seeds `−x₂ < −x₁`, angles `−θ₂ < −θ₁ + π`), and the pathwise barrier is
`R`-invariant (`firstExitBarrier_reflect`), so the second conjunct is the first one for the reflected configuration.

* `isBounded_connectedComponentIn_image_reflectC`, `mem_unboundedPart_image_reflectC`,
  `mem_jordanIn_image_reflectC`: the topological notions of `IsForbiddenExit` are `R`-invariant;
* `image_lowerArc_reflectC`: `R(lowerArc x₂ x₁) = lowerArc (−x₁) (−x₂)`;
* `isForbiddenExit_reflect`, **`firstExitBarrier_reflect`**;
* `Lemma76RightStatement`: the first conjunct of `Lemma76Statement` alone (a named input, not proved here);
* **`lemma76Statement_of_right`**: `Lemma76RightStatement → Lemma76Statement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric Bornology
open scoped NNReal ENNReal ComplexConjugate

open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Sec7

namespace FlowReflect

open LP (reflectC)

/-! ### Invariance of the topological notions -/

theorem image_reflectC_compl (S : Set ℂ) : reflectC '' Sᶜ = (reflectC '' S)ᶜ :=
  (LP.reflectHomeo.toEquiv.image_compl S)

theorem isBounded_connectedComponentIn_image_reflectC (U : Set ℂ) (z : ℂ) :
    IsBounded (connectedComponentIn (reflectC '' U) (reflectC z)) ↔ IsBounded (connectedComponentIn U z) := by
  by_cases hz : z ∈ U
  · have h := LP.reflectHomeo.image_connectedComponentIn hz
    rw [LP.coe_reflectHomeo] at h
    rw [← h, LP.isBounded_reflectC_image_iff]
  · have hz' : reflectC z ∉ reflectC '' U := fun ⟨w, hw, e⟩ => hz (LP.reflectC_injective e ▸ hw)
    rw [connectedComponentIn_eq_empty hz, connectedComponentIn_eq_empty hz']

theorem mem_image_reflectC_iff {S : Set ℂ} {z : ℂ} : reflectC z ∈ reflectC '' S ↔ z ∈ S :=
  LP.reflectC_injective.mem_set_image

theorem mem_unboundedPart_image_reflectC {U : Set ℂ} {z : ℂ} :
    reflectC z ∈ unboundedPart (reflectC '' U) ↔ z ∈ unboundedPart U := by
  simp only [unboundedPart, mem_ofPred_eq, mem_image_reflectC_iff, isBounded_connectedComponentIn_image_reflectC]

theorem mem_jordanIn_image_reflectC {Γ : Set ℂ} {z : ℂ} :
    reflectC z ∈ WangWu.jordanIn (reflectC '' Γ) ↔ z ∈ WangWu.jordanIn Γ := by
  simp only [WangWu.jordanIn, mem_ofPred_eq, mem_image_reflectC_iff, ← image_reflectC_compl,
    isBounded_connectedComponentIn_image_reflectC]

theorem image_comp_reflectC (γ : ℝ≥0 → ℂ) (I : Set ℝ≥0) :
    (fun t => reflectC (γ t)) '' I = reflectC '' (γ '' I) := (image_image reflectC γ I).symm

theorem H_diff_union_reflectC (A B : Set ℂ) :
    H \ (reflectC '' A ∪ reflectC '' B) = reflectC '' (H \ (A ∪ B)) := by
  rw [← image_union, LP.H_diff_reflectC_image]

/-! ### The closing arc -/

theorem reflectC_segPath (a b : ℂ) (t : ℝ) :
    reflectC (Sec6.segPath a b t) = Sec6.segPath (reflectC a) (reflectC b) t := by
  simp only [Sec6.segPath, LP.reflectC, map_add, map_mul, map_sub, Complex.conj_ofReal]
  ring

theorem image_segPath_symm (a b : ℂ) : Sec6.segPath a b '' Icc 0 1 = Sec6.segPath b a '' Icc 0 1 := by
  have key : ∀ a b : ℂ, Sec6.segPath a b '' Icc 0 1 ⊆ Sec6.segPath b a '' Icc 0 1 := by
    rintro a b _ ⟨t, ht, rfl⟩
    refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    simp only [Sec6.segPath]
    push_cast
    ring
  exact (key a b).antisymm (key b a)

theorem image_reflectC_segPath (a b : ℂ) :
    reflectC '' (Sec6.segPath a b '' Icc 0 1) = Sec6.segPath (reflectC a) (reflectC b) '' Icc 0 1 := by
  rw [image_image]
  simp only [reflectC_segPath]

/-- **The closing arc under `R`**: `R(lowerArc x₂ x₁) = lowerArc (−x₁) (−x₂)`. -/
theorem image_lowerArc_reflectC (x₂ x₁ : ℝ) : reflectC '' lowerArc x₂ x₁ = lowerArc (-x₁) (-x₂) := by
  have h1 : reflectC (x₁ : ℂ) = ((-x₁ : ℝ) : ℂ) := reflectC_ofReal x₁
  have h2 : reflectC (x₂ : ℂ) = ((-x₂ : ℝ) : ℂ) := reflectC_ofReal x₂
  have h3 : reflectC ((((x₁ + x₂) / 2 : ℝ) : ℂ) - Complex.I) = (((-x₂ + -x₁) / 2 : ℝ) : ℂ) - Complex.I := by
    apply Complex.ext <;>
      simp only [LP.reflectC, Complex.neg_re, Complex.conj_re, Complex.sub_re, Complex.ofReal_re, Complex.I_re,
        Complex.neg_im, Complex.conj_im, Complex.sub_im, Complex.ofReal_im, Complex.I_im] <;> ring
  rw [image_lowerArcPath, image_lowerArcPath, image_union, image_reflectC_segPath, image_reflectC_segPath, h1, h2, h3]
  refine (union_comm _ _).trans ?_
  congr 1 <;> exact image_segPath_symm _ _

/-! ### The barrier -/

theorem isForbiddenExit_reflect {α β : ℝ≥0 → ℂ} {a b e u v : ℝ≥0} {L : Set ℂ} :
    IsForbiddenExit (fun t => reflectC (α t)) a (fun t => reflectC (β t)) b e u v (reflectC '' L) ↔
      IsForbiddenExit α a β b e u v L := by
  unfold IsForbiddenExit
  simp only [image_comp_reflectC, ← image_union, LP.H_diff_reflectC_image, mem_unboundedPart_image_reflectC,
    LP.reflectC_injective.eq_iff, mem_jordanIn_image_reflectC]

/-- **The pathwise barrier of Lemma 7.6 is `R`-invariant.** -/
theorem firstExitBarrier_reflect {α β : ℝ≥0 → ℂ} {a b : ℝ≥0} {ζβ : ℝ≥0∞} {L : Set ℂ} :
    FirstExitBarrier (fun t => reflectC (α t)) a (fun t => reflectC (β t)) ζβ b (reflectC '' L) ↔
      FirstExitBarrier α a β ζβ b L := by
  unfold FirstExitBarrier
  simp only [image_comp_reflectC, Set.disjoint_image_iff LP.reflectC_injective, LP.H_diff_reflectC_image,
    mem_unboundedPart_image_reflectC, isForbiddenExit_reflect]

end FlowReflect

/-! ### Lemma 7.6 from its first half -/

/-- **Named input: the first half of Lemma 7.6** (§7.2, p. 267), the first conjunct of `Lemma76Statement`: for
`x₂ < x₁`, `θ₁ < θ₂ + π`, at the deterministic stops `r ∧ ζ₁`, `t ∧ ζ₂`, the second path does not first exit the
joint unbounded component through the right side of the first prefix. Not proved in Lean; with
`lemma76Statement_of_right` it gives the whole of `Lemma76Statement` (the swapped half by reflection). -/
def Lemma76RightStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ r t : ℝ≥0, ∀ᵐ ω ∂P,
        FirstExitBarrier (η₁ ω) (truncAt (ζ₁ ω) r) (η₂ ω) (ζ₂ ω) (truncAt (ζ₂ ω) t) (lowerArc x₂ x₁)

/-- **Lemma 7.6 from its first half**: the swapped half ("the first path does not first exit through the left side of
the second prefix") is the first half for the reflected configuration `(R ∘ η₂, R ∘ η₁)` of the reflected field
`−h ∘ R` (specification p. 270: "Reflection and exchange of the path labels gives its corresponding opposite-side
form"). -/
theorem lemma76Statement_of_right (hR : Lemma76RightStatement.{u}) : Lemma76Statement.{u} := by
  intro κ hκ hκ4 b J hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ r t
  have hA := hR κ hκ hκ4 b J hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ r t
  have hB := hR κ hκ hκ4 (FlowReflect.reflData b) (FlowReflect.reflJumps J)
    (FlowReflect.isPiecewiseConstantBoundaryData_reflData hb) (-x₂) (-x₁) (-θ₂) (-θ₁) (by linarith)
    (by linarith) P (fun ω => FlowReflect.reflField (h ω)) (FlowReflect.IsGFFWithBoundaryData.reflect hh)
    (fun ω s => LP.reflectC (η₂ ω s)) (fun ω s => LP.reflectC (η₁ ω s)) ζ₂ ζ₁
    (FlowReflect.IsFlowLine.reflect hb hη₂) (FlowReflect.IsFlowLine.reflect hb hη₁) t r
  filter_upwards [hA, hB] with ω h1 h2
  refine ⟨h1, ?_⟩
  rw [← FlowReflect.image_lowerArc_reflectC, FlowReflect.firstExitBarrier_reflect] at h2
  exact h2

end Sec7

end InteractingSLE
