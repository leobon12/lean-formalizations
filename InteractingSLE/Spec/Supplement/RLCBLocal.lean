/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCBMain
import InteractingSLE.Spec.Supplement.S9DFrame

/-!
# The localized local completion: W5's late cuts

Packet PROVE-RLC-B, the question of `planning/handoffs/PROVE-RLC-A.md` §"What remains" 2(b) (G2a's height condition
for an original real interval touched by only one fresh arc). Source: W5's proof (`source/spec/p529-576.md`,
pp. 535–536): "Choose the cuts sufficiently late that their fresh incoming arcs and short available outgoing portions
at `p` lie in a prescribed small physical neighborhood of `p`. […] If `p ∈ ℍ`, choose its physical neighborhood disjoint
from the original real line. […] Suppose `p` is real. […] Shrink the physical neighborhood to one on which the original
height is one constant `C`, and which avoids both original seeds."

**Finding.** W5 itself has no gap here: its cuts are chosen late, so every real point of the fresh arcs lies in one
original interval of constant height `C` around the common real point `p`, which both paths visit strictly before
their lifetimes; strict continuation of both paths at `p` gives both of G2a's inequalities for that single `C`
(p. 536). The gap is in the *formulation* `Supp9D.RetainedLocalCompletionStatement` (and so
`RLC.RetainedLocalCompletionRealStatement`): it quantifies over *all* fresh arcs from the cuts `(u, r)` to a contact,
which may touch several original real intervals, one of them between the seeds and visited by only one path, whose
height then satisfies only that path's inequality; no G2a (or G8) reference matches it, and the source gives no
argument for that configuration.

**Fix (this file, statements only).** The localized statement `RetainedLocalCompletionLocStatement` adds W5's
late-cut localization as an antecedent (`IsLocalContact`: the fresh arcs lie in a ball around `p` which avoids `ℝ` if
`p ∈ ℍ`, avoids both seeds, and whose real trace has no boundary jump other than possibly at `Re p`). It follows from
the proved interior case and the localized real-contact case `RetainedLocalCompletionRealLocStatement`
(`retainedLocalCompletionLocStatement_of_interior_of_realLoc`, `…_of_restart`, `…_of_param`), in which the contact
point is real (`IsLocalContact.im_eq_zero`); the unlocalized statement implies it
(`retainedLocalCompletionLocStatement_of_global`). **Not done here** (the real-touch case passed to PROVE-RLC-C): the
consumer with late cuts, i.e. `Supp9D.localCompletionAtContact_of_retained` and `Supp9D.w5LocalFrameStatement_of_inputs`
re-proved from the localized statement (choose the cut window `δ` of `Supp9D.exists_incomingCuts'` by continuity of
both paths at the contact, for a radius `ρ` below `Im p` (if `p ∈ ℍ`), the distances to both seeds, and the distance
from `Re p` to the other jumps).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Supp7 Supp9 Supp9D Sec2.Assembly

/-! ### The localization -/

/-- **W5's localization of a contact** (pp. 535–536): the fresh arcs `α((u, a])`, `β((r, τ])` lie in a ball of radius
`ρ` around the contact point `p = α(a)`; the ball lies in `ℍ` if `p` does, it avoids both seeds, and its real trace
contains no boundary jump other than possibly `Re p`. -/
def IsLocalContact (J : Finset ℝ) (α : ℝ≥0 → ℂ) (u a : ℝ≥0) (β : ℝ≥0 → ℂ) (r τ : ℝ≥0) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ (∀ x : ℝ≥0, u < x → x ≤ a → α x ∈ ball (α a) ρ) ∧
    (∀ y : ℝ≥0, r < y → y ≤ τ → β y ∈ ball (α a) ρ) ∧ (α a ∈ H → ρ ≤ (α a).im) ∧
    (∀ y : ℝ, |y - (α a).re| < ρ → y ≠ (α a).re → y ∉ J) ∧ ρ ≤ ‖α 0 - α a‖ ∧ ρ ≤ ‖β 0 - α a‖

/-- At a localized contact with a real fresh point, the contact point is real. -/
theorem IsLocalContact.im_eq_zero {J : Finset ℝ} {α β : ℝ≥0 → ℂ} {u a r τ : ℝ≥0}
    (h : IsLocalContact J α u a β r τ) (hm : 0 ≤ (α a).im)
    (hreal : (∃ x : ℝ≥0, u < x ∧ x ≤ a ∧ α x ∉ H) ∨ ∃ y : ℝ≥0, r < y ∧ y ≤ τ ∧ β y ∉ H) : (α a).im = 0 := by
  obtain ⟨ρ, -, h₁, h₂, hH, -⟩ := h
  refine ((hm.lt_or_eq).resolve_left fun hpos => ?_).symm
  have hball : ∀ z ∈ ball (α a) ρ, z ∈ H := fun z hz => by
    have h1 : |z.im - (α a).im| ≤ dist z (α a) := by
      rw [Complex.dist_eq]; exact (abs_im_le_norm (z - α a)).trans_eq' (by simp)
    have h2 := lt_of_le_of_lt h1 (lt_of_lt_of_le (mem_ball.1 hz) (hH hpos))
    show 0 < z.im
    rw [abs_lt] at h2; linarith
  rcases hreal with ⟨x, hux, hxa, hx⟩ | ⟨y, hry, hyτ, hy⟩
  · exact hx (hball _ (h₁ x hux hxa))
  · exact hy (hball _ (h₂ y hry hyτ))

/-- **The localized local completion** (`Supp9D.RetainedLocalCompletionStatement` with W5's localization of the
contact, `IsLocalContact`, as an additional antecedent). -/
def RetainedLocalCompletionLocStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ u r : ℝ≥0, ∀ᵐ ω ∂P, Supp7.IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r →
      ∀ a τ : ℝ≥0, u < a → (a : ℝ≥0∞) < ζ₁ ω → r < τ → (τ : ℝ≥0∞) < ζ₂ ω → η₁ ω a = η₂ ω τ →
        (∀ x : ℝ≥0, u < x → x ≤ a → η₁ ω x ∉ η₁ ω '' Icc 0 u ∪ η₂ ω '' Icc 0 r) →
        (∀ y : ℝ≥0, r < y → y ≤ τ → η₂ ω y ∉ η₁ ω '' Icc 0 u ∪ η₂ ω '' Icc 0 r) →
        IsLocalContact jumps (η₁ ω) u a (η₂ ω) r τ →
        ∃ a₂ b₂ : ℝ≥0, a < a₂ ∧ (a₂ : ℝ≥0∞) < ζ₁ ω ∧ τ < b₂ ∧ (b₂ : ℝ≥0∞) < ζ₂ ω ∧
          HasOrderedProperCompletions (η₁ ω) a₂ (η₂ ω) b₂

/-- **Named input: the localized real-contact case** (W5, pp. 535–536: "G8 or G2a with G7a for real `p`", with G9,
G10 and the planar gluing across the genuine original-real contacts of the local buffer): the localized local
completion when some fresh point is real (then the contact point is real, `IsLocalContact.im_eq_zero`, and every real
point of the fresh arcs lies in the jump-free interval around it). **Not proved in Lean.** -/
def RetainedLocalCompletionRealLocStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ u r : ℝ≥0, ∀ᵐ ω ∂P, Supp7.IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r →
      ∀ a τ : ℝ≥0, u < a → (a : ℝ≥0∞) < ζ₁ ω → r < τ → (τ : ℝ≥0∞) < ζ₂ ω → η₁ ω a = η₂ ω τ →
        (∀ x : ℝ≥0, u < x → x ≤ a → η₁ ω x ∉ η₁ ω '' Icc 0 u ∪ η₂ ω '' Icc 0 r) →
        (∀ y : ℝ≥0, r < y → y ≤ τ → η₂ ω y ∉ η₁ ω '' Icc 0 u ∪ η₂ ω '' Icc 0 r) →
        IsLocalContact jumps (η₁ ω) u a (η₂ ω) r τ →
        ((∃ x : ℝ≥0, u < x ∧ x ≤ a ∧ η₁ ω x ∉ H) ∨ ∃ y : ℝ≥0, r < y ∧ y ≤ τ ∧ η₂ ω y ∉ H) →
        ∃ a₂ b₂ : ℝ≥0, a < a₂ ∧ (a₂ : ℝ≥0∞) < ζ₁ ω ∧ τ < b₂ ∧ (b₂ : ℝ≥0∞) < ζ₂ ω ∧
          HasOrderedProperCompletions (η₁ ω) a₂ (η₂ ω) b₂

/-- The unlocalized statement implies the localized one. -/
theorem retainedLocalCompletionLocStatement_of_global (hL : Supp9D.RetainedLocalCompletionStatement.{u}) :
    RetainedLocalCompletionLocStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r
  filter_upwards [hL κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r]
    with ω hω hord a τ hua haζ hrτ hτζ hp hf₁ hf₂ _
  exact hω hord a τ hua haζ hrτ hτζ hp hf₁ hf₂

/-- **The localized local completion from the interior case and the localized real-contact case.** -/
theorem retainedLocalCompletionLocStatement_of_interior_of_realLoc
    (hI : RetainedLocalCompletionInteriorStatement.{u}) (hR : RetainedLocalCompletionRealLocStatement.{u}) :
    RetainedLocalCompletionLocStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r
  filter_upwards [hI κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r,
    hR κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r]
    with ω hIω hRω hord a τ hua haζ hrτ hτζ hp hf₁ hf₂ hloc
  by_cases hin : (∀ x : ℝ≥0, u < x → x ≤ a → η₁ ω x ∈ H) ∧ ∀ y : ℝ≥0, r < y → y ≤ τ → η₂ ω y ∈ H
  · exact hIω hord a τ hua haζ hrτ hτζ hp hf₁ hf₂ hin.1 hin.2
  · refine hRω hord a τ hua haζ hrτ hτζ hp hf₁ hf₂ hloc ?_
    by_contra hno
    push Not at hno
    exact hin ⟨fun x h1 h2 => hno.1 x h1 h2, fun y h1 h2 => hno.2 y h1 h2⟩

/-- **The localized local completion from G2, G3, the retained-pair restart and the localized real-contact case.** -/
theorem retainedLocalCompletionLocStatement_of_restart (hG2 : G2ReferenceStatement.{0})
    (hG3 : G3ChartComparisonStatement.{0}) (hRst : RetainedPairRestartStatement.{u})
    (hR : RetainedLocalCompletionRealLocStatement.{u}) : RetainedLocalCompletionLocStatement.{u} :=
  retainedLocalCompletionLocStatement_of_interior_of_realLoc
    (retainedLocalCompletionInteriorStatement_of_chart (retainedChartCompletionStatement_of_restart hG2 hG3 hRst)) hR

/-- **The localized local completion from G2, G3, Theorems 1.2 (param), 1.3, PROVE-CONDDET's two-tip input and the
localized real-contact case.** -/
theorem retainedLocalCompletionLocStatement_of_param (hG2 : G2ReferenceStatement.{0})
    (hG3 : G3ChartComparisonStatement.{0}) (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : Restart.RetainedCanonCondDetStatement.{u})
    (hR : RetainedLocalCompletionRealLocStatement.{u}) : RetainedLocalCompletionLocStatement.{u} :=
  retainedLocalCompletionLocStatement_of_interior_of_realLoc
    (retainedLocalCompletionInteriorStatement_of_chart
      (retainedChartCompletionStatement_of_param hG2 hG3 h12p h13 hD)) hR

end RLC

end InteractingSLE
