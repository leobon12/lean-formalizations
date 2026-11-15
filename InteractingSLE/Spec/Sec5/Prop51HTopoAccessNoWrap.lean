/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HTopoAccessComponent

/-!
# Positive-gate exit reduction for contacted no-wrap

The free gate and its possible bounded component are constructed in the
preceding modules. The remaining planar selection assertion says that a bounded
positive-gate component forces a positively ending excursion. Western ends
exclude that assertion's conclusion, so the gate must belong to the outer face.
This supplies positive-boundary access directly; no collar construction remains
in this reduction. The planar selection assertion is an explicit hypothesis,
not an asserted theorem or a source-facing assumption.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Bornology
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Prop51HTopo

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G

/-- A positive terminal prime end, at a finite first exit or at infinite
original time. This is the exact alternative excluded by western ends. -/
def HasPositiveExcursionEnd (η : ℝ → ℂ) (w : ℝ → ℝ) (s : ℝ) : Prop :=
  (∃ a b x : ℝ, 0 < a ∧ a < b ∧ 0 < x ∧
    (∀ t ∈ Ico a b, η t ∈ H \ cfHullQ w s) ∧ η b ∉ H \ cfHullQ w s ∧
      Tendsto (fun t => revChart w s (η t)) (𝓝[<] b) (𝓝 (x : ℂ))) ∨
  (∃ a x : ℝ, 0 ≤ a ∧ 0 < x ∧ (∀ t ∈ Ioi a, η t ∈ H \ cfHullQ w s) ∧
    Tendsto (fun t => revChart w s (η t)) atTop (𝓝 (x : ℂ)))

/-- Both end predicates use the same nontrivial one-sided or infinite filter;
uniqueness of the terminal limit excludes a positive western endpoint. -/
theorem HasWesternExcursionEnds.not_positive {η : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ}
    (hends : HasWesternExcursionEnds η w s) : ¬ HasPositiveExcursionEnd η w s := by
  rintro (⟨a, b, x, ha, hab, hx, hD, hb, hlim⟩ | ⟨a, x, ha, hx, hD, hlim⟩)
  · obtain ⟨y, hy, hylim⟩ := hends.1 a b ha hab hD hb
    have heq := ofReal_injective (tendsto_nhds_unique hlim hylim)
    linarith
  · obtain ⟨y, hy, hylim⟩ := hends.2 a ha hD
    have heq := ofReal_injective (tendsto_nhds_unique hlim hylim)
    linarith

/-- **Unproved remaining planar selection assertion.** A bounded component
behind an untouched positive original-real gate must have a forward excursion
ending at a positive chart prime end. The gate component and its physical
right-side orientation are already constructed, not assumed as extra source
data. This assertion has no western-end premise and no no-wrap conclusion.
Handling its countable excursion frontier is the remaining mathematical step. -/
def PositiveGateExitStatement : Prop :=
  ∀ (η : ℝ → ℂ) (w : ℝ → ℝ) (β : ℝ → ℂ) (s : ℝ),
    IsProperArc η → Continuous w → w 0 = 0 → IsLoewnerTrace w β → 0 < s →
    (∀ v : ℝ, 0 < v → β v ≠ 0) → negInv (β s) ∉ arcRange η →
    IsBounded (chartFlowSet η w s) →
    PositiveGateComponent η w s → HasPositiveExcursionEnd η w s

/-- The selection assertion, if discharged, puts every free positive gate
half-ball in the outer face: its filled alternative is impossible. -/
theorem positiveBoundaryGate_outer_of_positiveGateExit
    (hexit : PositiveGateExitStatement) {η β : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ}
    (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0)
    (hβ : IsLoewnerTrace w β) (hs : 0 < s) (hnr : ∀ v : ℝ, 0 < v → β v ≠ 0)
    (htip : negInv (β s) ∉ arcRange η) (hb : IsBounded (chartFlowSet η w s))
    (hends : HasWesternExcursionEnds η w s) (g : PositiveBoundaryGate η w s) :
    Metric.ball (g.source : ℂ) g.radius ∩ H ⊆ outerChartFace η w s := by
  rcases g.halfBall_dichotomy with ho | hf
  · exact ho
  · obtain ⟨c, _⟩ := g.exists_boundedComponent hf
    exact (hends.not_positive (hexit η w β s hη hw hw0 hβ hs hnr htip hb c)).elim

/-- Conditional completion of the previously named geometric access input.
Only its positive-boundary branch is needed by this reduction. -/
theorem contactedOuterFaceAccessStatement_of_positiveGateExit
    (hexit : PositiveGateExitStatement) : ContactedOuterFaceAccessStatement := by
  intro η w β s hη hw hw0 hβ hs hnr _ htip hends hb
  obtain ⟨g⟩ := exists_positiveBoundaryGate hη hβ hw hw0 hs.le
  have ho := positiveBoundaryGate_outer_of_positiveGateExit hexit hη hw hw0 hβ hs
    hnr htip hb hends g
  exact Or.inl ⟨g.target, g.target_pos, g.physical_access ho⟩

/-- The exact original no-wrap statement from the sole remaining positive-gate
excursion-selection input. This theorem is explicitly conditional. -/
theorem fwdNoWrapQStatement_of_positiveGateExit
    (hexit : PositiveGateExitStatement) : FwdNoWrapQStatement :=
  fwdNoWrapQStatement_of_outerFaceAccess
    (contactedOuterFaceAccessStatement_of_positiveGateExit hexit)

end InteractingSLE.Sec5.Prop51HTopo
