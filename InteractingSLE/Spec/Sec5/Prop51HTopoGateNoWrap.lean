/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HTopoGatePaths

/-!
# Finite descent for positive-gate exit

Failure of a positive terminal prime end gives all western excursion ends, by
the proved endpoint limits. Under the explicitly named geometric detour input,
an outer-face path can then cross a strict subset of its previous finite
excursion family. A path minimizing that family's cardinality rules this out.
The detour construction is the sole unproved input in this conditional assembly.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Bornology
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Prop51HTopo

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G

/-- Under the established endpoint regularity, exclusion of positive ends
already implies strictly western ends. No rational-barrier input is needed
for this direction, and zero endpoints are excluded by actual tip avoidance. -/
theorem hasWesternExcursionEnds_of_not_positive {η β : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ}
    (hη : IsProperArc η) (hβ : IsLoewnerTrace w β) (hw : Continuous w)
    (hw0 : w 0 = 0) (hs : 0 ≤ s) (hβs : β s ≠ 0)
    (htip : negInv (β s) ∉ arcRange η) (hnp : ¬ HasPositiveExcursionEnd η w s) :
    HasWesternExcursionEnds η w s := by
  constructor
  · intro a b ha hab hD hb
    obtain ⟨x, hx0, hlim⟩ := exists_tendsto_revChart_left hη hβ hw hw0 hs ha hab hD hb
      (fun he => htip ⟨b, (ha.trans hab).le, he⟩)
    have hxn : x ≤ 0 := le_of_not_gt (fun hx =>
      hnp (Or.inl ⟨a, b, x, ha, hab, hx, hD, hb, hlim⟩))
    exact ⟨x, lt_of_le_of_ne hxn hx0, hlim⟩
  · intro a ha hD
    obtain ⟨x, hx0, hlim⟩ := exists_tendsto_revChart_atTop hη hβ hw hw0 hs hβs ha hD
    have hxn : x ≤ 0 := le_of_not_gt (fun hx => hnp (Or.inr ⟨a, x, ha, hx, hD, hlim⟩))
    exact ⟨x, lt_of_le_of_ne hxn hx0, hlim⟩

/-- **Unproved remaining local planar construction.** When all forward ends
are western, an actual gate-to-outer-face path can be detoured to the same outer
endpoint while crossing a strict subset of its excursion family. The subset
clause forbids adding previously unvisited excursions. Compact crossing
finiteness, completed finite crosscuts and physical side orientation are proved
elsewhere; none of them is substituted for this detour construction.
This proposition is only an explicit hypothesis of the assembly lemmas below. -/
def WesternGateDetourStatement : Prop :=
  ∀ (η : ℝ → ℂ) (w : ℝ → ℝ) (β : ℝ → ℂ) (s : ℝ),
    IsProperArc η → Continuous w → w 0 = 0 → IsLoewnerTrace w β → 0 < s →
    (∀ v : ℝ, 0 < v → β v ≠ 0) → negInv (β s) ∉ arcRange η →
    IsBounded (chartFlowSet η w s) → HasWesternExcursionEnds η w s →
    ∀ (c : PositiveGateComponent η w s) (p : GateExitPath c),
      ∃ q : GateExitPath c, q.curve 1 = p.curve 1 ∧ q.crossed ⊂ p.crossed

/-- The actual finite descent: choose a minimal crossed-excursion family;
western ends would allow a strict bypass, contradicting minimality. -/
theorem positiveGateExitStatement_of_westernGateDetour
    (hdetour : WesternGateDetourStatement) : PositiveGateExitStatement := by
  intro η w β s hη hw hw0 hβ hs hnr htip hb c
  by_contra hnp
  have hends := hasWesternExcursionEnds_of_not_positive hη hβ hw hw0 hs.le
    (hnr s hs) htip hnp
  obtain ⟨p, hmin⟩ := c.exists_minimal_exitPath hb
  obtain ⟨q, _, hstrict⟩ := hdetour η w β s hη hw hw0 hβ hs hnr htip hb hends c p
  exact p.not_strict_bypass hη hw hw0 hs.le hmin q hstrict

/-- Conditional assembly of the unchanged original no-wrap statement after
the positive-gate exit selection has been reduced to the precise detour input. -/
theorem fwdNoWrapQStatement_of_westernGateDetour
    (hdetour : WesternGateDetourStatement) : FwdNoWrapQStatement :=
  fwdNoWrapQStatement_of_positiveGateExit
    (positiveGateExitStatement_of_westernGateDetour hdetour)

end InteractingSLE.Sec5.Prop51HTopo
