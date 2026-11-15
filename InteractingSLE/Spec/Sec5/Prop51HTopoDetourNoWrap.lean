/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HTopoDetourFamily

/-!
# Precise finite-crosscut and terminal bypass obligations

All completed finite crosscuts are now constructed. The remaining planar
obligation must turn these data into a bypass without adding another crossed
excursion. It is recorded explicitly, separately from the terminal-excursion
case. No last contact removes the terminal case, but does not construct a bypass.
The original universal statements are assembled conditionally and unchanged.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Bornology
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Prop51HTopo

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G

/-- **Unproved finite-crosscut planar input.** The crossed components are
already completed to actual simple crosscuts, with their physical time
direction and strictly western finishing gates. The missing assertion is a
same-endpoint bypass crossing a strict subset of the old family. In particular,
it must control excursions accumulating at the real boundary during a detour.
This distinct conditional input does not replace any original statement. -/
def FiniteWesternCrosscutBypassStatement : Prop :=
  ∀ (η : ℝ → ℂ) (w : ℝ → ℝ) (s : ℝ),
    IsProperArc η → Continuous w → w 0 = 0 → 0 ≤ s →
    IsBounded (chartFlowSet η w s) →
    ∀ (c : PositiveGateComponent η w s) (p : GateExitPath c),
      (∀ C ∈ p.crossed, Nonempty (WesternFiniteCrosscut η w s C)) →
      ∃ q : GateExitPath c, q.curve 1 = p.curve 1 ∧ q.crossed ⊂ p.crossed

/-- **Unproved terminal-excursion planar input.** This is the additional
case needed by the universal deterministic statement. The small-gap
no-last-contact theorem excludes its premise only on that probabilistic regime. -/
def TerminalWesternCrosscutBypassStatement : Prop :=
  ∀ (η : ℝ → ℂ) (w : ℝ → ℝ) (s : ℝ),
    IsProperArc η → Continuous w → w 0 = 0 → 0 ≤ s →
    IsBounded (chartFlowSet η w s) → HasWesternExcursionEnds η w s →
    ∀ (c : PositiveGateComponent η w s) (p : GateExitPath c),
      (∃ t x : ℝ, 0 < t ∧ x < 0 ∧
        connectedComponentIn (excursionTimes η w s) t ∈ p.crossed ∧
        (∀ v ∈ Ioi t, η v ∈ H \ cfHullQ w s) ∧
        Tendsto (fun v => revChart w s (η v)) atTop (𝓝 (x : ℂ))) →
      ∃ q : GateExitPath c, q.curve 1 = p.curve 1 ∧ q.crossed ⊂ p.crossed

/-- The original detour statement follows from its finite-crosscut and
terminal cases. The crossed-component dichotomy is proved, not assumed. -/
theorem westernGateDetourStatement_of_crosscutBypasses
    (hfinite : FiniteWesternCrosscutBypassStatement)
    (hterminal : TerminalWesternCrosscutBypassStatement) : WesternGateDetourStatement := by
  intro η w β s hη hw hw0 hβ hs _hnr htip hb hends c p
  rcases p.finiteCrosscuts_or_terminal hη hβ hw hw0 hs.le htip hends with hf | ht
  · exact hfinite η w s hη hw hw0 hs.le hb c p hf
  · exact hterminal η w s hη hw hw0 hs.le hb hends c p ht

/-- Conditional completion of the unchanged positive-gate selection statement. -/
theorem positiveGateExitStatement_of_crosscutBypasses
    (hfinite : FiniteWesternCrosscutBypassStatement)
    (hterminal : TerminalWesternCrosscutBypassStatement) : PositiveGateExitStatement :=
  positiveGateExitStatement_of_westernGateDetour
    (westernGateDetourStatement_of_crosscutBypasses hfinite hterminal)

/-- Conditional completion of the unchanged universal no-wrap statement. -/
theorem fwdNoWrapQStatement_of_crosscutBypasses
    (hfinite : FiniteWesternCrosscutBypassStatement)
    (hterminal : TerminalWesternCrosscutBypassStatement) : FwdNoWrapQStatement :=
  fwdNoWrapQStatement_of_westernGateDetour
    (westernGateDetourStatement_of_crosscutBypasses hfinite hterminal)

/-- With no last contact, the finite-crosscut bypass alone forces a positive
end. There is no terminal-case input in this pathwise theorem. -/
theorem hasPositiveExcursionEnd_of_noLastContact_of_finiteCrosscutBypass
    (hfinite : FiniteWesternCrosscutBypassStatement)
    {η β : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ}
    (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0)
    (hβ : IsLoewnerTrace w β) (hs : 0 < s) (hβs : β s ≠ 0)
    (htip : negInv (β s) ∉ arcRange η) (hb : IsBounded (chartFlowSet η w s))
    (hno : NoLastCounterflowContact η w s) (c : PositiveGateComponent η w s) :
    HasPositiveExcursionEnd η w s := by
  by_contra hnp
  have hends := hasWesternExcursionEnds_of_not_positive hη hβ hw hw0 hs.le hβs htip hnp
  obtain ⟨p, hmin⟩ := c.exists_minimal_exitPath hb
  obtain ⟨q, _, hq⟩ := hfinite η w s hη hw hw0 hs.le hb c p
    (p.westernFiniteCrosscuts_of_noLastContact hη hβ hw hw0 hs.le htip hends hno)
  exact p.not_strict_bypass hη hw hw0 hs.le hmin q hq

/-- The no-last-contact route to the physical no-wrap conclusion. The only
unproved planar input is the finite-crosscut bypass; rational barriers and
the original counterflow hypotheses are retained exactly. -/
theorem negInv_notMem_leftSideOf_of_noLastContact_of_finiteCrosscutBypass
    (hfinite : FiniteWesternCrosscutBypassStatement)
    {η β : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ}
    (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0)
    (hβ : IsLoewnerTrace w β) (hs : 0 < s) (hnr : ∀ v : ℝ, 0 < v → β v ≠ 0)
    (hbar : ∀ t : ℚ, 0 ≤ t → FirstContactNotEast w s t η)
    (hno : NoLastCounterflowContact η w s) : negInv (β s) ∉ leftSideOf (arcRange η) := by
  intro hleft
  have htip := hleft.1.2
  have hb := isBounded_revChart_arcRange_of_mem_leftSideOf hη hβ hw hw0 hs.le hleft
  have hends := hasWesternExcursionEnds_of_rational hη hβ hw hw0 hs.le (hnr s hs)
    htip hbar
  obtain ⟨g⟩ := exists_positiveBoundaryGate hη hβ hw hw0 hs.le
  have ho : ball (g.source : ℂ) g.radius ∩ H ⊆ outerChartFace η w s := by
    rcases g.halfBall_dichotomy with ho | hf
    · exact ho
    · obtain ⟨c, _⟩ := g.exists_boundedComponent hf
      exact (hends.not_positive
        (hasPositiveExcursionEnd_of_noLastContact_of_finiteCrosscutBypass hfinite
          hη hw hw0 hβ hs (hnr s hs) htip hb hno c)).elim
  exact tip_notMem_leftSideOf_of_outerFace_access hη hβ hw hw0 hs.le (hnr s hs) hb
    (Or.inl ⟨g.target, g.target_pos, g.physical_access ho⟩) hleft

end InteractingSLE.Sec5.Prop51HTopo
