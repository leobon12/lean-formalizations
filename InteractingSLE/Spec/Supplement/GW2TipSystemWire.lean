/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TipSystemSched
import InteractingSLE.Spec.Supplement.GW2TipUnbounded

/-!
# GW2's tip exhaustion from per-schedule stage claims

Packet PROVE-T14-TIP12. PROVE-T14-TIP11 reduced GW2's tip exhaustion (`GW2Tip.GW2TipExhaustionCanonStatement`) to
`GW2TipStage.GW2StageSystemStatement`: a valid **adaptive** stage system for every tolerance. This file reduces it
further, to **non-adaptive per-schedule** claims (`GW2TipSystem.SchedRule.IsValid`): for every fixed finite schedule
(a root and finitely many angle–time entries) and its stage-start σ-algebra (the counterflow history at the stop `s`
and the canonical prefix of the schedule), the stage claim of follow-up note A.3–A.4 under the schedule's regular
conditional law (some rule succeeds with conditional probability `≥ 1 − ε_j`), the uniform Lemma 5.10 at even depths,
the initial cover of A.5 and the capacity bookkeeping. The adaptive selection (least qualifying rule index, A.2/A.4)
and the countable tree of rule–outcome histories are built and verified in `GW2TipSystemRule`, `GW2TipSystemSelect`,
`GW2TipSystemSched` (generic).

* **`GW2SchedRuleStatement`** (named): in the setting of `GW2TipStage.GW2StageSystemStatement`, for every tolerance
  `ε₀ > 0` a valid schedule rule for the event `{γ(s) ∈ ℍ}` and the target `GW2TipStage.jointTarget`;
* **`gw2StageSystemStatement_of_schedRules`**: it implies TIP11's `GW2StageSystemStatement`;
* `gw2TipJointUnboundedStatement_of_schedRules`, **`gw2TipExhaustionCanonStatement_of_schedRules`**: hence the
  joint-chart unboundedness and the canonical tip exhaustion (TIP9's and TIP11's chains).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2TipSystem

open GW2Schedule GW2Cone GW2Later GW2Tip GW2TipStage Exist Staged StagedLaw Restart LQGMetric

/-- **Named statement: GW2's per-schedule stage claims** (follow-up note A.2–A.5; GB9, pp. 525–526). Binders of
`GW2TipStage.GW2StageSystemStatement`; conclusion: for every tolerance `ε₀ > 0` there is a schedule rule
(`SchedRule`: per fixed schedule, its stage-start σ-algebra, rule success and outcome events, unit events, capacity),
valid for the event `{γ(s) ∈ ℍ}` and the target `jointTarget` (the joint-chart image of the canonical family off the
counterflow hull), with total tolerance `ε₀`. -/
def GW2SchedRuleStatement : Prop :=
  ∀ κ : ℝ, ∀ hκ : 0 < κ, κ < 4 → ∀ (h12p : Theorem12ParamStatement.{u})
    (βA : BoundaryWord × ℝ × RecData → BoundaryWord), IsStopLaw.{u} κ βA →
    ∀ (b : ℝ → ℝ) (jumps : Finset ℝ) (c₀ : BoundaryWord), IsPiecewiseConstantBoundaryData b jumps →
      c₀.jumps = jumps → (∀ y ∉ jumps, c₀.fn y = b y) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ Θ : Set ℝ, Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) → Θ.Countable →
      Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ →
    ∀ Q : Set ℝ≥0, Q.Countable → Dense Q → (∀ q ∈ Q, 0 < q) →
      ∀ γ : Ω → ℝ≥0 → ℂ, (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (γ ω)) →
        ∀ s : ℝ≥0, ∀ ε₀ : ℝ≥0∞, 0 < ε₀ → ∃ T : SchedRule Ω,
          T.IsValid P {ω | γ ω s ∈ H} (jointTarget hκ h12p βA b jumps c₀ h W' Θ Q s) ε₀

/-- **TIP11's per-stage statement from the per-schedule claims**: the adaptive construction
(`SchedRule.toRule`, `StageRule.toSystem`) of a valid schedule rule is a valid stage system. -/
theorem gw2StageSystemStatement_of_schedRules (hS : GW2SchedRuleStatement.{u}) : GW2StageSystemStatement.{u} := by
  intro κ hκ hκ4 h12p βA hβA b jumps c₀ hb hc₀J hc₀ Ω _ _ P _ h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd Q hQc hQd hQpos
    γ hγ s ε₀ hε₀
  obtain ⟨T, hv⟩ :=
    hS κ hκ hκ4 h12p βA hβA b jumps c₀ hb hc₀J hc₀ P h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd Q hQc hQd hQpos γ hγ s ε₀ hε₀
  exact ⟨(T.toRule P).toSystem, hv.toRule_isValid.toSystem_isValid⟩

/-- **GW2's joint-chart unboundedness from the per-schedule claims.** -/
theorem gw2TipJointUnboundedStatement_of_schedRules (hS : GW2SchedRuleStatement.{u}) :
    GW2TipJointUnboundedStatement.{u} :=
  gw2TipJointUnboundedStatement_of_stageSystems (gw2StageSystemStatement_of_schedRules hS)

/-- **The canonical tip exhaustion from the per-schedule claims** (TIP9's and TIP11's chains). -/
theorem gw2TipExhaustionCanonStatement_of_schedRules (hS : GW2SchedRuleStatement.{u}) :
    GW2TipExhaustionCanonStatement.{u} :=
  gw2TipExhaustionCanonStatement_of_stageSystems (gw2StageSystemStatement_of_schedRules hS)

end GW2TipSystem

end Theorem14

end InteractingSLE
