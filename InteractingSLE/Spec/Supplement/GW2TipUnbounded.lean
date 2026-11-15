/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TipStageTree
import InteractingSLE.Spec.Supplement.GW2TipAssembly

/-!
# GW2's tip exhaustion from the stage experiment's per-stage bounds

Packet PROVE-T14-TIP11. Follow-up note A.5 (`source/external/AstraIG1/ig1_followup_a_e_audited.txt` L222–L241;
GB9, `source/spec/p481-528.md` L1082–L1100, p. 526) assembles the stages: an initial positive interior prefix
(a countable almost-sure cover), alternating near-extreme stages with conditional failure probabilities `εⱼ`
(`Σ εⱼ ≤ ε`), the uniform one-unit estimate at even stages (Lemma 5.10), "Relative capacity is therefore unbounded.
A bounded relative trace range would bound its filled hull in a rectangle, and hence bound its half-plane capacity.
The selected ranges are consequently unbounded in the joint chart … let `ε ↓ 0`".

This file states the per-stage content as one named statement and proves the assembly:

* **`GW2StageSystemStatement`** (named): in the setting of `GW2Tip.GW2TipJointUnboundedStatement`, for every tolerance
  `ε₀ > 0` there is a valid stage system (`GW2TipStage.StageSystem.IsValid`) for the event `{γ(s) ∈ ℍ}` and the
  joint-chart
  image of the canonical light-cone family off the counterflow hull. Its fields are exactly the source's per-stage
  claims: the countable tree of finite histories with times in `Q` and angles in `Θ` (A.5: "Every successful finite
  history uses only `Θ` and `Q`"), the stage-start information of each history, the one-stage success bound (A.2–A.4),
  the unit bound at even stages (Lemma 5.10), the initial cover (A.5, "a countable almost-sure cover"), and the
  relative capacity of each history with `2t ≤ 2r²`-type bound ("bound its half-plane capacity").
* **`gw2TipJointUnboundedStatement_of_stageSystems`**: it implies `GW2Tip.GW2TipJointUnboundedStatement`
  (by `GW2TipStage.ae_not_isBounded_of_stageSystems`: the adaptive iteration of A.5 along the tree);
* **`gw2TipExhaustionCanonStatement_of_stageSystems`**: hence the canonical tip exhaustion
  (`GW2Tip.GW2TipExhaustionCanonStatement`, PROVE-T14-TIP9's chain).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2TipStage

open GW2Schedule GW2Cone GW2Later GW2Tip Exist Staged StagedLaw Restart LQGMetric

/-- **The target set of the exhaustion at the counterflow stop `s`**: the joint-chart image
(`GW2JointKernel.jointChart`, physical tip `−1/γ(s)` at `∞`) of the canonical light-cone family off the counterflow
hull. -/
def jointTarget {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
    (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (b : ℝ → ℝ) (jumps : Finset ℝ) (c₀ : BoundaryWord)
    {Ω : Type u} (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (Θ : Set ℝ) (Q : Set ℝ≥0)
    (s : ℝ≥0) (ω : Ω) : Set ℂ :=
  (GW2JointKernel.jointChart (fun r : ℝ => W' r.toNNReal ω) s).1 ''
    (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => canonSpecFam hκ h12p βA c₀ h spec k ω) ∩
      (fun z : ℂ => -z⁻¹) '' (H \ QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal ω) s))

/-- **Named statement: the stage experiment's per-stage bounds** (follow-up note A.2–A.5; GB9, pp. 525–526). Binders of
`GW2Tip.GW2TipJointUnboundedStatement`; conclusion: for every tolerance `ε₀ > 0` there is a stage system, valid for the
event `{γ(s) ∈ ℍ}` and the target `jointTarget` (the joint-chart image of the canonical family off the counterflow
hull), with total tolerance `ε₀`. -/
def GW2StageSystemStatement : Prop :=
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
        ∀ s : ℝ≥0, ∀ ε₀ : ℝ≥0∞, 0 < ε₀ → ∃ T : StageSystem Ω,
          T.IsValid P {ω | γ ω s ∈ H} (jointTarget hκ h12p βA b jumps c₀ h W' Θ Q s) ε₀

/-- **GW2's joint-chart unboundedness from the per-stage bounds** (follow-up note A.5): the adaptive iteration along the
tree of histories (`GW2TipStage.ae_not_isBounded_of_stageSystems`). -/
theorem gw2TipJointUnboundedStatement_of_stageSystems (hS : GW2StageSystemStatement.{u}) :
    GW2TipJointUnboundedStatement.{u} := by
  intro κ hκ hκ4 h12p βA hβA b jumps c₀ hb hc₀J hc₀ Ω _ _ P _ h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd Q hQc hQd hQpos
    γ hγ s
  have := ae_not_isBounded_of_stageSystems (P := P) (G := {ω | γ ω s ∈ H})
    (S := jointTarget hκ h12p βA b jumps c₀ h W' Θ Q s) fun ε₀ hε₀ =>
      hS κ hκ hκ4 h12p βA hβA b jumps c₀ hb hc₀J hc₀ P h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd Q hQc hQd hQpos γ hγ s ε₀
        hε₀
  exact this

/-- **The canonical tip exhaustion from the per-stage bounds** (PROVE-T14-TIP9's chain:
`gw2TipExhaustionCanonAllQStatement_of_jointUnbounded`, `gw2TipExhaustionCanonStatement_of_canonAllQ`). -/
theorem gw2TipExhaustionCanonStatement_of_stageSystems (hS : GW2StageSystemStatement.{u}) :
    GW2TipExhaustionCanonStatement.{u} :=
  gw2TipExhaustionCanonStatement_of_canonAllQ
    (gw2TipExhaustionCanonAllQStatement_of_jointUnbounded (gw2TipJointUnboundedStatement_of_stageSystems hS))

end GW2TipStage

end Theorem14

end InteractingSLE
