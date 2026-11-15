/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LkSplit

/-!
# SB2(2)'s geometric half reduced to the range identity of the lifted walk

Packet PROVE-T14-SB2LIFT (round 7). The geometric half `Lk.SB2LowerRelWalkStatement` asks for a measurable family of
relative drivers, regular at every sample, such that almost surely under the retained kernel, for every proper
parametrization `β₀` of the actual lower walk, the tail of `β₀` after `R` lifts onto the relative walk
(`Lf.IsTailLiftOf`: a lift curve exists **and** its range is the relative walk's physical set). The existence of the
lift curve is proved (`Lk.sb2LowerTailLiftCurve`, Lemma S2 reflected and the finite-fibre extension). This file
separates it off:

* **`SB2LowerRelWalkRangeStatement`** (named input; the remaining content of the geometric half, P1–P4): at the
  later launches there is a measurable family `EL` of drivers regular at every sample whose relative walk's physical
  set is, almost surely under the retained kernel, the range of **every** lift curve of every proper parametrization
  of the actual lower walk;
* **`sb2LowerRelWalkStatement_of_range`**: it gives `Lk.SB2LowerRelWalkStatement` (with Theorem 1.3, for the lift
  curve);
* **`sb2LowerLaunchLiftStatement_of_range`**: SB2(2)'s combined target (R104a) from Theorems 1.2–1.3, the range
  statement and the conditional half `Lk.SB2LowerRelStageCondStatement`.

R48: Theorems 1.2–1.3 appear only as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw

/-- **The range identity at one launch**: for `m = −e_R` there is a measurable family of drivers, regular at every
sample, whose relative walk's physical set is almost surely the range of every lift curve of the actual tail. -/
def RelWalkRange (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∃ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
    (∀ j, Measurable (EL j)) ∧ (∀ j ω, IsRegularDriver (EL j ω)) ∧
    ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
        ∀ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), IsTailLiftCurve c (realMax (upperPrefix κ b jumps E u l k ω₀)) m β₀ tL γ →
          range γ = relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω

/-- **Named input: the range identity of SB2(2)'s lifted walk at the later launches.** -/
def SB2LowerRelWalkRangeStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → RelWalkRange κ b jumps P E u l k ω₀ c b' J'

/-- **The geometric half from the range identity** (and Theorem 1.3, for the lift curve). -/
theorem sb2LowerRelWalkStatement_of_range (h13 : Exist.Theorem13Statement.{u})
    (hN : SB2LowerRelWalkRangeStatement.{u}) : SB2LowerRelWalkStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hN κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerTailLiftCurve h13 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft]
    with ω₀ hN₀ hC₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨EL, hELm, hELr, hrange⟩ := hN₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  refine ⟨EL, hELm, hELr, ?_⟩
  filter_upwards [hrange, hC₀ c θ hlaunch b' J' h' hb' hT' hG' m hm] with ω h1 h2
  intro β₀ hβ hβ0 hβr
  obtain ⟨tL, γ, hγ⟩ := h2 β₀ hβ hβ0 hβr
  exact isTailLiftOf_iff.2 ⟨tL, γ, hγ, h1 β₀ hβ hβ0 hβr tL γ hγ⟩

/-- **SB2(2)'s combined target (R104a) from the range identity and the conditional half** (and Theorems 1.2–1.3). -/
theorem sb2LowerLaunchLiftStatement_of_range (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hN : SB2LowerRelWalkRangeStatement.{u})
    (hcond : SB2LowerRelStageCondStatement.{u}) : Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_split h12 h13 h12₀ h13₀ (sb2LowerRelWalkStatement_of_range h13 hN) hcond

end InteractingSLE.Theorem14.SB.Lk
