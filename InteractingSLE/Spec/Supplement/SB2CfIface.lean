/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CfRoot
import InteractingSLE.Spec.Supplement.SB2XzPhys
import InteractingSLE.Spec.Supplement.SB2XzTW

/-!
# SB2(2)'s conditional half over the bundle without `tail` (decision D36)

Packet PROVE-SB2-CONDFIN (Target 2, retargeted by D36). The `T`/`TR` bundles are false (their `tail` field; SB2LIFT
§R29.1), so the conditional half and its inputs are restated over SB2LIFT's corrected bundle `Mn.ClauseTW ∧
Mn.StageFactsAS`, together with LIFTSET's root facts `Lk.RootFactsAS` (D25), which the root record needs
(`Cf.SB2LowerRootRecRFStatement`; without them the relative root may be `zeroDrv` or not on samples with the same
B-runs, so its record need not be known to B's marks):

* `RelDataClauseW` (the bundle), `RelStageCondW`, **`SB2LowerRelStageCondWStatement`** (the conditional half, D36's
  `CondW`), `RelStagePosW`, `SB2LowerRelPosWStatement` (the positive-lifetime code match);
* the inputs owned by others, each a named statement:
  - **`SB2LowerZeroClauseWStatement`** (SB2LIFT, (L1)/D11 over the corrected bundle): every relative stage `j ≥ 1`
    that launches has positive lifetime;
  - **`SB2LowerRelPosWRootStatement`**: the code match of a relative root of positive lifetime (the root law at the
    entrance time, D31/LCMEAN R14.4 item 5: NOJUMP's root variant of F2b′ and the reviewer's root law);
  - **`SB2LowerRelDriverStatementTWR`** (LIFTSET/SB2LIFT): SB2LIFT's `Lk.SB2LowerRelDriverStatementTW` with the root
    facts exported (D25);
  - **`SB2LowerRangeTWStatement`** (SB2LIFT, D36 (1)): the range identity over the corrected bundle — every proper
    parametrization of the lower walk has the relative walk set as its tail lift (`Lf.IsTailLiftOf`);
* `SB2LowerRelPosWTailStatement` (proved in `SB2CfTail`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cf

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw Lk Mn Mq Restart

/-- **The corrected bundle with the root facts** (D36 with D25): SB2LIFT's `ClauseTW`, LIFTSET's per-stage facts and
root facts. -/
def RelDataClauseW (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (m : ℝ)
    (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ClauseTW κ b jumps P E u l k ω₀ c b' J' m EL ∧ StageFactsAS κ b jumps P E u l k ω₀ c b' J' m EL ∧
    RootFactsAS κ b jumps P E u l k ω₀ c b' J' m EL

section Cond

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → Drv) (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ)
  (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens)

/-- **The conditional half at one launch over the corrected bundle** (`Mv.RelStageCond4` with `RelDataClauseW`). -/
def RelStageCondW : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → Ω → Drv,
    (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
    RelDataClauseW κ b jumps P E u l k ω₀ c b' J' m EL →
    ∀ j, ∀ᵐ ω₁ ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∀ (c₁ : Chart) (θ : ℝ),
        (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω₁)
          (j + 1)).2.2.2.1 j = some (c₁, θ) →
        ∃ (b'' : ℝ → ℝ) (J'' : Finset ℝ) (h'' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b'' J'' ∧
          (∀ ω, IsChartTransport c₁ 1 0 (chiC κ) (affField m one_pos (h' ω)) (h'' ω)) ∧
          IsFlowLineDriver κ b'' J'' θ
            (condExpKernel (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
              (pastSigma κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) EL j) ω₁)
            h'' (fun t ω => (EL j ω).1 t) (fun ω => (EL j ω).2)

/-- **The code match at relative stages of positive lifetime over the corrected bundle** (`Mv.RelStagePos4` with
`RelDataClauseW`). -/
def RelStagePosW (h12p : Theorem12ParamStatement.{u}) (hκ : 0 < κ) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → Ω → Drv,
    (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
    RelDataClauseW κ b jumps P E u l k ω₀ c b' J' m EL →
    ∀ (j : ℕ) (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ (affData 1 m b') (affJumps 1 m J')
        (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
        (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' J' m) EL j β Y →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω)
          (j + 1)).2.2.2.1 j ≠ none → (EL j ω).2 ≠ 0 →
        IsDriverCodeMatch (driverCode h12p hκ (-(Real.pi / 2)) (β ω, Y ω)) (fun t => (EL j ω).1 t) (EL j ω).2

end Cond

/-- **SB2(2)'s conditional half over the corrected bundle** (D36's `CondW`; this packet's Target 2). -/
def SB2LowerRelStageCondWStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    0 < k → RelStageCondW κ b jumps P E u l k ω₀ c b' J' h'

/-- **The positive-lifetime code match over the corrected bundle.** -/
def SB2LowerRelPosWStatement (h12p : Theorem12ParamStatement.{u}) : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    0 < k → ∀ hκ : 0 < κ, RelStagePosW κ b jumps P E u l k ω₀ c b' J' h' h12p hκ

/-- **Named input (SB2LIFT, (L1)/D11 over the corrected bundle): the zero clause.** Almost surely under the retained
kernel, every relative stage `j ≥ 1` that launches has positive lifetime. -/
def SB2LowerZeroClauseWStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → _ → Drv,
      (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      ClauseTW κ b jumps P E u l k ω₀ c b' J' m EL → StageFactsAS κ b jumps P E u l k ω₀ c b' J' m EL →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        StageChainAtZ κ b' J' m EL ω

/-- **The positive-lifetime code match at the tail relative stages `j ≥ 1`** over the corrected bundle. -/
def SB2LowerRelPosWTailStatement (h12p : Theorem12ParamStatement.{u}) : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    0 < k → ∀ hκ : 0 < κ, ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → _ → Drv,
      (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      RelDataClauseW κ b jumps P E u l k ω₀ c b' J' m EL →
      ∀ (j : ℕ), 1 ≤ j → ∀ (β : _ → BoundaryWord) (Y : _ → DistOn upperHalfPlaneOpens),
        IsStageWitness κ (affData 1 m b') (affJumps 1 m J')
          (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
          (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' J' m) EL j β Y →
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
          (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω)
            (j + 1)).2.2.2.1 j ≠ none → (EL j ω).2 ≠ 0 →
          IsDriverCodeMatch (driverCode h12p hκ (-(Real.pi / 2)) (β ω, Y ω)) (fun t => (EL j ω).1 t) (EL j ω).2

/-- **Named input: the code match of a relative root of positive lifetime** over the corrected bundle (the root law
at the entrance time; D31 and LCMEAN's R14.4 item 5, option (A): NOJUMP's root variant of F2b′ with the reviewer's
root law). The relative root always launches (`relRun_one_launches`). -/
def SB2LowerRelPosWRootStatement (h12p : Theorem12ParamStatement.{u}) : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    0 < k → ∀ hκ : 0 < κ, ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → _ → Drv,
      (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      RelDataClauseW κ b jumps P E u l k ω₀ c b' J' m EL →
      ∀ (β : _ → BoundaryWord) (Y : _ → DistOn upperHalfPlaneOpens),
        IsStageWitness κ (affData 1 m b') (affJumps 1 m J')
          (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
          (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' J' m) EL 0 β Y →
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
          (EL 0 ω).2 ≠ 0 →
          IsDriverCodeMatch (driverCode h12p hκ (-(Real.pi / 2)) (β ω, Y ω)) (fun t => (EL 0 ω).1 t) (EL 0 ω).2

/-- **The relative-driver data over the corrected bundle with the root facts** (LIFTSET/SB2LIFT): SB2LIFT's
`Lk.RelDriverAtTW` with LIFTSET's root facts exported (D25), as `Lk.sb2LowerRelDriverStatementTR_of_v5` builds them. -/
def RelDriverAtTWR (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∃ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
    (∀ j, Measurable (EL j)) ∧ (∀ j ω, IsRegularDriver (EL j ω)) ∧ RelDataClauseW κ b jumps P E u l k ω₀ c b' J' m EL

/-- **Named input (LIFTSET/SB2LIFT): SB2(2)'s relative-driver data over the corrected bundle with the root facts.** -/
def SB2LowerRelDriverStatementTWR : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → RelDriverAtTWR κ b jumps P E u l k ω₀ c b' J'

/-- The data with root facts give SB2LIFT's corrected data. -/
theorem sb2LowerRelDriverStatementTW_of_TWR (hD : SB2LowerRelDriverStatementTWR.{u}) :
    SB2LowerRelDriverStatementTW.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hD κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ h₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨EL, hm1, hm2, hTW, hSF, -⟩ := h₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  exact ⟨EL, hm1, hm2, hTW, hSF⟩

/-- **Named input (SB2LIFT, D36 (1)): the range identity over the corrected bundle.** For every measurable,
everywhere regular family with the corrected bundle, almost surely under the retained kernel every proper
parametrization of the lower walk has the relative walk set as its tail lift (the `W` copies of the landed range
lemmas `range_eq_physSet_of_bundles''`, `range_eq_physSet_of_topV`, with `tail` read at connectors through
`Mn.tailArc_of_bundle`). -/
def SB2LowerRangeTWStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → _ → Drv,
      (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      ClauseTW κ b jumps P E u l k ω₀ c b' J' m EL → StageFactsAS κ b jumps P E u l k ω₀ c b' J' m EL →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
          Lf.IsTailLiftOf c (realMax (upperPrefix κ b jumps E u l k ω₀)) m β₀
            (relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω)

end InteractingSLE.Theorem14.SB.Cf
