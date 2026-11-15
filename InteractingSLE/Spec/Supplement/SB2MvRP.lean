/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MvBase
import InteractingSLE.Spec.Supplement.SB2XxPhys
import InteractingSLE.Spec.Supplement.SB2MrCode

/-!
# SB2(2)'s conditional half over the strengthened bundle (D23)

Packet PROVE-SB2-LCMEAN, round 14. D23: SB2LIFT assembled the per-stage chain with the physical domain identity
(`Mn.sb2LowerStageChainStatementWP_of_thms`, from Theorems 1.2–1.3) over LIFTSET's strengthened bundle — the corrected
bundle with the offset fixed to `relOff` (`Mn.ClauseTR`) and the per-stage facts (`Mn.StageFactsAS`); LCMEAN's
per-stage statement consumes it. This file re-types the conditional half over that bundle:

* `RelDataClause4` (`Mn.ClauseTR ∧ Mn.StageFactsAS`), `relDataClause3_of_clause4` (it carries round 12's T bundle);
* `RelStageCond4` / **`SB2LowerRelStageCond4Statement`**: the conditional half over the strengthened bundle;
* the zero clause over it, **`SB2LowerZeroClauseStatement`** (`Mq.StageChainAtZ`, D11's consumer check);
* `SB2LowerStageChainStatementRP4` (R2 chain ∧ physical domain identity ∧ zero clause) and
  **`sb2LowerStageChainStatementRP4_of_zero`**: the first two are SB2LIFT's proved `WP`;
* `RelStagePos4` / **`SB2LowerRelPos4Statement`** (the positive-lifetime code match over the strengthened bundle) and
  **`sb2LowerRelStageCond4Statement_of_pos4`**: the conditional half from it and the zero clause (round 12's argument:
  the relative root of lifetime `0` by `Mr.ae_codeMatch_relRoot_zero`).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mv

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw Lk Mn Mq Restart

/-- **The strengthened bundle** for one relative family (D23): the corrected bundle at the offset `relOff` and the
per-stage facts. -/
def RelDataClause4 (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (m : ℝ)
    (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ClauseTR κ b jumps P E u l k ω₀ c b' J' m EL ∧ StageFactsAS κ b jumps P E u l k ω₀ c b' J' m EL

/-- The strengthened bundle carries round 12's T bundle. -/
theorem relDataClause3_of_clause4 {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ} {ω₀ : Ω} {c : Chart} {b' : ℝ → ℝ} {J' : Finset ℝ} {m : ℝ}
    {EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (h : RelDataClause4 κ b jumps P E u l k ω₀ c b' J' m EL) :
    RelDataClause3 κ b jumps P E u l k ω₀ c b' J' m EL :=
  ClauseTR.clauseT h.1

section Cond

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → Drv) (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ)
  (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens)

/-- **The conditional half at one launch over the strengthened bundle** (`Mq.RelStageCond3` with
`RelDataClause4`). -/
def RelStageCond4 : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → Ω → Drv,
    (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
    RelDataClause4 κ b jumps P E u l k ω₀ c b' J' m EL →
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

/-- **The code match at relative stages of positive lifetime over the strengthened bundle** (`Mr.RelStagePos3` with
`RelDataClause4`). -/
def RelStagePos4 (h12p : Theorem12ParamStatement.{u}) (hκ : 0 < κ) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → Ω → Drv,
    (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
    RelDataClause4 κ b jumps P E u l k ω₀ c b' J' m EL →
    ∀ (j : ℕ) (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ (affData 1 m b') (affJumps 1 m J')
        (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
        (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' J' m) EL j β Y →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω)
          (j + 1)).2.2.2.1 j ≠ none → (EL j ω).2 ≠ 0 →
        IsDriverCodeMatch (driverCode h12p hκ (-(Real.pi / 2)) (β ω, Y ω)) (fun t => (EL j ω).1 t) (EL j ω).2

end Cond

/-- **This packet's target over the strengthened bundle (D23): SB2(2)'s conditional half.** -/
def SB2LowerRelStageCond4Statement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    0 < k → RelStageCond4 κ b jumps P E u l k ω₀ c b' J' h'

/-- **The positive-lifetime code match over the strengthened bundle.** -/
def SB2LowerRelPos4Statement (h12p : Theorem12ParamStatement.{u}) : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    0 < k → ∀ hκ : 0 < κ, RelStagePos4 κ b jumps P E u l k ω₀ c b' J' h' h12p hκ

/-- **The zero clause over the strengthened bundle** (D11's consumer check; SB2LIFT's (L1) route in its handoff
§R27.2 item 2): almost surely under the retained kernel, every relative stage `j ≥ 1` that launches has positive
lifetime. -/
def SB2LowerZeroClauseStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → _ → Drv,
      (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      RelDataClause4 κ b jumps P E u l k ω₀ c b' J' m EL →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        StageChainAtZ κ b' J' m EL ω

/-- **The per-stage statement over the strengthened bundle** (D23): SB2LIFT's R2 chain, the physical domain identity
and the zero clause. -/
def SB2LowerStageChainStatementRP4 : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → _ → Drv,
      (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      RelDataClause4 κ b jumps P E u l k ω₀ c b' J' m EL →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        StageChainAtR2 κ b jumps E u l k ω₀ c b' J' m EL ω ∧ StageChainAtP κ b jumps E u l k ω₀ c b' J' m EL ω ∧
          StageChainAtZ κ b' J' m EL ω

/-- **The per-stage statement over the strengthened bundle from the zero clause** (the R2 chain and the physical
domain identity are SB2LIFT's `Mn.sb2LowerStageChainStatementWP_of_thms`, Theorems 1.2–1.3). -/
theorem sb2LowerStageChainStatementRP4_of_zero (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hZ : SB2LowerZeroClauseStatement.{u}) :
    SB2LowerStageChainStatementRP4.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [sb2LowerStageChainStatementWP_of_thms h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E
      hE hER u l k hu hlp hlθ hL hleft,
    hZ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ hW₀ hZ₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hcl
  filter_upwards [hW₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hcl.1 hcl.2,
    hZ₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hcl] with ω h1 h2
  exact ⟨h1.1, h1.2, h2⟩

/-- **SB2(2)'s conditional half over the strengthened bundle from the positive-lifetime code match and the zero clause**
(round 12's `Mr.sb2LowerRelStageCond3Statement_of_pos3` over `RelDataClause4`). -/
theorem sb2LowerRelStageCond4Statement_of_pos4 (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hZ : SB2LowerZeroClauseStatement.{u})
    (hpos : SB2LowerRelPos4Statement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)) :
    SB2LowerRelStageCond4Statement.{u} := by
  set h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13 with hh12p
  have hPR := Mr.rightWalkProperRegStatement_of_thms h12 h13 h12₀ h13₀
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  have hβP := hPR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER
  filter_upwards [hZ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    hpos κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerTailLiftCurve h13 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 hβP] with ω₀ hZ₀ hP₀ hC₀ hβ₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hcl j
  have hb'' := isPiecewiseConstantBoundaryData_affData (m := m) one_pos hb'
  have hG'' := hG'.affine_finset (m := m) one_pos
  refine Lcd.stageOK_all_of_codeMatch h12p h13 hκ hb'' hG'' (-(Real.pi / 2))
    (fun _ _ _ _ hl => Lv.launch_angle_boundaryWalk hl) hELm hELr (fun j β Y hW => ?_) j
  have hpos' := hP₀ c θ hlaunch b' J' h' hb' hT' hG' hk hκ m hm EL hELm hELr hcl j β Y hW
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · filter_upwards [hpos', Mr.ae_codeMatch_relRoot_zero h12p h13 hκ hb' hG' hELm hELr
      (relDataClause3_of_clause4 hcl) hβ₀ (hC₀ c θ hlaunch b' J' h' hb' hT' hG' m hm) hW] with ω h1 h2 hl
    by_cases hz : (EL 0 ω).2 = 0
    · exact h2 hz
    · exact h1 hl hz
  · filter_upwards [hpos', hZ₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hcl] with ω h1 h2 hl
    by_cases hz : (EL j ω).2 = 0
    · obtain ⟨⟨c₁, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
      exact absurd hz (h2 j c₁ θ' hj hcθ)
    · exact h1 hl hz

end InteractingSLE.Theorem14.SB.Mv
