/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MzMain
import InteractingSLE.Spec.Supplement.SB2MvRP
import InteractingSLE.Spec.Supplement.SB2WdInd

/-!
# SB2(2)'s code match at the tail relative stages

Packet PROVE-SB2-LCMEAN, round 15 (item 4). **`sb2LowerRelPos4TailStatement_of_canon`**: SB2(2)'s positive-lifetime
code match (`Mv.RelStagePos4`) at every relative stage `j ≥ 1`, over the strengthened bundle. Its inputs:

* the `P`-level canonical objects of the tail stages (`Mz.SB2LowerStageCanonStatement`, the output form of the joint
  induction);
* the root record (`Mz.SB2LowerRootRecStatement`: the record of the relative root is, under the upper kernel, the record
  of a driver known to the marks after B's start stage);
* the zero clause (`Mv.SB2LowerZeroClauseStatement`, SB2LIFT's);
* Theorems 1.2–1.3 (SB2LIFT's per-stage correspondence `Mv.sb2LowerStageChainStatementRP4_of_zero`, the lift curves).

The proof collects, for `P`-almost every upper-past sample, the transfers to the upper kernel (`Mz.ae_ae_isGFF_marksQ`,
`Mz.ae_offset_decided`, `KernelTower.ae_ae_condExpKernel_of_ae`, `Retain.ae_ae_run_eq`) and applies
`Mz.ae_codeMatch_tail_Q`.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mz

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw Lk Mx Mn Mq Mv Restart

/-- **Named statement (the root record)**: in SB2(2)'s setting, for every relative family with the strengthened
bundle, the record of the relative root is, almost surely under the upper kernel, the record of a regular driver
`Dr₀ relOff` known to the marks after B's stage `relOff`. -/
def SB2LowerRootRecStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → _ → Drv,
      (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      RelDataClause4 κ b jumps P E u l k ω₀ c b' J' m EL →
      ∃ Dr₀ : ℕ → _ → Drv, (∀ n, Measurable[Ms.stageMarks κ b jumps E u l k (n + 1)] (Dr₀ n)) ∧
        (∀ n ω, IsRegularDriver (Dr₀ n ω)) ∧
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
          recOf ⊤ (EL 0 ω) = recOf ⊤ (Dr₀ (relOff κ (-(Real.pi / 2)) b jumps
            (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω)) ω)

/-- **The positive-lifetime code match at the tail relative stages** (`Mv.RelStagePos4` for `j ≥ 1`). -/
def SB2LowerRelPos4TailStatement (h12p : Theorem12ParamStatement.{u}) : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    0 < k → ∀ hκ : 0 < κ, ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → _ → Drv,
      (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      RelDataClause4 κ b jumps P E u l k ω₀ c b' J' m EL →
      ∀ (j : ℕ), 1 ≤ j → ∀ (β : _ → BoundaryWord) (Y : _ → DistOn upperHalfPlaneOpens),
        IsStageWitness κ (affData 1 m b') (affJumps 1 m J')
          (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
          (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' J' m) EL j β Y →
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
          (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω)
            (j + 1)).2.2.2.1 j ≠ none → (EL j ω).2 ≠ 0 →
          IsDriverCodeMatch (driverCode h12p hκ (-(Real.pi / 2)) (β ω, Y ω)) (fun t => (EL j ω).1 t) (EL j ω).2

/-- **SB2(2)'s positive-lifetime code match at the tail relative stages**, from the canonical tail objects, the root
record, the zero clause and Theorems 1.2–1.3. -/
theorem sb2LowerRelPos4TailStatement_of_canon (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hZ : SB2LowerZeroClauseStatement.{u})
    (hcan : SB2LowerStageCanonStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13))
    (hroot : SB2LowerRootRecStatement.{u}) :
    SB2LowerRelPos4TailStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  by_cases hk : 0 < k
  swap
  · exact Eventually.of_forall fun ω₀ c θ hlaunch b' J' h' hb' hT' hG' hk' => absurd hk' hk
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hspl : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps
      ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hEu := hE _ hsp
  have hRu := hER _ hsp
  have hEl := hE _ hspl
  have hRl := hER _ hspl
  have hm𝒢 := hEu.2.1 k
  have hT := hcan κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft hk
  choose G cw K x₀ Dr hKc hKp hT' using hT
  have hlawQ := fun n => ae_ae_isGFF_marksQ hb hEu hRu hEl hRl (hT' n).2.2.2.1
  have hcovQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 (ae_all_iff.2 fun n => (hT' n).2.2.2.2.1)
  have hidQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 (ae_all_iff.2 fun n => (hT' n).2.2.2.2.2.2.2)
  have hoffQ := fun o => ae_offset_decided (u := u) (l := l) (k := k) hb hEu hEl hRl o
  have hRP := sb2LowerStageChainStatementRP4_of_zero h12 h13 h12₀ h13₀ hZ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf
    hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hrun := Retain.ae_ae_run_eq (upperSpec u l) hRu hm𝒢 (le_refl _)
  have hBregQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 (GW1W.regLaunches_of_stagedPiecesRegular hRl)
  have hUreg := GW1W.regLaunches_of_stagedPiecesRegular hRu
  have hβex := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (Mn.rightWalkProperReg_of_thms h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER)
  have htl := sb2LowerTailLiftCurve h13 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hrootP := hroot κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [ae_all_iff.2 hlawQ, hcovQ, hidQ, ae_all_iff.2 hoffQ, hRP, hrun, hBregQ, hUreg, hβex, htl,
    hrootP] with ω₀ hlaw₀ hcov₀ hid₀ hoff₀ hRP₀ hrun₀ hB₀ hU₀ hβ₀ htl₀ hroot₀
  intro c θ hlaunch b' J' h' hb' hT'' hG' hk' hκ' m hm EL hELm hELr hcl j hj β Y hW
  obtain ⟨Dr₀, hDr₀m, hDr₀r, hroot'⟩ := hroot₀ c θ hlaunch b' J' h' hb' hT'' hG' hk' m hm EL hELm hELr hcl
  have hcN : WalkIntCanon.IsNormalized c := isNormalized_launchChart (upperSpec u l) hU₀ hlaunch
  have hRPQ := hRP₀ c θ hlaunch b' J' h' hb' hT'' hG' hk' m hm EL hELm hELr hcl
  have hupQ : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      upperPrefix κ b jumps E u l k ω = upperPrefix κ b jumps E u l k ω₀ ∧ ω ∈ upperLaunchSet κ b jumps E u l k := by
    filter_upwards [hrun₀] with ω hω
    refine ⟨?_, ?_⟩
    · show SB.prefixPhysSet κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) k ∪ _ =
        SB.prefixPhysSet κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) k ∪ _
      unfold SB.prefixPhysSet
      rw [hω]
    · show (ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) (k + 1)).2.2.2.1 k ≠ none
      rw [launches_run_succ_of_run_eq (upperSpec u l) hω, hlaunch]
      exact Option.some_ne_none _
  have hELregQ : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      SB.LuM.RegLaunches κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω) := by
    filter_upwards [hcl.2] with ω hf
    exact Mn.regLaunches_of_facts (fun j => hELr j ω) (fun j hl hz => (hf j hl hz).1.2.2.2.2.2.2)
  have hRmemQ : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ((realMax (upperPrefix κ b jumps E u l k ω₀) : ℝ) : ℂ) ∈
        ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω) := by
    filter_upwards [hβ₀, htl₀ c θ hlaunch b' J' h' hb' hT'' hG' m hm] with ω hβω htlω
    obtain ⟨β₀, hβ, hβ0, hβr⟩ := hβω
    obtain ⟨tL, γ, hγ⟩ := htlω β₀ hβ hβ0 hβr
    rw [← hγ.1]
    have hmem : β₀ tL ∈ range β₀ := mem_range_self tL
    rw [hβr] at hmem
    exact hmem
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · refine Eventually.of_forall fun ω hl _ => absurd (GW1W.even_of_launches_walk hl).1 ?_
    have : j = 1 := by omega
    subst this
    decide
  have hmain := ae_codeMatch_tail_Q (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h13 hκ' hb
    hh.1 hEu hEl hcN hb' hT'' hG'.1 hELm hELr hRPQ hupQ hB₀ hELregQ hRmemQ hKc hKp
    (fun n => (hT' n).1) (fun n => (hT' n).2.1) (fun n => (hT' n).2.2.1) (fun n => (hT' n).2.2.2.2.2.1)
    (fun n => (hT' n).2.2.2.2.2.2.1) hlaw₀ hcov₀ hid₀ hoff₀ hDr₀m hDr₀r hroot' hj2 hW
  filter_upwards [hmain] with ω h1 hl _
  exact h1 hl

end InteractingSLE.Theorem14.SB.Mz
