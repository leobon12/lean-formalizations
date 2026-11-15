/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CfIface

/-!
# SB2(2)'s code match at the tail relative stages over the corrected bundle

Packet PROVE-SB2-CONDFIN (Target 2, D36). **`sb2LowerRelPosWTailStatement_of_canon`**: the positive-lifetime code match
at every relative stage `j ≥ 1` over the corrected bundle `RelDataClauseW` (no `tail`), from

* the `P`-level canonical objects of the tail stages (`Mz.SB2LowerStageCanonStatement`, LIFTSET's joint induction,
  D29/D32; bundle-free);
* the zero clause over the corrected bundle (`SB2LowerZeroClauseWStatement`, SB2LIFT's);
* Theorems 1.2–1.3, which give SB2LIFT's R2 chain and physical domain identity over `ClauseTW`
  (`Mn.sb2LowerStageChainStatementWAP_of_thms`) and this packet's root record (`sb2LowerRootRecRFStatement`).

The proof is LCMEAN's `Mz.sb2LowerRelPos4TailStatement_of_canon` with the bundle replaced: its Q-level core
`Mz.ae_codeMatch_tail_Q` reads the bundle only through the per-stage correspondence (R2, physical identity, zero
clause), the root record and the regularity of the relative launches (from `StageFactsAS`), so field by field the
`tail`-free bundle suffices. R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cf

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw Lk Mx Mn Mq Mz Restart

/-- **SB2(2)'s positive-lifetime code match at the tail relative stages over the corrected bundle**, from the canonical
tail objects, the zero clause and Theorems 1.2–1.3. -/
theorem sb2LowerRelPosWTailStatement_of_canon (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hZ : SB2LowerZeroClauseWStatement.{u})
    (hcan : SB2LowerStageCanonStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)) :
    SB2LowerRelPosWTailStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) := by
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
  have hRP := sb2LowerStageChainStatementWAP_of_thms h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf
    hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hZW := hZ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hrun := Retain.ae_ae_run_eq (upperSpec u l) hRu hm𝒢 (le_refl _)
  have hBregQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 (GW1W.regLaunches_of_stagedPiecesRegular hRl)
  have hUreg := GW1W.regLaunches_of_stagedPiecesRegular hRu
  have hβex := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (Mn.rightWalkProperReg_of_thms h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER)
  have htl := sb2LowerTailLiftCurve h13 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hrootP := sb2LowerRootRecRFStatement h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k
    hu hlp hlθ hL hleft
  filter_upwards [ae_all_iff.2 hlawQ, hcovQ, hidQ, ae_all_iff.2 hoffQ, hRP, hZW, hrun, hBregQ, hUreg, hβex, htl,
    hrootP] with ω₀ hlaw₀ hcov₀ hid₀ hoff₀ hRP₀ hZ₀ hrun₀ hB₀ hU₀ hβ₀ htl₀ hroot₀
  intro c θ hlaunch b' J' h' hb' hT'' hG' hk' hκ' m hm EL hELm hELr hcl j hj β Y hW
  obtain ⟨hTW, hSF, hRF⟩ := hcl
  obtain ⟨Dr₀, hDr₀m, hDr₀r, hroot'⟩ := hroot₀ c θ hlaunch b' J' h' hb' hT'' hG' hk' m hm EL hELm hELr hRF
  have hcN : WalkIntCanon.IsNormalized c := isNormalized_launchChart (upperSpec u l) hU₀ hlaunch
  have hRPQ : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      StageChainAtR2 κ b jumps E u l k ω₀ c b' J' m EL ω ∧ StageChainAtP κ b jumps E u l k ω₀ c b' J' m EL ω ∧
        StageChainAtZ κ b' J' m EL ω := by
    filter_upwards [hRP₀ c θ hlaunch b' J' h' hb' hT'' hG' hk' m hm EL hELm hELr hTW hSF,
      hZ₀ c θ hlaunch b' J' h' hb' hT'' hG' hk' m hm EL hELm hELr hTW hSF] with ω h1 h2
    exact ⟨h1.1, h1.2, h2⟩
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
    filter_upwards [hSF] with ω hf
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

end InteractingSLE.Theorem14.SB.Cf
