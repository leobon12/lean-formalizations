/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2aConnWitness
import InteractingSLE.Spec.Supplement.GW1ActiveLaw

/-!
# GW2a's connectors: one stage of an arbitrary program, almost surely

Packet PROVE-GW2A-CONN. For a staged history of a boundary-continued program (gw2 flag `false`) with measurable drivers
regular at every sample, and the witness `(β, Y)` of the staged conditional law at a launch `ℓ` (PROVE-STAGEDLAW,
`IsStageWitness`) whose word satisfies the run invariant `Inv` almost surely at launches, almost surely at a launch at
`ℓ` (`ae_stage`):

* the record of the piece is good when its stop is finite;
* if the piece ends at a right threshold, the original height outward of the new right record is low and the left seed
  stays open (`markPosL(0) < 0`, read from the record); the mirror at a left threshold;
* a launch from a threshold status does not have zero lifetime (the conditional word's seed is the admissible seed
  of the program's heights: `admissible_word_of_thr_true/false`; a flow line with an admissible seed has positive
  lifetime, `GW0.lifetime_eq_zero_iff`).

All four are measurable events, so they pass from "almost surely under almost every regular conditional law given the
retained past" to "almost surely" (`Sec5.Lemma56Stages.ae_of_ae_condExpKernel`); the pathwise arguments under the
conditional law are `stopWord_facts_right/left`, `markPosL_neg_of_right_hit`, `markPos_pos_of_left_hit` and the run
invariant at the conditioning sample.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2aConn

open Exist Exist.StagedLaw Exist.Staged Restart LQGMetric GW1W
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The good event of a stage (all four clauses are measurable). -/
def StageGood (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ℓ : ℕ)
    (ω : Ω) : Prop :=
  (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
    (min (instrTime spec ℓ) (E ℓ ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf (instrTime spec ℓ) (E ℓ ω)))) ∧
    (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)) = stThr (some true) →
      rightLim b (stRecR (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1))) +
          instrAngle spec ℓ * chiC κ ≤ -sleLambda κ ∧
        markPosL (rdrv (recOf (instrTime spec ℓ) (E ℓ ω))) (rtime (recOf (instrTime spec ℓ) (E ℓ ω))) 0 < 0) ∧
    (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)) = stThr (some false) →
      sleLambda κ ≤ leftLim b (stRecL (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1))) +
          instrAngle spec ℓ * chiC κ ∧
        0 < markPos (rdrv (recOf (instrTime spec ℓ) (E ℓ ω))) (rtime (recOf (instrTime spec ℓ) (E ℓ ω))) 0) ∧
    (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) = stThr (some true) ∨
        stStatus (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) = stThr (some false) →
      (E ℓ ω).2 ≠ 0)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem measurableSet_stageGood (hb : IsPiecewiseConstantBoundaryData b jumps) (hEm : ∀ j, Measurable (E j))
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (ℓ : ℕ) :
    MeasurableSet {ω | StageGood κ b jumps spec E ℓ ω} := by
  have hMS := isMeasState_run (κ := κ) hb spec hEm hreg (ℓ + 1)
  have hMS₀ := isMeasState_run (κ := κ) hb spec hEm hreg ℓ
  have hLp := measurableSet_launch_self (κ := κ) (b := b) (jumps := jumps) (spec := spec) runMeasStatement hb
    (k := ℓ) (fun j _ => hEm j) (fun j _ => hreg j)
  set t := instrTime spec ℓ with ht
  have hrec : Measurable fun ω => recOf t (E ℓ ω) := measurable_recOf (hEm ℓ) (hreg ℓ) t
  have hWm : ∀ x : ℝ, Measurable fun ω => rdrv (recOf t (E ℓ ω)) x := fun x => (measurable_rdrv_apply x).comp hrec
  have hτ : Measurable fun ω => rtime (recOf t (E ℓ ω)) := measurable_rtime.comp hrec
  have hmL : Measurable fun ω => markPosL (rdrv (recOf t (E ℓ ω))) (rtime (recOf t (E ℓ ω))) 0 :=
    measurable_markPosL (fun ω => continuous_rdrv _) hWm (fun ω => rdrv_zero _) hτ (fun ω => rtime_nonneg _)
      measurable_const
  have hmR : Measurable fun ω => markPos (rdrv (recOf t (E ℓ ω))) (rtime (recOf t (E ℓ ω))) 0 :=
    measurable_markPos (fun ω => continuous_rdrv _) hWm (fun ω => rdrv_zero _) hτ (fun ω => rtime_nonneg _)
      measurable_const
  have hζ : Measurable fun ω => (E ℓ ω).2 := measurable_snd.comp (hEm ℓ)
  have h1 : MeasurableSet {ω | min t (E ℓ ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf t (E ℓ ω)))} :=
    ((measurableSet_eq_fun (measurable_const.min hζ) measurable_const).union
      (measurableSet_good t (hEm ℓ) (hreg ℓ))).congr (by ext ω; simp only [mem_union, mem_ofPred_eq]; tauto)
  have hR : Measurable fun ω => rightLim b (stRecR (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1))) +
      instrAngle spec ℓ * chiC κ := ((measurable_rightLim_of_pcbd hb).comp hMS.2.2.2.1).add_const _
  have hL : Measurable fun ω => leftLim b (stRecL (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1))) +
      instrAngle spec ℓ * chiC κ := ((measurable_leftLim_of_pcbd hb).comp hMS.2.2.2.2.1).add_const _
  have h2 := ((hMS.1 (stThr (some true))).compl.union
    ((measurableSet_le hR (measurable_const (a := -sleLambda κ))).inter
      (measurableSet_lt hmL (measurable_const (a := (0 : ℝ))))))
  have h3 := ((hMS.1 (stThr (some false))).compl.union
    ((measurableSet_le (measurable_const (a := sleLambda κ)) hL).inter
      (measurableSet_lt (measurable_const (a := (0 : ℝ))) hmR)))
  have h4 := (((hMS₀.1 (stThr (some true))).union (hMS₀.1 (stThr (some false)))).compl.union
    (measurableSet_eq_fun hζ (measurable_const (a := (0 : ℝ≥0∞)))).compl)
  exact (hLp.compl.union (h1.inter (h2.inter (h3.inter h4)))).congr
    (by ext ω; simp only [mem_union, mem_compl_iff, mem_inter_iff, mem_ofPred_eq, StageGood]; tauto)

/-- **One stage of an arbitrary program, almost surely** (Lemma GW1/GW2a: the conditional flow line at a launch; the
right threshold's low start and open left seed; no zero lifetime for a launch from a threshold). -/
theorem ae_stage (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hgw : spec.2.1 = false) (hE : IsStagedHistory κ b jumps P h spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {ℓ : ℕ} {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h spec E ℓ β Y)
    (hinv : ∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps spec (fun j => E j ω₀) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      Inv κ b jumps (β ω₀) (ExplState.run κ b jumps spec (fun j => E j ω₀) ℓ)) :
    ∀ᵐ ω ∂P, StageGood κ b jumps spec E ℓ ω := by
  have h𝒢 : pastSigma κ b jumps spec E ℓ ≤ mΩ := hE.2.1 ℓ
  have hLp := measurableSet_pastSigma_launch (κ := κ) hb spec hE.1 hreg ℓ
  refine Sec5.Lemma56Stages.ae_of_ae_condExpKernel h𝒢 (measurableSet_stageGood hb hE.1 hreg ℓ) ?_
  filter_upwards [ae_isFlowLineDriver_stage hκ hb hh hE hreg hW, hinv,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem h𝒢 hLp.compl] with ω₀ hfl₀ hinv₀ hmemc
  by_cases hl₀ : (ExplState.run κ b jumps spec (fun j => E j ω₀) (ℓ + 1)).2.2.2.1 ℓ ≠ none
  swap
  · filter_upwards [hmemc hl₀] with ω hω hlω
    exact absurd hlω hω
  obtain ⟨⟨h', hfl⟩, hrunK⟩ := hfl₀ hl₀
  have hI := hinv₀ hl₀
  set θ := instrAngle spec ℓ with hθdef
  set t := instrTime spec ℓ with htdef
  set s₀ := ExplState.run κ b jumps spec (fun j => E j ω₀) ℓ with hs₀
  obtain ⟨⟨c₀, θ₀⟩, hcθ₀⟩ := Option.ne_none_iff_exists'.1 hl₀
  obtain ⟨hspec, -, -⟩ := eq_launch_of_launches spec (fun j => E j ω₀) hcθ₀
  have hθ₀ : θ = θ₀ := by rw [hθdef]; unfold instrAngle; rw [hspec]
  have hfs : (ExplState.flowStep κ b false s₀ ℓ (E ℓ ω₀) θ t).2.2.2.1 ℓ ≠ none := by
    have h1 := hl₀
    rw [run_succ, hspec] at h1
    rw [hθ₀]
    rw [← hgw]
    exact h1
  have hs0 : s₀.2.2.2.1 ℓ = none := launches_run_of_le spec _ le_rfl
  have hfl' := hfl
  obtain ⟨_, 𝓕, VL, VR, B, -, hC⟩ := hfl'
  have hEv := hC.1
  filter_upwards [hEv.ae_isIntegratedSLEPath, hEv.ae_tendsto_threshold hκ,
    ae_isDrvGood_of_isFlowLineDriver hκ t (hreg ℓ) hfl, hrunK] with ω hp hthr hgood hrun
  intro hlω
  have hR1 : ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1) = ExplState.launch s₀ ℓ (E ℓ ω) θ t := by
    obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlω
    obtain ⟨hspec', hrun', -⟩ := eq_launch_of_launches spec (fun j => E j ω) hcθ
    have hθ' : θ' = θ₀ := by
      rw [hspec] at hspec'
      simp only [Option.some.injEq, Sum.inl.injEq, Prod.mk.injEq] at hspec'
      exact hspec'.1.symm
    rw [hrun', hrun, hθ', ← hθ₀]
  rw [hR1, hrun]
  -- the good stop path at a finite positive lifetime
  have hgpOf : ∀ (hfin : min t (E ℓ ω).2 ≠ ⊤), (E ℓ ω).2 ≠ 0 →
      IsGoodStopPath κ (flowLineXL (β ω₀).fn (β ω₀).jumps 0) (flowLineXR (β ω₀).fn (β ω₀).jumps 0)
        (flowLineRhoL κ (β ω₀).fn (β ω₀).jumps 0 θ) (flowLineRhoR κ (β ω₀).fn (β ω₀).jumps 0 θ) t (E ℓ ω)
        (fun i s => VL i s ω) (fun j s => VR j s ω) (fun s => B s ω) := fun hfin h0 => by
    refine ⟨hp, fun T hT hζ => ?_, hreg ℓ ω, hgood hfin, hfin, pos_iff_ne_zero.2 h0⟩
    obtain ⟨w₀, vL₀, vR₀, hlim, -⟩ := hthr T hT hζ
    exact ⟨w₀, vL₀, vR₀, hlim⟩
  have hfinOf : ∀ st, st ≠ stDone → stStatus (ExplState.launch s₀ ℓ (E ℓ ω) θ t) = st →
      min t (E ℓ ω).2 ≠ ⊤ := fun st hst h htop => by
    rw [(launch_eq_of_top s₀ ℓ (E ℓ ω) θ t htop).2.2.2.2.1] at h
    exact hst h.symm
  refine ⟨fun hfin => hgood hfin, fun hst => ?_, fun hst => ?_, fun hst => ?_⟩
  · -- a right threshold
    have hfin := hfinOf _ (by simp [stThr, stDone]) hst
    obtain ⟨hnt, h0, ⟨x₀, hx₀, hhit₀, hdead₀⟩, -, -⟩ := launch_thr_true_gen hfin hst
    have hle : (E ℓ ω).2 ≤ t := not_lt.1 hnt
    have hgd := hgood hfin
    have hgp := hgpOf hfin h0
    have hWr : rdrv (recOf t (E ℓ ω)) = stopDrv t (E ℓ ω) := by
      rw [rdrv_recOf]; exact recDrv_eq_stopDrv (hreg ℓ ω) hgd
    have hrt : rtime (recOf t (E ℓ ω)) = stopTime t (E ℓ ω) := rtime_recOf t _
    have hy₀ : 0 < rProf (stChart s₀) x₀ := hI.1.2.1.2 x₀ hx₀
    have hc₀ : (stChart s₀).1 x₀ = (rProf (stChart s₀) x₀ : ℂ) := hI.1.1.eq_ofReal x₀
    have hal : ∀ r < rtime (recOf t (E ℓ ω)), ∃ u,
        IsForwardSol (rdrv (recOf t (E ℓ ω))) (rProf (stChart s₀) x₀ : ℂ) r u := by
      rw [hWr, hrt, ← hc₀]; exact hhit₀
    have hde : ¬ ∃ u, IsForwardSol (rdrv (recOf t (E ℓ ω))) (rProf (stChart s₀) x₀ : ℂ)
        (rtime (recOf t (E ℓ ω))) u := by
      rw [hWr, hrt, ← hc₀]; exact hdead₀
    obtain ⟨⟨ε, hε, hlow⟩, -⟩ := stopWord_facts_right hκ hgp hle hy₀ hal hde
    have hG := gInv_launch hκ hb hI.1 ℓ θ t (hreg ℓ ω) hgd hfin
    have hsmall := rSmall_launch hI.1 ℓ θ t (hreg ℓ ω) hgd hfin ⟨x₀, hx₀, hhit₀, hdead₀⟩
    have hs₁R : RProf (ExplState.launch s₀ ℓ (E ℓ ω) θ t) := ⟨hG.1, hG.2.1.1, hG.2.1.2, hsmall⟩
    exact ⟨rightLim_le_of_lowStart hb hs₁R hG.2.2.2.1 hε hlow, markPosL_neg_of_right_hit hgp hle hy₀ hal hde⟩
  · -- a left threshold
    have hfin := hfinOf _ (by simp [stThr, stDone]) hst
    obtain ⟨hnt, h0, ⟨x₀, hx₀, hhit₀, hdead₀⟩, -, -⟩ := launch_thr_false_gen hfin hst
    have hle : (E ℓ ω).2 ≤ t := not_lt.1 hnt
    have hgd := hgood hfin
    have hgp := hgpOf hfin h0
    have hWr : rdrv (recOf t (E ℓ ω)) = stopDrv t (E ℓ ω) := by
      rw [rdrv_recOf]; exact recDrv_eq_stopDrv (hreg ℓ ω) hgd
    have hrt : rtime (recOf t (E ℓ ω)) = stopTime t (E ℓ ω) := rtime_recOf t _
    have hy₀ : rProf (stChart s₀) x₀ < 0 := rProf_neg_of_lProf hI.1.2.2.1.2 hx₀
    have hc₀ : (stChart s₀).1 x₀ = (rProf (stChart s₀) x₀ : ℂ) := hI.1.1.eq_ofReal x₀
    have hal : ∀ r < rtime (recOf t (E ℓ ω)), ∃ u,
        IsForwardSol (rdrv (recOf t (E ℓ ω))) (rProf (stChart s₀) x₀ : ℂ) r u := by
      rw [hWr, hrt, ← hc₀]; exact hhit₀
    have hde : ¬ ∃ u, IsForwardSol (rdrv (recOf t (E ℓ ω))) (rProf (stChart s₀) x₀ : ℂ)
        (rtime (recOf t (E ℓ ω))) u := by
      rw [hWr, hrt, ← hc₀]; exact hdead₀
    obtain ⟨⟨ε, hε, hhigh⟩, -⟩ := stopWord_facts_left hκ hgp hle hy₀ hal hde
    have hG := gInv_launch hκ hb hI.1 ℓ θ t (hreg ℓ ω) hgd hfin
    have hsmall := lSmall_launch hI.1 ℓ θ t (hreg ℓ ω) hgd hfin ⟨x₀, hx₀, hhit₀, hdead₀⟩
    have hs₁L : LProf (ExplState.launch s₀ ℓ (E ℓ ω) θ t) := ⟨hG.1, hG.2.2.1.1, hG.2.2.1.2, hsmall⟩
    exact ⟨leftLim_ge_of_highStart hb hs₁L hG.2.2.2.2.1 hε hhigh, markPos_pos_of_left_hit hgp hle hy₀ hal hde⟩
  · -- a launch from a threshold has positive lifetime
    have hne1 : stStatus s₀ ≠ .inl () := by rcases hst with h | h <;> rw [h] <;> simp [stThr]
    have hne2 : stStatus s₀ ≠ .inr (.inl ()) := by rcases hst with h | h <;> rw [h] <;> simp [stThr]
    have hadm := admissible_of_flowStep_launch s₀ ℓ (E ℓ ω₀) θ t hs0 hfs hne1 hne2
    have hadmW : ExplState.IsAdmissibleSeed κ (leftLim (β ω₀).fn 0) (rightLim (β ω₀).fn 0) θ := by
      rcases hst with h | h
      · exact admissible_word_of_thr_true hb hI h hadm
      · exact admissible_word_of_thr_false hb hI h hadm
    intro h0
    exact ((GW1.thresholdCondition_flowLine_zero_iff hκ _ _ θ).1 ((GW0.lifetime_eq_zero_iff hp).1 h0)) hadmW

/-! ### The run invariant at every launch and every living state -/

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem heights_default (s : ExplState) (h1 : stStatus s ≠ stThr (some true)) (h2 : stStatus s ≠ stThr (some false)) :
    ExplState.heights κ b s = (leftLim b (stPt s), rightLim b (stPt s)) := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  rcases st with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | o | ⟨r, m⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · rfl
  · rfl
  · rcases o with _ | r
    · rfl
    · cases r
      · exact absurd rfl h2
      · exact absurd rfl h1
  · rfl
  · rfl
  · rfl

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem launch_zero_from_tip {s : ExplState} {k : ℕ} {D : (ℝ≥0 → ℝ) × ℝ≥0∞} {θ : ℝ} {t : ℝ≥0∞} (h0 : D.2 = 0)
    (hst : stStatus s = .inr (.inl ())) : stStatus (ExplState.launch s k D θ t) ≠ stThr none := by
  have hfin : min t D.2 ≠ ⊤ := by rw [h0, min_eq_right zero_le]; exact ENNReal.zero_ne_top
  obtain ⟨-, -, -, -, hst', -⟩ := launch_eq_of_ne_top s k D θ t hfin
  rw [hst']
  unfold lStatus
  have hnt : ¬ t < D.2 := by rw [h0]; exact not_lt.2 zero_le
  rw [ite_eq_right_of_eq_false _ _ (eq_false hnt), ite_eq_left_of_eq_true _ _ (eq_true h0), hst]
  simp [stDead, stThr]

/-- **The run invariant at every launch and at every living state** (Lemma GW1's classification for an arbitrary
boundary-continued program): for every instruction `k` there are witnesses of the staged conditional law at the launch
and at the state `k` whose words satisfy `Inv` almost surely (at a launch at `k`, resp. at a living state `k`). -/
theorem exists_inv (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hgw : spec.2.1 = false) (hx₀ : spec.1 = 0)
    (hE : IsStagedHistory κ b jumps P h spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω)) :
    ∀ k, ∃ (βs : Ω → BoundaryWord) (Ys : Ω → DistOn upperHalfPlaneOpens) (βt : Ω → BoundaryWord)
      (Yt : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h spec E k βs Ys ∧ IsStateWitness κ b jumps P h spec E k βt Yt ∧
      ∀ᵐ ω ∂P, ((ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
          Inv κ b jumps (βs ω) (ExplState.run κ b jumps spec (fun j => E j ω) k)) ∧
        (IsLive (ExplState.run κ b jumps spec (fun j => E j ω) k) →
          Inv κ b jumps (βt ω) (ExplState.run κ b jumps spec (fun j => E j ω) k)) := by
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨fun _ => BoundaryWord.shiftW spec.1 c₀, fun ω => flowField spec.1 0 (h ω), fun _ => default,
        fun _ => 0, isStageWitness_zero hh hc₀J hc₀, ⟨measurable_const, measurable_const, ?_, ?_⟩,
        Eventually.of_forall fun ω => ⟨fun _ => ?_, fun hl => ?_⟩⟩
      · exact Eventually.of_forall fun ω hl => absurd (rfl : stStatus (ExplState.init spec.1) = .inl ()) hl.2
      · exact Eventually.of_forall fun ω hl => absurd (rfl : stStatus (ExplState.init spec.1) = .inl ()) hl.2
      · change Inv κ b jumps (BoundaryWord.shiftW spec.1 c₀) (ExplState.init spec.1)
        rw [hx₀]
        exact inv_init hc₀J hc₀
      · exact absurd (rfl : stStatus (ExplState.init spec.1) = .inl ()) hl.2
    have H : ∀ ℓ, ∃ (βs : Ω → BoundaryWord) (Ys : Ω → DistOn upperHalfPlaneOpens) (βt : Ω → BoundaryWord)
        (Yt : Ω → DistOn upperHalfPlaneOpens), ℓ < k →
        IsStageWitness κ b jumps P h spec E ℓ βs Ys ∧ IsStateWitness κ b jumps P h spec E ℓ βt Yt ∧
        ∀ᵐ ω ∂P, ((ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
            Inv κ b jumps (βs ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ)) ∧
          (IsLive (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) →
            Inv κ b jumps (βt ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ)) := by
      intro ℓ
      by_cases hℓ : ℓ < k
      · obtain ⟨βs, Ys, βt, Yt, hW⟩ := ih ℓ hℓ
        exact ⟨βs, Ys, βt, Yt, fun _ => hW⟩
      · exact ⟨fun _ => default, fun _ => 0, fun _ => default, fun _ => 0, fun h' => absurd h' hℓ⟩
    choose βs Ys βt Yt hWI using H
    obtain ⟨βs', Ys', hWs', hexs⟩ := isStageWitness_succ_expl (isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb
      hh hk (fun j _ => hE.1 j) (fun j _ => hreg j) (fun j _ => hE.2.2.2 j) βs Ys fun ℓ hℓ => (hWI ℓ hℓ).1
    obtain ⟨βt', Yt', hWt', hext⟩ := stateWitness_succ_expl (isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb
      hh (fun j _ => hE.1 j) (fun j _ => hreg j) (fun j _ => hE.2.2.2 j) βs Ys fun ℓ hℓ => (hWI ℓ hℓ).1
    refine ⟨βs', Ys', βt', Yt', hWs', hWt', ?_⟩
    have hall : ∀ᵐ ω ∂P, ∀ ℓ, ℓ < k →
        ((ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
          Inv κ b jumps (βs ℓ ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ)) ∧
        StageGood κ b jumps spec E ℓ ω := by
      refine ae_all_iff.2 fun ℓ => ?_
      by_cases hℓ : ℓ < k
      · filter_upwards [(hWI ℓ hℓ).2.2, ae_stage hκ hb hh hgw hE hreg (hWI ℓ hℓ).1
          ((hWI ℓ hℓ).2.2.mono fun ω hω => hω.1)] with ω h1 h2 _ using ⟨h1.1, h2⟩
      · exact Eventually.of_forall fun ω h' => absurd h' hℓ
    filter_upwards [hall] with ω hω
    -- the invariant at `k` from the last launch `ℓ`
    have core : ∀ ℓ, ℓ < k → (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        (∀ j, ℓ < j → j < k → (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = none) →
        min (instrTime spec ℓ) (E ℓ ω).2 ≠ ⊤ →
        ¬ IsTerminal (ExplState.run κ b jumps spec (fun j => E j ω) k) →
        Inv κ b jumps (BoundaryWord.shiftW (((ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.2.1.1 0 -
          (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.1 0).re)
          (stopWord κ (βs ℓ ω, instrAngle spec ℓ, pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ))))
          (ExplState.run κ b jumps spec (fun j => E j ω) k) := by
      intro ℓ hℓk hl hn hstop hnT
      obtain ⟨hinvℓ, hgoodℓ⟩ := hω ℓ hℓk
      have hI := hinvℓ hl
      obtain ⟨⟨c', θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
      obtain ⟨hspec, hrun1, -⟩ := eq_launch_of_launches spec (fun j => E j ω) hcθ
      have hθ : instrAngle spec ℓ = θ' := by unfold instrAngle; rw [hspec]
      rw [pastMap_last_of_launch hl, hθ]
      obtain ⟨hg1, hg2, hg3, hg4⟩ := hgoodℓ hl
      set s := ExplState.run κ b jumps spec (fun j => E j ω) ℓ with hs
      set t := instrTime spec ℓ with ht
      have hfs : (ExplState.flowStep κ b false s ℓ (E ℓ ω) θ' t).2.2.2.1 ℓ ≠ none := by
        have h1 := hl
        rw [run_succ, hspec] at h1
        rw [← hgw]
        exact h1
      have hs0 : s.2.2.2.1 ℓ = none := launches_run_of_le spec _ le_rfl
      have hI1 : Inv κ b jumps (stopWord κ (βs ℓ ω, θ', recOf t (E ℓ ω)))
          (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)) := by
        rw [hrun1]
        refine inv_launch hκ hb hI ℓ θ' t (hreg ℓ ω) (hg1 hstop) hstop (fun h => ?_) (fun h => ?_) (fun h => ?_)
        · have h2 := hg2
          rw [hrun1, hθ] at h2
          exact h2 h
        · have h3 := hg3
          rw [hrun1, hθ] at h3
          exact h3 h
        · obtain ⟨h0, -, -⟩ := launch_thr_none_gen hstop h
          by_cases hroot : stStatus s = .inl ()
          · exact Or.inl hroot
          by_cases htip : stStatus s = .inr (.inl ())
          · exact absurd h (launch_zero_from_tip h0 htip)
          by_cases hthr : stStatus s = stThr (some true) ∨ stStatus s = stThr (some false)
          · exact absurd h0 (hg4 hthr)
          push Not at hthr
          right
          have hadm := admissible_of_flowStep_launch s ℓ (E ℓ ω) θ' t hs0 hfs hroot htip
          rwa [heights_default s hthr.1 hthr.2] at hadm
      have hbetw := inv_run_between hb spec hgw (fun j => E j ω) hI1 (k - (ℓ + 1))
        (fun j hj hjk => hn j hj (by omega)) (by rw [show ℓ + 1 + (k - (ℓ + 1)) = k by omega]; exact hnT)
      rw [show ℓ + 1 + (k - (ℓ + 1)) = k by omega] at hbetw
      exact hbetw
    refine ⟨fun hlk => ?_, fun hlive => ?_⟩
    · obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlk
      obtain ⟨ℓ, hℓk, ⟨c', θ', hl'⟩, hstop, hn, -⟩ := exists_last_launch spec (fun j => E j ω) hk hcθ
      have hl : (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by rw [hl']; simp
      have hnT : ¬ IsTerminal (ExplState.run κ b jumps spec (fun j => E j ω) k) := fun hT => by
        rw [(isTerminal_run_of_le spec _ hT k le_rfl).2] at hcθ
        exact absurd hcθ (by simp)
      rw [hexs ℓ ω hℓk hlk hl hn]
      exact core ℓ hℓk hl hn hstop hnT
    · obtain ⟨ℓ, hℓk, ⟨c', θ', hl'⟩, hstop, hn, -⟩ := exists_last_launch_of_live spec (fun j => E j ω) hlive
      have hl : (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by rw [hl']; simp
      rw [hext ℓ ω hℓk hlive hl hn]
      exact core ℓ hℓk hl hn hstop hlive.1

end GW2aConn

end Theorem14

end InteractingSLE
