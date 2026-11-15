/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2StmStepSample
import InteractingSLE.Spec.Supplement.GW2StmPairEq
import InteractingSLE.Spec.Supplement.GW2StmRun
import InteractingSLE.Spec.Supplement.GB6PastStep
import InteractingSLE.Spec.Supplement.GW2SchedRuleGB6
import InteractingSLE.Spec.Supplement.GB6LMeanFinal
import InteractingSLE.Spec.Supplement.LPProbExtract

/-!
# GW2's stage step, part 12: GW1's inductive step with GB6's equality (`GB6StagedEqStepStatement`)

Packet PROVE-GW2-STAGEMEAN, step round. **`gb6StagedEqStepStatement_of_thm12_thm13`** proves the named input
`GW2TipSystem.GB6StagedEqStepStatement` (PROVE-GW2-SCHED) from Theorems 1.2–1.3 (R48: Theorem 1.4 may use them): at
almost every sample carrying GB6's equality datum (`GW2TipSystem.HasLaunchPairEq`: the conditional counterflow of the
field read in the launch chart is the original counterflow before its first visit of the retained prefix, up to a
measurable time change) at launch `j`, almost every sample of the conditional law given the retained past carries the
datum at launch `j + 1`.

The proof is `GW2Later.gb6PastStepStatement_of_prefix` (the containment step) with the time change kept:

1. as there, under the conditional law `ν` given the past before `j` the past is that of the launching sample, the field
   read in the launch chart is a GFF whose flow line is the piece launched at `j`, and the datum at `j` gives the
   conditional counterflow `W_k` with its clock `ℓ_k`; the kernel of a kernel identifies `condExpKernel ν σ(g)` with
   the conditional law given the past before `j + 1`;
2. GB6 conditioned on the piece's record, equality form (`GW2Stm.exists_prefixPairEq`, in the world `ν`), gives the new
   counterflow `W₂`, the measurable time change `ℓ₂` onto the times before the first contact `T_c` of `W_k` with the
   piece, and the tip relation through the piece's Loewner chart;
3. at each sample, `GW2Stm.isPrefixClock_step` composes the clocks (`ℓ_k ∘ ℓ₂`), using the fibre property of the launch
   chart (`GW1Z.chartFiber_run`) and the identification of `T_c` with the first visit of the piece's physical tips
   (`GW2Stm.firstTipTime_piece_eq`); the retained prefix grows by the piece (`GW2Stm.contactSet_succ`) and does not
   depend on the sample of equal records (`GW2Stm.contactSet_eq_of_recOf_eq`);
4. the composed clock is measurable through rational times (`GW2Stm.evalQ`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Stm

open CounterflowRange GW2Schedule GW2aMulti GW2Sched GW2Later Exist.StagedLaw Exist.Staged GW1LaunchClock GW2TipSystem

/-- **GW1's inductive step with GB6's equality, from Theorems 1.2–1.3.** -/
theorem gb6StagedEqStepStatement_of_thm12_thm13 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) : GB6StagedEqStepStatement.{u} := by
  have hD := Supp8.GB6LMean.gb6HullDetStatement_of_thm12_thm13 h12 h13
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER x hx l hlθ hlt j
  have hbc := isBoundaryContinuedProgram_scheduleProgram hlθ 0
  have hS := hE ⟨x, true, scheduleProgram 0 l⟩ hbc
  have hR := hER ⟨x, true, scheduleProgram 0 l⟩ hbc
  set spec : ExplSpec := ⟨x, true, scheduleProgram 0 l⟩ with hspec
  set E' := E spec with hE'
  have hgw : spec.2.1 = true := rfl
  have hprog : IsFlowProg spec.2.2 (schedAngle l) (schedDelta 0 l) := isFlowProg_scheduleProgram 0 l
  have hΔ : ∀ i, schedDelta 0 l i ≠ ⊤ := schedDelta_ne_top 0 l
  by_cases hj : j < spec.2.2.length
  swap
  · refine Eventually.of_forall fun ω₀ _ => Eventually.of_forall fun ω _ _ c θ hl => ?_
    rw [launches_run_succ_of_length_le κ b jumps spec _ (by omega)] at hl
    exact absurd hl (by simp)
  have hlen_le : j ≤ spec.2.2.length := hj.le
  have hpm : ∀ k, Measurable[pastSigma κ b jumps spec E' k] (pastMap κ b jumps spec E' k) := fun k s hs => by
    rw [pastSigma_eq_comap]
    exact ⟨s, hs, rfl⟩
  have hpmΩ : Measurable (pastMap κ b jumps spec E' (j + 1)) := (hpm (j + 1)).mono (hS.2.1 (j + 1)) le_rfl
  have hcg : @MeasurableSpace.CountablyGenerated Ω (pastSigma κ b jumps spec E' (j + 1)) := by
    rw [pastSigma_eq_comap]
    exact MeasurableSpace.CountablyGenerated.comap _
  set g : Ω → RecData := fun ω => pastMap κ b jumps spec E' (j + 1) ω (Fin.last j) with hgdef
  have hgm : Measurable g := (measurable_pi_apply _).comp hpmΩ
  have hθj : schedAngle l j ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    schedAngle_mem_Icc hlθ (by rwa [← length_scheduleProgram 0 l])
  have hallSucc : ∀ ω ω', pastMap κ b jumps spec E' j ω = pastMap κ b jumps spec E' j ω' →
      AllSucc (schedDelta 0 l) (fun i => E' i ω') j → AllSucc (schedDelta 0 l) (fun i => E' i ω) j :=
    fun ω ω' he hs' => by
      rw [allSucc_iff_flags hgw hprog hΔ E' hlen_le ω, he]
      exact (allSucc_iff_flags hgw hprog hΔ E' hlen_le ω').1 hs'
  have hstop : ∀ ω i, i < j → AllSucc (schedDelta 0 l) (fun i => E' i ω) j →
      pieceStop spec (fun i => E' i ω) i = schedDelta 0 l i := fun ω i hi hs' => by
    simp only [pieceStop]
    rw [show instrTime spec i = schedDelta 0 l i from instrTime_sched (lt_of_lt_of_le hi hlen_le)]
    exact min_eq_left (hs' i hi).le
  filter_upwards [hS.2.2.2 j, hR.ae_pieceRegular,
    Sec7.Aux122Disint.ae_ae_condExpKernel_eq (hS.2.1 j) (hpm j),
    Sec7.Aux122Disint.ae_ae_condExpKernel (hS.2.1 j) hR.ae_pieceRegular,
    KernelTower.ae_ae_condExpKernel_condExpKernel_eq (P := P) (pastSigma_mono spec E' (Nat.le_succ j))
      (hS.2.1 (j + 1)) hcg,
    Sec7.Aux122Disint.ae_ae_condExpKernel (hS.2.1 j)
      (Sec7.Aux122Disint.ae_ae_condExpKernel_eq (hS.2.1 (j + 1)) (hpm (j + 1))),
    Sec7.Aux122Disint.ae_ae_condExpKernel (hS.2.1 j)
      (Sec7.Aux122Disint.ae_ae_condExpKernel (hS.2.1 (j + 1)) hR.ae_pieceRegular)]
    with ω₀ hst hreg0 hpmω hregν hkk hpm1ν hreg1ν hint
  -- the first `j` pieces failed at `ω₀`: nothing to prove
  by_cases hs0 : AllSucc (schedDelta 0 l) (fun i => E' i ω₀) j
  swap
  · filter_upwards [hpmω] with ω hω hs1
    exact absurd (hallSucc ω₀ ω hω.symm (hs1.mono (Nat.le_succ j))) hs0
  have hr0 := pieceRegular_of_allSucc hreg0 hlen_le hs0
  -- a switching tip before `j` was on the boundary at `ω₀`: nothing to prove
  by_cases hti0 : SwitchTipsInterior spec (fun i => E' i ω₀) j
  swap
  · filter_upwards [hpmω, hregν] with ω hω hregω hs1 hti1
    exfalso
    apply hti0
    intro i hi
    have hsω : AllSucc (schedDelta 0 l) (fun i => E' i ω) j := hs1.mono (Nat.le_succ j)
    have hrω := pieceRegular_of_allSucc hregω hlen_le hsω
    have hrec : recOf (schedDelta 0 l i) (E' i ω) = recOf (schedDelta 0 l i) (E' i ω₀) := by
      have h1 := congrFun hω ⟨i, hi⟩
      rwa [pastMap_of_allSucc hgw hprog hΔ E' hlen_le hsω,
        pastMap_of_allSucc hgw hprog hΔ E' hlen_le hs0] at h1
    have h1 := hti1 i (Nat.lt_succ_of_lt hi)
    rw [hstop ω i hi hsω] at h1
    rw [hstop ω₀ i hi hs0]
    exact (isInteriorStop_congr (hΔ i) (hsω i hi) (hs0 i hi) (continuousOn_of_pieceRegular (hrω i hi) (hsω i hi))
      (continuousOn_of_pieceRegular (hr0 i hi) (hs0 i hi)) hrec).1 h1
  -- the datum at `j`
  have hpair : HasLaunchPairEq κ b jumps P h W' spec E' j ω₀ := hint hs0 hti0
  have hl0 := (launches_run_gw2 (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ (fun i => E' i ω₀) hj).1 hs0
  obtain ⟨b', J', hj', hb', htrj, hfl⟩ := hst _ _ hl0
  obtain ⟨Wk, ζk, ℓk, hWk, hℓkm, hidk⟩ := hpair _ _ hl0 hj' htrj
  have hζk : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E' j) ω₀), ζk ω = ⊤ := hidk.mono fun _ h => h.1
  have hconf := isConformal_succChart spec.1 (schedDelta 0 l) (fun i => E' i ω₀) j hr0
  have hhj := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hb' hfl
  have hgν : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E' j) ω₀),
      g ω = recOf (schedDelta 0 l j) (E' j ω) := by
    filter_upwards [hpmω] with ω hω
    exact pastMap_succ_last E' hj (hallSucc ω ω₀ hω hs0)
  have hGν := exists_prefixPairEq hD h12 h13 h12₀ h13₀ κ hκ hκ4 (schedAngle l j) hθj b' J' hb'
    (condExpKernel P (pastSigma κ b jumps spec E' j) ω₀) hj' hhj Wk ζk hWk hζk _ _ hfl (schedDelta 0 l j) (hΔ j) g
    hgm hgν
  have hfg : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E' j) ω₀),
      pastMap κ b jumps spec E' (j + 1) ω =
        Fin.snoc (α := fun _ => RecData) (pastMap κ b jumps spec E' j ω₀) (g ω) := by
    filter_upwards [hpmω] with ω hω
    rw [pastMap_succ_eq_snoc spec E' j ω, hω]
  have hker2 := KernelTower.ae_condExpKernel_comap_eq (P := condExpKernel P (pastSigma κ b jumps spec E' j) ω₀)
    hpmΩ hgm (measurable_snoc_const _) (ψ := fun u : PastData (j + 1) => u (Fin.last j))
    (measurable_pi_apply _) hfg (Eventually.of_forall fun ω => rfl)
  -- the chosen traces of the conditional counterflow and of the piece
  have hk16 : 0 < 16 / κ := by positivity
  have hWk' := hWk
  obtain ⟨b'', J'', hk'', -, -, hflk⟩ := hWk'
  have hlift := KernelTower.ae_ae_condExpKernel_of_ae (P := condExpKernel P (pastSigma κ b jumps spec E' j) ω₀)
    (m := MeasurableSpace.comap g inferInstance) hgm.comap_le
    (hidk.and ((GW2aSingle.ae_chosenTrace h13 hk16 hflk).and ((Supp8.GB6.ae_driver_zero_continuousOn hflk).and
      ((GW2aSingle.ae_chosenTrace h13 hκ hfl).and (Supp8.GB6.ae_driver_zero_continuousOn hfl)))))
  -- the fibre property of the launch chart at `ω₀`
  have hfib : GW1Z.FiberGood (succChart spec.1 (schedDelta 0 l) (fun i => E' i ω₀) j)
      (contactSet κ b jumps spec (fun i => E' i ω₀) j) := by
    have h1 := GW1Z.chartFiber_run (κ := κ) (b := b) (jumps := jumps) spec (fun i => E' i ω₀) hreg0 j
    have hch : (ExplState.run κ b jumps spec (fun i => E' i ω₀) j).2.2.2.2.1 =
        succChart spec.1 (schedDelta 0 l) (fun i => E' i ω₀) j :=
      ((run_gw2 (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ (fun i => E' i ω₀) j hlen_le).1 hs0).2
    rw [hch] at h1
    rw [contactSet_eq_prefixPhysSet hgw hprog hΔ hlen_le hs0]
    exact h1
  filter_upwards [hpmω, hregν, hkk, hGν, hker2, hlift, hpm1ν, hreg1ν]
    with ω hω hregω hkkω hGω hker2ω hliftω hpm1ω hreg1ω
  intro hs1 hti1 c θ' hl1 h'' htr''
  have hsω : AllSucc (schedDelta 0 l) (fun i => E' i ω) j := hs1.mono (Nat.le_succ j)
  have hjω : schedDelta 0 l j < (E' j ω).2 := hs1 j (Nat.lt_succ_self j)
  have hk1 : j + 1 < spec.2.2.length := by
    by_contra hk
    rw [launches_run_succ_of_length_le κ b jumps spec _ (not_lt.1 hk)] at hl1
    exact absurd hl1 (by simp)
  rw [(launches_run_gw2 (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ (fun i => E' i ω) hk1).1 hs1] at hl1
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hl1)
  have hrω := pieceRegular_of_allSucc hregω hk1.le hs1
  have hrec0 : ∀ i < j, recOf (schedDelta 0 l i) (E' i ω) = recOf (schedDelta 0 l i) (E' i ω₀) := fun i hi => by
    have h1 := congrFun hω ⟨i, hi⟩
    rwa [pastMap_of_allSucc hgw hprog hΔ E' hlen_le hsω, pastMap_of_allSucc hgw hprog hΔ E' hlen_le hs0] at h1
  have hsucc : succChart spec.1 (schedDelta 0 l) (fun i => E' i ω) j =
      succChart spec.1 (schedDelta 0 l) (fun i => E' i ω₀) j :=
    succChart_eq_of_recOf_eq spec.1 hΔ j hsω hs0
      (fun i hi => continuousOn_of_pieceRegular (hrω i (Nat.lt_succ_of_lt hi)) (hsω i hi))
      (fun i hi => continuousOn_of_pieceRegular (hr0 i hi) (hs0 i hi)) hrec0
  obtain ⟨hU, hU0⟩ := continuous_stopDrv (hrω j (Nat.lt_succ_self j))
  have hT : 0 ≤ stopTime (schedDelta 0 l j) (E' j ω) := NNReal.coe_nonneg _
  have hc_eq : succChart spec.1 (schedDelta 0 l) (fun i => E' i ω) (j + 1) =
      (succChart spec.1 (schedDelta 0 l) (fun i => E' i ω₀) j).loewner (stopDrv (schedDelta 0 l j) (E' j ω))
        (stopTime (schedDelta 0 l j) (E' j ω)) := by
    change (succChart spec.1 (schedDelta 0 l) (fun i => E' i ω) j).loewner _ _ = _
    rw [hsucc]
  have hc₂ := Chart.isConformal_id.loewner hU hU0 hT
  have hℓ₂c := hc₂.continuousOn_lift_inv (Chart.continuousOn_lift_loewner hU hU0 hT)
  have htr₂ : ∀ ω', IsChartTransport (Chart.id.loewner (stopDrv (schedDelta 0 l j) (E' j ω))
      (stopTime (schedDelta 0 l j) (E' j ω))) 1 0 (QuantumZipper.chiC κ) (hj' ω') (h'' ω') := fun ω' =>
    IsChartTransport.of_trans hconf.1 hc₂ hconf.2 hℓ₂c (htrj ω') (by
      rw [← Chart.loewner_eq_trans, ← hc_eq]
      exact htr'' ω')
  have hint_stop : IsInteriorStop (fun t => (E' j ω).1 t) (schedDelta 0 l j) := by
    have h1 := hti1 j (Nat.lt_succ_self j)
    have e : pieceStop spec (fun i => E' i ω) j = schedDelta 0 l j := by
      simp only [pieceStop]
      rw [show instrTime spec j = schedDelta 0 l j from instrTime_sched hj]
      exact min_eq_left hjω.le
    rwa [e] at h1
  obtain ⟨W₂, ζ₂, ℓ₂, hW₂, hℓ₂m, hid₂⟩ := hGω hjω hint_stop h'' htr₂
  have hμ : condExpKernel (condExpKernel P (pastSigma κ b jumps spec E' j) ω₀) (MeasurableSpace.comap g inferInstance)
      ω = condExpKernel P (pastSigma κ b jumps spec E' (j + 1)) ω := hker2ω.symm.trans hkkω
  rw [hμ] at hW₂ hid₂ hliftω
  have hB : HasBdryLimits (fwdMapInv (stopDrv (schedDelta 0 l j) (E' j ω))
      (stopTime (schedDelta 0 l j) (E' j ω))) :=
    (hrω j (Nat.lt_succ_self j)).hasBdryLimits (ne_top_of_le_ne_top (hΔ j) (min_le_left _ _))
  have hζ₂ : ∀ᵐ ω' ∂(condExpKernel P (pastSigma κ b jumps spec E' (j + 1)) ω), ζ₂ ω' = ⊤ :=
    hid₂.mono fun _ h => h.1
  refine ⟨W₂, ζ₂, fun ω' u => evalQ (ℓk ω') (ℓ₂ ω' u), hW₂, fun u => measurable_evalQ hℓkm (hℓ₂m u), ?_⟩
  filter_upwards [hid₂, GW2Later.ae_counterflow_regular h13 hκ hW₂ hζ₂, hliftω, hpm1ω, hreg1ω]
    with ω' hid₂ω hreg₂ω hlω hpmω' hregω'
  obtain ⟨Γ₂, hΓ₂, hW₂c, hW₂0, -⟩ := hreg₂ω
  obtain ⟨hidkω, ⟨hγk, -⟩, hdrvk, ⟨hαj, -⟩, hdrvα⟩ := hlω
  have hζkω : ζk ω' = ⊤ := hidkω.1
  rw [hζkω] at hγk hdrvk
  have hWkc : Continuous fun t => Wk t ω' := by
    have h1 := hdrvk.2
    simp only [ENNReal.coe_lt_top, ofPred_true] at h1
    exact continuousOn_univ.1 h1
  -- the sample `ω'` has the past of `ω` before `j + 1`
  have hs1' : AllSucc (schedDelta 0 l) (fun i => E' i ω') (j + 1) := by
    rw [allSucc_iff_flags hgw hprog hΔ E' hk1.le ω', hpmω']
    exact (allSucc_iff_flags hgw hprog hΔ E' hk1.le ω).1 hs1
  have hrω' := pieceRegular_of_allSucc hregω' hk1.le hs1'
  have hrec1 : ∀ i < j + 1, recOf (schedDelta 0 l i) (E' i ω') = recOf (schedDelta 0 l i) (E' i ω) := fun i hi => by
    have h1 := congrFun hpmω' ⟨i, hi⟩
    rwa [pastMap_of_allSucc hgw hprog hΔ E' hk1.le hs1', pastMap_of_allSucc hgw hprog hΔ E' hk1.le hs1] at h1
  have hcω' : ∀ i < j + 1, ContinuousOn (E' i ω').1 {t | (t : ℝ≥0∞) ≤ schedDelta 0 l i} := fun i hi =>
    continuousOn_of_pieceRegular (hrω' i hi) (hs1' i hi)
  have hcω : ∀ i < j + 1, ContinuousOn (E' i ω).1 {t | (t : ℝ≥0∞) ≤ schedDelta 0 l i} := fun i hi =>
    continuousOn_of_pieceRegular (hrω i hi) (hs1 i hi)
  have hcω₀ : ∀ i < j, ContinuousOn (E' i ω₀).1 {t | (t : ℝ≥0∞) ≤ schedDelta 0 l i} := fun i hi =>
    continuousOn_of_pieceRegular (hr0 i hi) (hs0 i hi)
  have hsω' : AllSucc (schedDelta 0 l) (fun i => E' i ω') j := hs1'.mono (Nat.le_succ j)
  have hcontact : contactSet κ b jumps spec (fun i => E' i ω) (j + 1) =
      contactSet κ b jumps spec (fun i => E' i ω₀) j ∪
        (succChart spec.1 (schedDelta 0 l) (fun i => E' i ω₀) j).tipSet
          (fun r : ℝ≥0 => (E' j ω').1 (min (r : ℝ≥0∞) ((schedDelta 0 l j).toNNReal : ℝ≥0∞)).toNNReal)
          ((schedDelta 0 l j).toNNReal : ℝ≥0∞) := by
    rw [contactSet_eq_of_recOf_eq hgw hprog hΔ hk1.le hs1 hs1' hcω hcω' fun i hi => (hrec1 i hi).symm,
      contactSet_succ hgw hprog hΔ hk1.le hs1',
      contactSet_eq_of_recOf_eq hgw hprog hΔ hlen_le hsω' hs0 (fun i hi => hcω' i (Nat.lt_succ_of_lt hi)) hcω₀
        fun i hi => (hrec1 i (Nat.lt_succ_of_lt hi)).trans (hrec0 i hi),
      succChart_eq_of_recOf_eq spec.1 hΔ j hsω' hs0 (fun i hi => hcω' i (Nat.lt_succ_of_lt hi)) hcω₀
        fun i hi => (hrec1 i (Nat.lt_succ_of_lt hi)).trans (hrec0 i hi),
      min_eq_left (hs1' j (Nat.lt_succ_self j)).le, ENNReal.coe_toNNReal (hΔ j)]
  -- the piece at `ω'`, up to its own time
  have hSζ : (((schedDelta 0 l j).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ (E' j ω').2 := by
    rw [ENNReal.coe_toNNReal (hΔ j)]
    exact (hs1' j (Nat.lt_succ_self j)).le
  have hαp := LP.isGeneratingTrace_mono hαj hSζ
  have hWp : ContinuousOn (E' j ω').1 {t | (t : ℝ≥0∞) ≤ ((schedDelta 0 l j).toNNReal : ℝ≥0)} := by
    have h1 := hcω' j (Nat.lt_succ_self j)
    rwa [ENNReal.coe_toNNReal (hΔ j)]
  have hold : IsPrefixClock (succChart spec.1 (schedDelta 0 l) (fun i => E' i ω₀) j) (fun t => W' t ω')
      (fun t => Wk t ω') (contactSet κ b jumps spec (fun i => E' i ω₀) j) (ℓk ω') :=
    ⟨hidkω.2.1, hidkω.2.2.1, hidkω.2.2.2.1, hidkω.2.2.2.2⟩
  have hstep := isPrefixClock_step hfib hold hγk hWkc hdrvk.1 hΓ₂ hW₂c hW₂0 hU hU0 hT hB hαp hWp hdrvα.1
    hid₂ω.2.1 hid₂ω.2.2.1 hid₂ω.2.2.2.1 hid₂ω.2.2.2.2
  have hℓeq : (fun u => evalQ (ℓk ω') (ℓ₂ ω' u)) = ℓk ω' ∘ ℓ₂ ω' :=
    funext fun u => evalQ_eq hidkω.2.2.1.monotone hidkω.2.1 _
  refine ⟨hid₂ω.1, ?_, ?_, ?_, ?_⟩
  · rw [hℓeq]; exact hstep.1
  · rw [hℓeq]; exact hstep.2.1
  · rw [hℓeq, hstep.2.2.1, hcontact]
  · rw [hc_eq]
    intro r z
    rw [evalQ_eq hidkω.2.2.1.monotone hidkω.2.1]
    exact hstep.2.2.2 r z

end InteractingSLE.Theorem14.GW2Stm
