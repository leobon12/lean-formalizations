/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Lemma47AngleMart
import InteractingSLE.Spec.Sec5.Lemma47AngleGood
import InteractingSLE.Spec.Sec5.Lemma47AngleWeights
import InteractingSLE.Spec.Sec5.RestartGenOne
/-!
# Lemma 4.7 in chart Q at an interior relative angle

The killed image word is restarted with `Prop49Exit.ae_restart_code`. The existing
code event and trace concatenation unkill it; `isFirstHitQ_of_imgFull` then gives
the first contact. The only theorem-valued input is Zhan's Part A at `16/κ`.
This proof does not use either full determination or full trace-existence theorem.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real
universe u
namespace InteractingSLE.Sec5.Lemma47Angle
open Sec7.Lemma71C (capClock)
open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique GlueCond Cond44Ref CfRegQ Prop411Q MartChar WholeField CrossCond.Theta
open Prop49Exit Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47
section Seed
open MartChar.RealFlow
open CrossCond.Word49 (psiL psiR junL junR)
variable {Ω : Type*} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {s : ℝ≥0} {E : Set (Ω × HistorySpace 0 0)}
  {p : Ω × HistorySpace 0 0} {κ θ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
/-- The general-angle image word is initially above its continuation threshold. -/
theorem not_threshold_q_angle (hκ : 0 < κ) (hθb : CfThetaBounds κ θ ρL ρR xL xR)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (hp : p ∈ E) (hs : 0 < s) :
    ¬ ForceWord.ThresholdCondition (iwLT κ θ ρL ρR xL xR) (iwRT κ θ ρL ρR xL xR) (qW W VL VR ζ s E 0 p)
      (fun i => qVL (qxLT κ θ ρL ρR xL xR) W VL VR ζ s E i 0 p)
      (fun j => qVR (qxRT κ θ ρL ρR xL xR) W VL VR ζ s E j 0 p) := by
  have hg := hEg p hp
  have hγ := isKilledCurve_qgCurve (q := s) hEg p
  have hxo := isOrderedForceWord_qx_angle κ θ ρL ρR xL xR
  have hw := continuous_fDrv hg
  obtain ⟨hjL, hjR⟩ := junction_gaps hg hs
  have hW0 : qW W VL VR ζ s E 0 p = 0 := hγ.kcW_zero
  have hVL : ∀ i, qVL (qxLT κ θ ρL ρR xL xR) W VL VR ζ s E i 0 p = qgXL (qxLT κ θ ρL ρR xL xR) W s E p i :=
    fun i => kcVL_zero_eq hγ _ (qgXL_nonpos hxo.2.1 hEg hs p) i
  have hVR : ∀ j, qVR (qxRT κ θ ρL ρR xL xR) W VL VR ζ s E j 0 p = qgXR (qxRT κ θ ρL ρR xL xR) W s E p j :=
    fun j => kcVR_zero_eq hγ _ (qgXR_nonneg hxo.2.2.2 hEg hs p) j
  have hjL0 : junL (fDrv W p) s ≠ 0 := div_ne_zero (by norm_num) hjL.ne'
  have hjR0 : junR (fDrv W p) s ≠ 0 := div_ne_zero (by norm_num) hjR.ne
  simp only [hW0, hVL, hVR, qgXL, qgXR, hp, ↓reduceIte, ForceWord.ThresholdCondition, not_or, not_le, iwLT, iwRT,
    CrossRestart.slitRhoL, CrossRestart.slitRhoR]
  rw [Prop49Exit.sum_filter_snoc_eq_zero _ _ _ _ hjL0, Prop49Exit.sum_filter_snoc_eq_zero _ _ _ _ hjR0]
  have eL : (Finset.univ.filter fun i => psiL (fDrv W p) s (qxLT κ θ ρL ρR xL xR i) = 0) =
      Finset.univ.filter fun i => qxLT κ θ ρL ρR xL xR i = 0 := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun h => by_contra fun h0 => Prop49Exit.psiL_ne_zero hw s.coe_nonneg hjL (hxo.2.1 i) h0 h,
      fun h => ?_⟩
    simp [psiL, h]
  have eR : (Finset.univ.filter fun j => psiR (fDrv W p) s (qxRT κ θ ρL ρR xL xR j) = 0) =
      Finset.univ.filter fun j => qxRT κ θ ρL ρR xL xR j = 0 := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun h => by_contra fun h0 => Prop49Exit.psiR_ne_zero hw s.coe_nonneg hjR (hxo.2.2.2 j) h0 h,
      fun h => ?_⟩
    simp [psiR, h]
  rw [eL, eR]
  have hc : -2 < 16 / κ / 2 - 2 := by have : 0 < 16 / κ / 2 := by positivity
                                      linarith
  refine ⟨Prop49Exit.neg_two_lt_sum_filter_zero hc (fun i i' hii h => ?_) (prefix_qρL_angle hκ hθb),
    Prop49Exit.neg_two_lt_sum_filter_zero hc (fun j j' hjj h => ?_) (prefix_qρR_angle hκ hθb)⟩
  · exact le_antisymm (hxo.2.1 i') (h ▸ hxo.1 hii)
  · exact le_antisymm (h ▸ hxo.2.2.1 hjj) (hxo.2.2.2 j')

end Seed
section Main

open LQGMetric (DistOn TestOn)

variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- **Lemma 4.7 at a flow time `s > 0`, in the chart `Q`**: almost surely on the glued space the counterflow first
hits `η((0, s])` at `η(s)` (`Prop411Q.IsFirstHitQ`), given Zhan's Part A inputs at `16/κ` (clearance form). -/
theorem ae_isFirstHitQ_of_clearance_angle (hθ₁ : -(π / 2) ≤ θ) (hθ₂ : θ ≤ π / 2)
    (hA : Sec5.PartAInputsSixteenDivOfClearance) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR) (hθb : CfThetaBounds κ θ ρL ρR xL xR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) {s : ℝ≥0} (hs : 0 < s) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      IsFirstHitQ (seedLine ζ W p.1) (histLine p.2) s := by
  set μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) with hμ
  set E := glueGood47 μ W VL VR ζ with hEdef
  have hNR := CfNoReturn.Route.counterflowNoReturnAdmStatement_of_partA_of_clearance.{u} hA
  have hae := ae_isGood47_angle hNR hκ hκ4 hF h44 hθb hC hcf hlaw k hk
  have hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p := isGood47_of_mem_glueGood47
  have hX := hC.2.2.2.1
  have hxo := isOrderedForceWord_qx_angle κ θ ρL ρR xL xR
  obtain ⟨-, hK, hWa, hVLa, hVRa, -, -, -, -, hζq⟩ :=
    filtClauses47 (μ := μ) (s := s) hX hxo.2.1 hxo.1 hxo.2.2.2 hxo.2.2.1 hs hae
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓦, Bi, hB, hBc, hEnt⟩ := exists_isWordEntrance_q_angle hκ hκ4 hF h44 hθb hC hcf hlaw k hk hae hs
  set 𝓖 := qFilt μ (qxLT κ θ ρL ρR xL xR) (qxRT κ θ ρL ρR xL xR) W VL VR ζ s E with h𝓖
  have hTq' : ∀ q : ℝ≥0, MeasurableSet[WholeField.prodFiltration 𝓖 𝓦 q]
      {p : (Ω × HistorySpace 0 0) × Ω₀ | (q : ℝ≥0∞) < (qT W VL VR ζ s E p.1 : ℝ≥0∞)} := fun q =>
    WholeField.comap_fst_le_prodFiltration 𝓖 𝓦 q _ ⟨_, hζq q, rfl⟩
  have hthr : ∀ᵐ p ∂(μ.prod P₀), ¬ ForceWord.ThresholdCondition (iwLT κ θ ρL ρR xL xR) (iwRT κ θ ρL ρR xL xR)
      (qW W VL VR ζ s E 0 p.1) (fun i => qVL (qxLT κ θ ρL ρR xL xR) W VL VR ζ s E i 0 p.1)
      (fun j => qVR (qxRT κ θ ρL ρR xL xR) W VL VR ζ s E j 0 p.1) := by
    have h1 : ∀ᵐ p ∂μ, ¬ ForceWord.ThresholdCondition (iwLT κ θ ρL ρR xL xR) (iwRT κ θ ρL ρR xL xR)
        (qW W VL VR ζ s E 0 p) (fun i => qVL (qxLT κ θ ρL ρR xL xR) W VL VR ζ s E i 0 p)
        (fun j => qVR (qxRT κ θ ρL ρR xL xR) W VL VR ζ s E j 0 p) := by
      filter_upwards [ae_mem_glueGood47 hae] with p hp
      exact not_threshold_q_angle hκ hθb hEg hp hs
    exact Measure.quasiMeasurePreserving_fst.ae h1
  -- the seed marks `0⁻`, `0⁺` of the counterflow word
  set i₀L : Fin (flowLineNL (Sec7.StripSysField.counterflowData κ (bDataT ρL ρR xL xR θ κ))
      (Sec7.StripSysField.counterflowJumps (Cond44Ref.forceJumpFinset xL xR)) 0) := ⟨0, Nat.succ_pos _⟩ with hi₀L
  set i₀R : Fin (flowLineNR (Sec7.StripSysField.counterflowData κ (bDataT ρL ρR xL xR θ κ))
      (Sec7.StripSysField.counterflowJumps (Cond44Ref.forceJumpFinset xL xR)) 0) := ⟨0, Nat.succ_pos _⟩ with hi₀R
  have hx₀L : qxLT κ θ ρL ρR xL xR i₀L = 0 := rfl
  have hx₀R : qxRT κ θ ρL ρR xL xR i₀R = 0 := rfl
  have hk' : 0 < 16 / κ := by positivity
  have hR := Prop49Exit.ae_restart_code (P := μ.prod P₀) (𝓘 := WholeField.prodFiltration 𝓖 𝓦) hk' hB hBc
    (W := fun t p => qW W VL VR ζ s E t p.1) (VL := fun i t p => qVL (qxLT κ θ ρL ρR xL xR) W VL VR ζ s E i t p.1)
    (VR := fun j t p => qVR (qxRT κ θ ρL ρR xL xR) W VL VR ζ s E j t p.1)
    (Sec7.PhaseSelFull.stronglyAdapted_fst hWa) (fun i => Sec7.PhaseSelFull.stronglyAdapted_fst (hVLa i))
    (fun j => Sec7.PhaseSelFull.stronglyAdapted_fst (hVRa j)) (T := fun p => (qT W VL VR ζ s E p.1 : ℝ≥0∞)) hTq'
    (fun p => (isKilledCurve_qgCurve hEg p.1).zero_lt_kcLife)
    (measurableSet_avCode47 (Fin.castSucc i₀L) (Fin.castSucc i₀R))
    (fun st hsep hFo => codeLaw_compl_avCode47_eq_zero hA hκ hκ4 (prefix_iwL_angle hκ hκ4 hθ₂ hθb)
      (prefix_iwR_angle hκ hκ4 hθ₁ hθb) _ _ st hsep hFo)
    hEnt (fun p t ht htT i => hK.sepL p.1 t ht htT i) (fun p t ht htT j => hK.sepR p.1 t ht htT j) hthr
  have h2 := Measure.ae_ae_of_ae_prod hR
  have hXm : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  have hadmF := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  have hline := ae_glue_fst (μ := P) k hXm (ae_seedLine_of_admissible hκ hκ4.le hF hadmF hC.1)
  have htrans := cfGlueAE_mem_goodTransSet_angle.{u} θ hA κ hκ hκ4 xL xR ρL ρR hF h44 hθb P 𝓕 W VL VR B
    ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  filter_upwards [h2, ae_mem_glueGood47 hae, hline, htrans] with p hpR hpE ⟨_, _, hβp⟩ hpT
  obtain ⟨ω₀, hpω⟩ := hpR.exists
  have hg := hEg p hpE
  have hγ := isKilledCurve_qgCurve (q := s) hEg p
  -- a positive rational image time before the killing
  obtain ⟨S, hSP, hS0⟩ := hγ.exists_gt 0 hγ.zero_mem
  have hcS : 0 < capClock (qgCurve W s E p) S := by
    rw [← hγ.capClock_zero]; exact hγ.strictMonoOn_capClock hγ.zero_mem hSP hS0
  obtain ⟨q', hq'0, hq'S⟩ := exists_rat_btwn hcS
  have hq'0' : (0 : ℚ) < q' := by exact_mod_cast hq'0
  set r : ℝ≥0 := (q' : ℝ).toNNReal with hrdef
  have hr0 : 0 < r := Real.toNNReal_pos.2 hq'0
  have hrT : (r : WithTop ℝ≥0) < qT W VL VR ζ s E p :=
    lt_of_le_of_lt (WithTop.coe_le_coe.2 (Real.toNNReal_le_toNNReal hq'S.le)) (hγ.lt_kcLife hSP)
  obtain ⟨x, hxC, hxS, -, hxag⟩ := hpω q' hq'0' hrT
  -- the restarted canonical solution: a transient trace with real values between the seed marks
  obtain ⟨hxF, -⟩ := mem_cRelF_iff.2 hxC
  obtain ⟨hcwc, hcw0⟩ := Prop49Exit.cw_props_of_mem_cRelF hxF
  obtain ⟨hζx, htrSet, hAvQ⟩ := (mem_avCode47_iff hxC).1 hxS
  rw [hζx] at hcwc
  have hcwc' : Continuous (cw x) := continuousOn_univ.1 (hcwc.mono fun t _ => ENNReal.coe_lt_top)
  obtain ⟨η, hη, hηtr⟩ := (mem_traceSet_iff hcwc'.continuousOn hcw0 (fun _ h => absurd h (lt_irrefl _))).1 htrSet
  have heqη : ∀ t, LP.traceAt t (cw x) = η t := fun t =>
    LP.traceAt_eq_of_isGeneratingTrace hη hcwc'.continuousOn hcw0 ENNReal.coe_lt_top
  have hηc : Continuous η := continuousOn_univ.1 (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have htrc : Continuous fun t => LP.traceAt t (cw x) := by
    have e : (fun t => LP.traceAt t (cw x)) = η := funext heqη
    rw [e]; exact hηc
  -- a frozen trace of the killed word beyond `r`
  obtain ⟨S', hS'P, hrS'⟩ := hγ.lt_kcLife_iff_exists.1 hrT
  have hcS'0 : 0 ≤ capClock (qgCurve W s E p) S' := hγ.capClock_nonneg hS'P
  obtain ⟨V, α', hV, hV0, hα', hEqV, hα'H⟩ := hγ.exists_frozenTrace (hγ.lt_kcLife hS'P)
  rw [Real.coe_toNNReal _ hcS'0] at hEqV hα'H
  have hL := qVL_seed_sub (x := qxLT κ θ ρL ρR xL xR) hpE hx₀L hrT hV hEqV hrS'.le
  have hR' := qVR_seed_sub (x := qxRT κ θ ρL ρR xL xR) hpE hx₀R hrT hV hEqV hrS'.le
  have hηR : ∀ t (y : ℝ), η t = y → chartAL V r ≤ y ∧ y ≤ chartAR V r := by
    intro t y hy
    have := avoid_of_avQ47 hAvQ htrc t y (by rw [heqη]; exact hy)
    simp only [stAt] at this
    rw [hL, hR'] at this
    exact this
  -- the full image trace
  have hwc := hK.contW p
  have hw0 := hK.w_zero p
  obtain ⟨Γ, hΓc, hΓγ, hΓR, hΓtr⟩ := fullTrace_of_restart (T := (qT W VL VR ζ s E p : ℝ≥0∞)) hwc hw0
    (γ := qTr W VL VR ζ s E p) (fun s' hs' => by
      obtain ⟨T', hs'T', hT'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs'
      exact Sec7.IsGeneratingTrace.isGeneratingTraceIcc (isGeneratingTrace_qTr hEg p hT')
        (hwc.mono fun t ht => lt_trans ht hT') hw0 hs'T')
    (fun t ht0 ht => hγ.kcTr_mem_H ht0 ht) hr0 hrT hcwc' hcw0 (fun t ht => (hxag t ht).1) hη (hηtr rfl) hηR
    (fun y h1 h2 => extendFrom_base_q (c := capClock (qgCurve W s E p) S') hrS' hV hV0 hα'
      (fun u hu => hα'H u ⟨hu.1, hu.2.trans hrS'.le⟩) hEqV y h1 h2)
  -- the deterministic first hit
  have hpre : preContact (histLine p.2) (negInv '' fwdHull (fDrv W p) s) = qgPre W VL VR ζ s E p := by
    rw [qgPre_of_mem hpE, qObs_of_good hg]
  have hGc : IsClosed (negInv '' fwdHull (fDrv W p) s) := by
    rw [← qObs_of_good (q := s) hg]; exact isClosed_qObs hg
  refine isFirstHitQ_of_imgFull (exists_flowTrace hg).1 hβp (continuous_fDrv hg) (fDrv_zero hg)
    (NNReal.coe_pos.2 hs) hGc
    ((Prop49Exit.continuous_traceAt_of_mem_goodCfSet hg.2.2.1.1).comp continuous_real_toNNReal)
    (histLine_zero hg) (fun v hv => histLine_mem_H hg hv) (GlueCond.tendsto_histLine_of_mem_goodTransSet hpT)
    (a := fun u => (capClock (qgCurve W s E p) u).toNNReal) ?_ hΓc hΓR hΓtr ?_
  · rw [hpre]
    intro u hu v hv huv
    exact Real.toNNReal_le_toNNReal (hγ.strictMonoOn_capClock.monotoneOn hu hv huv)
  · rw [hpre]
    intro u hu hu0
    rw [hΓγ _ (hγ.lt_kcLife hu), qTr_capClock hEg hpE hu, imgCurve_of_pos hu0]

end Main

/-- Lemma 4.7Q for every interior relative angle, from Zhan's Part A input. -/
theorem lemma47QHitTStatement_of_partA_of_clearance {θ : ℝ}
    (hθ₁ : -(π / 2) < θ) (hθ₂ : θ < π / 2) (hA : PartAInputsSixteenDivOfClearance) :
    RestartGen.Lemma47QHitTStatement.{u} θ := by
  intro q hq κ hκ hκ4 nL nR xL xR ρL ρR hF h44 hθb Ω mΩ P _ 𝓕 W VL VR B ζ h hC
    Ω₂ _mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have := ae_isFirstHitQ_of_clearance_angle hθ₁.le hθ₂.le hA hκ hκ4 hF h44 hθb hC hcf hlaw k hk
    (s := (q : ℝ).toNNReal) (Real.toNNReal_pos.2 hq')
  simpa only [Real.coe_toNNReal _ hq'.le] using this

/-- The same general-angle first contact from the stopping inverse-boundary input alone. -/
theorem lemma47QHitTStatement_of_inverseBoundary {θ : ℝ}
    (hθ₁ : -(π / 2) < θ) (hθ₂ : θ < π / 2)
    (hG5 : ∀ κ : ℝ, 0 < κ → κ < 4 → ZhanGT4.StoppingInverseBoundaryStatement.{0} (16 / κ)) :
    RestartGen.Lemma47QHitTStatement.{u} θ :=
  lemma47QHitTStatement_of_partA_of_clearance hθ₁ hθ₂
    (partAInputsSixteenDivOfClearance_of_inverseBoundary hG5)

end InteractingSLE.Sec5.Lemma47Angle
