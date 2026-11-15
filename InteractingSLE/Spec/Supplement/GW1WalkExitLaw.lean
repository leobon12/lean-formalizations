/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkExitStage

/-! # GW1: the conditional-law proof of a classified right exit -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC)

universe u

namespace InteractingSLE.Theorem14.GW1WalkExit

open Exist Exist.Staged Exist.StagedLaw Restart GW1WalkFinish LQGMetric

section Right

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

theorem ae_classifiedExit_right (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ true) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {k : ℕ}
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h (boundaryWalkSpec b jumps θ true) E k β Y)
    (hinv : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true)
        (fun j => E j ω) (k + 1)).2.2.2.1 k ≠
        none → GW1W.RInv κ θ b jumps (β ω)
          (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) k) ∧
        GW1W.RReady
          (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) k)) :
    ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true)
        (fun j => E j ω) (k + 1)).2.2.2.1 k ≠
        none → ClassifiedExit κ b true
          (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) k)
          (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) (k + 1)) := by
  let spec := boundaryWalkSpec b jumps θ true
  let R := fun ω n => ExplState.run κ b jumps spec (fun j => E j ω) n
  have h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ := hE.2.1 k
  have hLp := GW1W.measurableSet_pastSigma_launch (κ := κ) hb spec hE.1 hreg k
  have hGm : MeasurableSet {ω | (R ω (k + 1)).2.2.2.1 k ≠ none →
      ClassifiedExit κ b true (R ω k) (R ω (k + 1))} := by
    exact ((h𝒢 _ hLp).compl.union (measurableSet_classifiedExit hb
      (isMeasState_run hb spec hE.1 hreg k)
      (isMeasState_run hb spec hE.1 hreg (k + 1)) true)).congr (by
        ext ω
        simp only [mem_union, mem_compl_iff, mem_ofPred_eq]
        tauto)
  have hstage := GW1W.ae_stage_right hκ hb hh hE hreg hW
    (hinv.mono fun ω hω hl => (hω hl).1)
  refine Sec5.Lemma56Stages.ae_of_ae_condExpKernel h𝒢 hGm ?_
  filter_upwards [GW1W.ae_isFlowLineDriver_stage hκ hb hh hE hreg hW, hinv,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem h𝒢 hLp.compl,
    Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hstage] with ω₀ hfl₀ hI₀ hmem hstageK
  by_cases hl₀ : (R ω₀ (k + 1)).2.2.2.1 k ≠ none
  swap
  · filter_upwards [hmem hl₀] with ω hω hl
    exact False.elim (hω hl)
  obtain ⟨⟨h', hfl⟩, hrunK⟩ := hfl₀ hl₀
  rw [GW1W.instrAngle_walk hl₀] at hfl
  obtain ⟨hI, hready⟩ := hI₀ hl₀
  have hfl' := hfl
  obtain ⟨_, 𝓕, VL, VR, B, -, hC⟩ := hfl'
  have hEv := hC.1
  obtain ⟨cc, hcc, hgc⟩ := GW1Conn.exists_hasGroupEndSums_flowLineL hκ
    (β ω₀).isPiecewiseConstantBoundaryData hI.1
  have hanti : StrictAnti (flowLineXL (β ω₀).fn (β ω₀).jumps 0) :=
    fun i j hij => GW0.flowLineXL_lt (β ω₀).fn (β ω₀).jumps 0 hij
  filter_upwards [GW1Conn.ae_exists_hit_right hEv hκ hcc hanti.antitone hanti.injective hgc,
    hEv.ae_isIntegratedSLEPath, hrunK, hstageK] with ω hhit hp hrun hstageω hl
  obtain ⟨-, hgood, hbad⟩ := hstageω hl
  have hr : R ω (k + 1) = ExplState.launch (R ω₀ k) k (E k ω) θ ⊤ := by
    dsimp only [R, spec]
    rw [GW1W.launch_walk hl, hrun]
  change ClassifiedExit κ b true (R ω k) (R ω (k + 1))
  change R ω k = R ω₀ k at hrun
  rw [hr, hrun]
  apply classifiedExit_launch_right hI.2.1 hready k (hreg k ω) hgood ?_ ?_ ?_
  · intro hfin hzero
    apply launch_thr_true_of_hit hI.2.1 k θ hfin hzero
    let T : ℝ≥0 := (E k ω).2.toNNReal
    have hTζ : (T : ℝ≥0∞) = (E k ω).2 := ENNReal.coe_toNNReal hfin
    have hT : 0 < T := by
      apply pos_iff_ne_zero.2
      intro he
      exact hzero (by rw [← hTζ, he, ENNReal.coe_zero])
    obtain ⟨y, hy, hyb, hyd⟩ := hhit T hT hTζ (stopDrv ⊤ (E k ω))
      (fun r hr hrT => GW1W.stopDrv_top_eq hTζ hr hrT)
    rw [GW1W.stopTime_top_eq hTζ]
    exact ⟨y, hy, hyb, hyd⟩
  · intro hz
    rw [hready.2]
    exact right_height_of_zero_threshold hκ hb hI (hp.isForcePath.threshold_of_eq_zero hz)
  · intro hs
    rw [← hr] at hs ⊢
    exact hbad hs

end Right

end InteractingSLE.Theorem14.GW1WalkExit
