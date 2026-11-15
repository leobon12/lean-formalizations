/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkExitLaw

/-! # GW1: the classified left exit, including the original right seed bound -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC)

universe u

namespace InteractingSLE.Theorem14.GW1WalkExit

open Exist Exist.Staged Exist.StagedLaw Restart GW1WalkFinish LQGMetric
open PiecewiseConstantBoundaryData (leftLim rightLim)

theorem right_seed_of_left_launch {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (hready : GW1W.LReady (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D k))
    (hroot : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D k) = .inl () →
      -sleLambda κ < rightLim b
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D k)) + θ * chiC κ)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D (k + 1)).2.2.2.1 k ≠ none) :
    -sleLambda κ < rightLim b
      (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D k)) + θ * chiC κ := by
  rcases hready.1 with h | h
  · exact hroot h
  · suffices hadm : ExplState.IsAdmissibleSeed κ
        (leftLim b (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D k)))
        (rightLim b (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D k))) θ by
      exact hadm.2
    by_contra hna
    have hfs := GW1W.flowStep_arcL_eq_self
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D k) k (D k) θ ⊤ h hna
    obtain ⟨hev, hk⟩ := GW1W.even_of_launches_walk hl
    rw [GW1W.run_succ_walk_flow hk hev, hfs, launches_run_of_le _ _ le_rfl] at hl
    exact hl rfl

section Left

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

theorem ae_classifiedExit_left (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ false) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {k : ℕ}
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h (boundaryWalkSpec b jumps θ false) E k β Y)
    (hinv : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false)
        (fun j => E j ω) (k + 1)).2.2.2.1 k ≠
        none → GW1W.LInv κ θ b jumps (β ω)
          (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) (fun j => E j ω) k) ∧
        GW1W.LReady
          (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) (fun j => E j ω) k) ∧
        (stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) (fun j => E j ω) k) =
          .inl () → -sleLambda κ < rightLim b
            (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) (fun j => E j ω) k)) +
              θ * chiC κ)) :
    ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false)
        (fun j => E j ω) (k + 1)).2.2.2.1 k ≠
        none → ClassifiedExit κ b false
          (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) (fun j => E j ω) k)
          (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false)
            (fun j => E j ω) (k + 1)) := by
  let spec := boundaryWalkSpec b jumps θ false
  let R := fun ω n => ExplState.run κ b jumps spec (fun j => E j ω) n
  have h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ := hE.2.1 k
  have hLp := GW1W.measurableSet_pastSigma_launch (κ := κ) hb spec hE.1 hreg k
  have hGm : MeasurableSet {ω | (R ω (k + 1)).2.2.2.1 k ≠ none →
      ClassifiedExit κ b false (R ω k) (R ω (k + 1))} := by
    exact ((h𝒢 _ hLp).compl.union (measurableSet_classifiedExit hb
      (isMeasState_run hb spec hE.1 hreg k)
      (isMeasState_run hb spec hE.1 hreg (k + 1)) false)).congr (by
        ext ω
        simp only [mem_union, mem_compl_iff, mem_ofPred_eq]
        tauto)
  have hstage := GW1W.ae_stage_left hκ hb hh hE hreg hW
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
  obtain ⟨hI, hready, hroot⟩ := hI₀ hl₀
  have hseed := right_seed_of_left_launch hready hroot hl₀
  have hfl' := hfl
  obtain ⟨_, 𝓕, VL, VR, B, -, hC⟩ := hfl'
  have hEv := hC.1
  obtain ⟨cc, hcc, hgc⟩ := GW1Conn.exists_hasGroupEndSums_flowLineR hκ
    (β ω₀).isPiecewiseConstantBoundaryData hI.1
  have hmono : StrictMono (flowLineXR (β ω₀).fn (β ω₀).jumps 0) :=
    fun i j hij => GW0.flowLineXR_lt (β ω₀).fn (β ω₀).jumps 0 hij
  filter_upwards [GW1Conn.ae_exists_hit_left hEv hκ hcc hmono.monotone hmono.injective hgc,
    hEv.ae_isIntegratedSLEPath, hrunK, hstageK] with ω hhit hp hrun hstageω hl
  obtain ⟨hnoR, hgood, hbad⟩ := hstageω hl
  have hr : R ω (k + 1) = ExplState.launch (R ω₀ k) k (E k ω) θ ⊤ := by
    dsimp only [R, spec]
    rw [GW1W.launch_walk hl, hrun]
  change ClassifiedExit κ b false (R ω k) (R ω (k + 1))
  change R ω k = R ω₀ k at hrun
  rw [hr, hrun]
  apply classifiedExit_launch_left hI.2.1 hready k (hreg k ω) hgood ?_ ?_ ?_
  · intro hfin hzero
    apply launch_thr_false_of_hit hI.2.1 k θ hfin hzero
      (show stStatus (ExplState.launch (R ω₀ k) k (E k ω) θ ⊤) ≠ stThr (some true) from
        by rw [← hr]; exact hnoR)
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
    refine ⟨hseed, ?_⟩
    rw [hready.2]
    exact left_height_of_zero_threshold hκ hb hI (hp.isForcePath.threshold_of_eq_zero hz)
  · intro hs
    rw [← hr] at hs ⊢
    exact hbad hs

end Left

end InteractingSLE.Theorem14.GW1WalkExit
