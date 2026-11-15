/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1ActiveLaw
import InteractingSLE.Spec.Supplement.GW1ActiveRunL
import InteractingSLE.Spec.Supplement.GW1ActiveThrL

/-!
# Lemma GW1's active-word classification: the left walk

Packet PROVE-T14-GW1W. The mirror of `GW1ActiveLaw` for the left boundary walk (`boundaryWalkSpec b jumps θ false`,
in the application `θ = π/2`): one stage almost surely (`ae_stage_left`: no new right record, a good record, a high
outward height at a new left record) and the classification at every launch (`exists_witness_left`).
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

namespace GW1W

open Exist Exist.StagedLaw Exist.Staged Restart LQGMetric

section Left

open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ : ℝ}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **One stage of the left walk, almost surely** (the mirror of `ae_stage_right`). -/
theorem ae_stage_left (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ false) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {ℓ : ℕ} {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h (boundaryWalkSpec b jumps θ false) E ℓ β Y)
    (hinv : ∀ᵐ ω₀ ∂P,
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) (fun j => E j ω₀) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        LInv κ θ b jumps (β ω₀) (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) (fun j => E j ω₀) ℓ)) :
    ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) (fun j => E j ω) (ℓ + 1)) ≠
          stThr (some true) ∧
        ((E ℓ ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (E ℓ ω)))) ∧
        (stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) (fun j => E j ω) (ℓ + 1)) =
            stThr (some false) →
          sleLambda κ ≤
            leftLim b (stRecL (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) (fun j => E j ω) (ℓ + 1))) +
              θ * chiC κ) := by
  set spec := boundaryWalkSpec b jumps θ false with hspec
  set R : Ω → ℕ → ExplState := fun ω n => ExplState.run κ b jumps spec (fun j => E j ω) n with hRdef
  have h𝒢 : pastSigma κ b jumps spec E ℓ ≤ mΩ := hE.2.1 ℓ
  have hLp := measurableSet_pastSigma_launch (κ := κ) hb spec hE.1 hreg ℓ
  have hMS := isMeasState_run (κ := κ) hb spec hE.1 hreg (ℓ + 1)
  set G : Set Ω := {ω | (R ω (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      stStatus (R ω (ℓ + 1)) ≠ stThr (some true) ∧
        ((E ℓ ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (E ℓ ω)))) ∧
        (stStatus (R ω (ℓ + 1)) = stThr (some false) →
          sleLambda κ ≤ leftLim b (stRecL (R ω (ℓ + 1))) + θ * chiC κ)} with hGdef
  have hGm : MeasurableSet G := by
    have h1 : MeasurableSet {ω | stStatus (R ω (ℓ + 1)) ≠ stThr (some true)} := (hMS.1 _).compl
    have h2 : MeasurableSet {ω | (E ℓ ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (E ℓ ω)))} := by
      have hζ : Measurable fun ω => (E ℓ ω).2 := measurable_snd.comp (hE.1 ℓ)
      exact ((measurableSet_eq_fun hζ measurable_const).union (measurableSet_good ⊤ (hE.1 ℓ) (hreg ℓ))).congr
        (by ext ω; simp only [mem_union, mem_ofPred_eq]; tauto)
    have h3 : MeasurableSet {ω | stStatus (R ω (ℓ + 1)) = stThr (some false) →
        sleLambda κ ≤ leftLim b (stRecL (R ω (ℓ + 1))) + θ * chiC κ} := by
      have hm : Measurable fun ω => leftLim b (stRecL (R ω (ℓ + 1))) + θ * chiC κ :=
        ((measurable_leftLim_of_pcbd hb).comp hMS.2.2.2.2.1).add_const _
      exact ((hMS.1 _).compl.union (measurableSet_le measurable_const hm)).congr
        (by ext ω; simp only [mem_union, mem_compl_iff, mem_ofPred_eq]; tauto)
    exact ((h𝒢 _ hLp).compl.union (h1.inter (h2.inter h3))).congr
      (by ext ω; simp only [mem_union, mem_compl_iff, mem_inter_iff, mem_ofPred_eq, hGdef]; tauto)
  refine Sec5.Lemma56Stages.ae_of_ae_condExpKernel h𝒢 hGm ?_
  filter_upwards [ae_isFlowLineDriver_stage hκ hb hh hE hreg hW, hinv,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem h𝒢 hLp.compl] with ω₀ hfl₀ hinv₀ hmemc
  by_cases hl₀ : (R ω₀ (ℓ + 1)).2.2.2.1 ℓ ≠ none
  swap
  · filter_upwards [hmemc hl₀] with ω hω hlω
    exact absurd hlω hω
  obtain ⟨⟨h', hfl⟩, hrunK⟩ := hfl₀ hl₀
  rw [instrAngle_walk hl₀] at hfl
  have hI := hinv₀ hl₀
  have hfl' := hfl
  obtain ⟨_, 𝓕, VL, VR, B, -, hC⟩ := hfl'
  have hEv := hC.1
  obtain ⟨cc, hcc, hgc⟩ := GW1Conn.exists_hasGroupEndSums_flowLineR hκ (β ω₀).isPiecewiseConstantBoundaryData hI.1
  have hmono : StrictMono (flowLineXR (β ω₀).fn (β ω₀).jumps 0) := fun i j hij =>
    GW0.flowLineXR_lt (β ω₀).fn (β ω₀).jumps 0 hij
  filter_upwards [hEv.ae_isIntegratedSLEPath, hEv.ae_tendsto_threshold hκ,
    ae_isDrvGood_of_isFlowLineDriver hκ ⊤ (hreg ℓ) hfl, hrunK] with ω hp hthr hgood hrun hlω
  have hR1 : ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1) =
      ExplState.launch (ExplState.run κ b jumps spec (fun j => E j ω₀) ℓ) ℓ (E ℓ ω) θ ⊤ := by
    rw [launch_walk hlω, hrun]
  rw [hR1]
  have hnohit : (E ℓ ω).2 ≠ ⊤ → (E ℓ ω).2 ≠ 0 → ∀ y : ℝ, 0 < y →
      (∀ r < stopTime ⊤ (E ℓ ω), ∃ u, IsForwardSol (stopDrv ⊤ (E ℓ ω)) (y : ℂ) r u) →
      ∃ u, IsForwardSol (stopDrv ⊤ (E ℓ ω)) (y : ℂ) (stopTime ⊤ (E ℓ ω)) u := by
    intro hD h0 y hy halive
    set T : ℝ≥0 := (E ℓ ω).2.toNNReal with hTdef
    have hTζ : (T : ℝ≥0∞) = (E ℓ ω).2 := ENNReal.coe_toNNReal hD
    have hT : 0 < T := by
      rw [pos_iff_ne_zero]
      intro hT0
      rw [hT0, ENNReal.coe_zero] at hTζ
      exact h0 hTζ.symm
    obtain ⟨w₀, vL₀, vR₀, hlim, hthrc⟩ := hthr T hT hTζ
    have hUc : Continuous (stopDrv ⊤ (E ℓ ω)) := by
      rw [← recDrv_eq_stopDrv (hreg ℓ ω) (hgood (min_top_ne_top hD))]
      exact continuous_recDrv _ _
    rw [stopTime_top_eq hTζ] at halive ⊢
    exact no_hit_right_of_tendsto hp.isForcePath hcc hmono hgc (iL := ⟨0, by unfold flowLineNL; omega⟩)
      (iR := ⟨0, by unfold flowLineNR; omega⟩) rfl rfl (fun i => Fin.le_def.2 (Nat.zero_le _)) hT hTζ hlim hthrc
      hUc (fun r hr hrT => stopDrv_top_eq hTζ hr hrT) hy halive
  refine ⟨launch_ne_thr_true hI.2.1.1 hI.2.2.2 ℓ θ hnohit, fun hD => hgood (min_top_ne_top hD), fun hthr1 => ?_⟩
  have hfin : (E ℓ ω).2 ≠ ⊤ := by
    intro htop
    have hmin : min ⊤ (E ℓ ω).2 = ⊤ := by rw [htop]; rfl
    rw [(launch_eq_of_top (R ω₀ ℓ) ℓ (E ℓ ω) θ ⊤ hmin).2.2.2.2.1] at hthr1
    exact absurd hthr1 (by simp)
  obtain ⟨h0, hhitx, -, -⟩ := launch_thr_false hfin hthr1
  have hpos : 0 < (E ℓ ω).2 := pos_iff_ne_zero.2 h0
  have hgd := hgood (min_top_ne_top hfin)
  have hgp : IsGoodStopPath κ (flowLineXL (β ω₀).fn (β ω₀).jumps 0) (flowLineXR (β ω₀).fn (β ω₀).jumps 0)
      (flowLineRhoL κ (β ω₀).fn (β ω₀).jumps 0 θ) (flowLineRhoR κ (β ω₀).fn (β ω₀).jumps 0 θ) ⊤ (E ℓ ω)
      (fun i s => VL i s ω) (fun j s => VR j s ω) (fun s => B s ω) := by
    refine ⟨hp, fun T hT hζ => ?_, hreg ℓ ω, hgd, min_top_ne_top hfin, hpos⟩
    obtain ⟨w₀, vL₀, vR₀, hlim, -⟩ := hthr T hT hζ
    exact ⟨w₀, vL₀, vR₀, hlim⟩
  obtain ⟨ε, hε, hhigh⟩ := highStart_of_goodStopPath hκ hgp hI.1
  obtain ⟨hs₁, hrel⟩ := lProf_launch hI.2.1 ℓ θ (hreg ℓ ω) hgd hfin hhitx
  have hO := lOrig_of_rel hκ hb hI.2.1 hI.2.2.1 θ ⟨hs₁, hrel⟩
  exact leftLim_ge_of_highStart hb hs₁ hO hε hhigh

end Left

/-! ### The classification at every launch of the left walk -/

section InductionL

open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ : ℝ}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The invariant at the root of the left walk (deterministic). -/
theorem lInv_root (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hamb : ∀ t, 0 < t → t ∉ jumps → -sleLambda κ < b t + θ * chiC κ) {c₀ : BoundaryWord}
    (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) :
    LInv κ θ b jumps (BoundaryWord.shiftW 0 c₀) (ExplState.init 0) ∧ LReady (ExplState.init 0) ∧
      -sleLambda κ < rightLim b 0 + θ * chiC κ := by
  have hprof : rProf (stChart (ExplState.init 0)) = fun x => x := by
    funext x
    simp [rProf, ExplState.init, InteractingSLE.Chart.recenter, InteractingSLE.Chart.id]
  have hlprof : lProf (stChart (ExplState.init 0)) = fun x => x := by
    funext x
    simp [lProf, ExplState.init, InteractingSLE.Chart.recenter, InteractingSLE.Chart.id]
  have hR : stRecR (ExplState.init 0) = 0 := rfl
  have hL : stRecL (ExplState.init 0) = 0 := rfl
  have hJ : ∀ y, y ∉ (BoundaryWord.shiftW 0 c₀).jumps → y ∉ jumps := fun y hy h => hy (by
    rw [BoundaryWord.jumps_shiftW, hc₀J]
    exact Finset.mem_image.2 ⟨y, h, by ring⟩)
  have hRG : RightGood (fun x : ℝ => x) 0 :=
    ⟨strictMonoOn_id, continuousOn_id, fun M => ⟨max M 0 + 1, by positivity, by linarith [le_max_left M 0]⟩⟩
  refine ⟨⟨fun y hy hyJ => ?_, ⟨fun x => ?_, ?_, fun x hx => ?_, fun ε hε => ?_⟩, fun x hx hxJ hzJ => ?_,
    ?_, fun x hx => ?_⟩, ⟨Or.inl rfl, rfl⟩, ?_⟩
  · rw [BoundaryWord.fn_shiftW, add_zero, hc₀ y (hJ y hyJ)]
    exact hamb y hy (hJ y hyJ)
  · simp [ExplState.init, InteractingSLE.Chart.recenter, InteractingSLE.Chart.id]
  · rw [hlprof, hL, neg_zero]; exact hRG
  · rw [hlprof]; rw [hL, neg_zero] at hx; exact hx
  · rw [hlprof, hL, neg_zero]; exact ⟨ε / 2, half_pos hε, by linarith⟩
  · rw [hprof] at hzJ ⊢
    rw [BoundaryWord.fn_shiftW, add_zero]
    exact hc₀ x hxJ
  · rw [hprof, hR]; exact hRG
  · rw [hprof]; rw [hR] at hx; exact hx
  · obtain ⟨hi, hhi, hconst⟩ := Sec5.Aux22ChartE.exists_forall_Ioo_eq_rightLim hb 0
    have hne : (Ioo (0 : ℝ) hi \ (jumps : Set ℝ)).Nonempty :=
      ((Ioo_infinite hhi).sdiff jumps.finite_toSet).nonempty
    obtain ⟨t, ht, htJ⟩ := hne
    rw [← hconst t ht]
    exact hamb t ht.1 htJ

/-- **GW1's active-word classification for the left walk** (the mirror of `exists_witness_right`). -/
theorem exists_witness_left (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ false) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hamb : ∀ t, 0 < t → t ∉ jumps → -sleLambda κ < b t + θ * chiC κ) :
    ∀ k, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h (boundaryWalkSpec b jumps θ false) E k β Y ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) (fun j => E j ω) (k + 1)).2.2.2.1 k ≠
          none →
        LInv κ θ b jumps (β ω) (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) (fun j => E j ω) k) ∧
        LReady (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) (fun j => E j ω) k) ∧
        (stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) (fun j => E j ω) k) = .inl () →
          -sleLambda κ <
            rightLim b (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) (fun j => E j ω) k)) +
              θ * chiC κ) := by
  set spec := boundaryWalkSpec b jumps θ false with hspec
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨fun _ => BoundaryWord.shiftW spec.1 c₀, fun ω => flowField spec.1 0 (h ω),
        isStageWitness_zero hh hc₀J hc₀, Eventually.of_forall fun ω _ => ?_⟩
      have h0 := lInv_root (κ := κ) (θ := θ) hb hamb hc₀J hc₀
      exact ⟨h0.1, h0.2.1, fun _ => h0.2.2⟩
    have H : ∀ ℓ, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens), ℓ < k →
        IsStageWitness κ b jumps P h spec E ℓ β Y ∧
        ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
          LInv κ θ b jumps (β ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
          LReady (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
          (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) = .inl () →
            -sleLambda κ < rightLim b (stPt (ExplState.run κ b jumps spec (fun j => E j ω) ℓ)) + θ * chiC κ) := by
      intro ℓ
      by_cases hℓ : ℓ < k
      · obtain ⟨β, Y, hW, hI⟩ := ih ℓ hℓ
        exact ⟨β, Y, fun _ => ⟨hW, hI⟩⟩
      · exact ⟨fun _ => default, fun _ => 0, fun h' => absurd h' hℓ⟩
    choose β Y hWI using H
    obtain ⟨βk, Yk, hWk, hexpl⟩ := isStageWitness_succ_expl (isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb hh
      hk (fun j _ => hE.1 j) (fun j _ => hreg j) (fun j _ => hE.2.2.2 j) β Y fun ℓ hℓ => (hWI ℓ hℓ).1
    refine ⟨βk, Yk, hWk, ?_⟩
    have hall : ∀ᵐ ω ∂P, ∀ ℓ, ℓ < k →
        ((ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
          LInv κ θ b jumps (β ℓ ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
          LReady (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
          (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) = .inl () →
            -sleLambda κ < rightLim b (stPt (ExplState.run κ b jumps spec (fun j => E j ω) ℓ)) + θ * chiC κ)) ∧
        ((ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
          stStatus (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)) ≠ stThr (some true) ∧
          ((E ℓ ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (E ℓ ω)))) ∧
          (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)) = stThr (some false) →
            sleLambda κ ≤
              leftLim b (stRecL (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1))) + θ * chiC κ)) := by
      refine ae_all_iff.2 fun ℓ => ?_
      by_cases hℓ : ℓ < k
      · filter_upwards [(hWI ℓ hℓ).2, ae_stage_left hκ hb hh hE hreg (hWI ℓ hℓ).1
          ((hWI ℓ hℓ).2.mono fun ω hω hl => (hω hl).1)] with ω h1 h2 _ using ⟨h1, h2⟩
      · exact Eventually.of_forall fun ω h' => absurd h' hℓ
    filter_upwards [hall] with ω hω hlk
    obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlk
    obtain ⟨ℓ, hℓk, ⟨c', θ'', hl'⟩, -, hn, -⟩ := exists_last_launch spec (fun j => E j ω) hk hcθ
    have hl : (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by rw [hl']; simp
    obtain ⟨hinv, hst⟩ := hω ℓ hℓk
    obtain ⟨hI, hR, hroot⟩ := hinv hl
    obtain ⟨hnoR, hgood, hF2⟩ := hst hl
    obtain ⟨hInv, hReady, ha⟩ := lInv_walk_step (D := fun j => E j ω) hκ hb hℓk hlk hl hn hI hR hroot (hreg ℓ ω)
      hgood hnoR hF2
    have hβ := hexpl ℓ ω hℓk hlk hl hn
    rw [instrAngle_walk hl, pastMap_last_of_launch hl, instrTime_walk hl, ← ha] at hβ
    rw [hβ]
    refine ⟨hInv, hReady, fun hroot' => ?_⟩
    obtain ⟨-, -, r, hr⟩ := run_eq_of_last_launch (D := fun j => E j ω) hℓk hlk hl hn
    rw [hr] at hroot'
    exact absurd hroot' (by simp [stArcM])

end InductionL

end GW1W

end Theorem14

end InteractingSLE
