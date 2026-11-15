/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkInfCap
import InteractingSLE.Spec.Supplement.WalkSideInputs
import InteractingSLE.Spec.Supplement.WalkPastDet

/-!
# Theorem 1.4's walk leaves: the capped prefix of a boundary walk is a marked local set

Packet PROVE-T14-WALKINF. The capped program `capSpec w ℓ θ τ` of PROVE-T14-WALKSIDE (the walk truncated before
instruction `ℓ`, then the angle-`θ` flow for own time `τ`, run with the walk's drivers) is a staged history; its last
piece is the walk's piece `ℓ` stopped at `τ`. Here:

* **`launchLocalCap_of_thm12_thm13`**: under the stage kernel the capped piece is marked local off the explored set,
  for the marks of its stopped record (Theorems 1.2–1.3 through the walk's own uncapped stage `ℓ`, then the capped
  kernel lemma `isHistoryAvoidanceLocalOff_of_chartFlow_cap`);
* `kernelLocal_of_launchLocal`: the per-stage step `WalkLaw.walkStageKernelLocalStatement_of_launch`, for any staged
  program;
* `markedLocalAE_of_kernel`: the stage gluing `WalkLaw.walkMarkedLocalRegAEStatement_of_kernel`, for any staged
  program (R58 form);
* **`PrefixMarkedLocalOnStatement θ right`**: WALKSIDE's input `PrefixMarkedLocalStatement` for the instructions `ℓ`
  that are unstopped angle-`θ` flows of the walk (the only ones its consumer uses, `WalkSide.ae_prefix_limit`), and
  **`prefixMarkedLocalOnStatement_of_thm12_thm13`**, its proof.

For any other `ℓ` (a continuation instruction, or `ℓ` past the program) the capped program launches a piece driven by a
driver on which the staged hypotheses put no constraint, so the unrestricted `PrefixMarkedLocalStatement` asks for the
locality of an arbitrary random curve; it is not used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkInf

open LocalSets Exist.Staged Exist.StagedLaw Sec6 Restart.StagedEntrance WalkSide

/-! ### The capped piece under the stage kernel -/

section Launch

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {w : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

omit mΩ [StandardBorelSpace Ω] in
/-- The explored set of the capped program before `ℓ` is the program's. -/
theorem stageSet_capSpec_of_le {ℓ : ℕ} {θ : ℝ} {τ : ℝ≥0∞} (hℓ : ℓ ≤ w.2.2.length) (ω : Ω) {k : ℕ}
    (hk : k ≤ ℓ) : WalkLaw.stageSet κ b jumps (capSpec w ℓ θ τ) E k ω = WalkLaw.stageSet κ b jumps w E k ω := by
  unfold WalkLaw.stageSet
  rw [run_capSpec_of_le hℓ _ hk]

/-- A generating trace on `[0, ζ]` is one on `[0, min τ ζ]`. -/
theorem isGeneratingTrace_min {W : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace W ζ α) (τ : ℝ≥0∞) :
    IsGeneratingTrace W (min τ ζ) α := by
  rcases le_or_gt ζ τ with h | h
  · rwa [min_eq_right h]
  · rw [min_eq_left h.le]
    induction τ using ENNReal.recTopCoe with
    | top => exact absurd h (not_lt.2 le_top)
    | coe r => exact Sec5.CrossRestart.isGeneratingTrace_of_eqOn_of_lt hα (fun _ _ => rfl) h

/-- **The capped piece of a staged history is marked local off the explored set under the stage kernel** (Theorems
1.2–1.3; R48 allows them for Theorem 1.4). For a staged history `E` of `w` with `StagedPiecesRegular`, drivers regular
at every sample, and an instruction `ℓ` that is an unstopped angle-`θ` flow: for almost every `ω₀` at which the capped
program launches its last piece, under the regular conditional law given the retained past before `ℓ`, the piece
stopped at `τ` is history-avoidance local for the centred field and the marks of its stopped record, on the open sets
off the explored set. -/
theorem launchLocalCap_of_thm12_thm13 (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hE : IsStagedHistory κ b jumps P h w E)
    (hR : StagedPiecesRegular κ b jumps P w E) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (u₀ : ℂ → ℝ) {ℓ : ℕ}
    {θ : ℝ} (hℓ : ℓ < w.2.2.length) (hwℓ : w.2.2[ℓ]? = some (Sum.inl (θ, ⊤))) (τ : ℝ≥0) :
    ∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps (capSpec w ℓ θ τ) (fun j => E j ω₀) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      WalkLaw.IsHistoryAvoidanceLocalOff
        (MeasurableSpace.comap (fun ω => recOf (instrTime (capSpec w ℓ θ τ) ℓ) (E ℓ ω)) inferInstance)
        (WalkLaw.stageSet κ b jumps (capSpec w ℓ θ τ) E ℓ ω₀) (WalkLaw.pieceSet κ b jumps (capSpec w ℓ θ τ) E ℓ)
        (WholeField.centredField h u₀) (condExpKernel P (pastSigma κ b jumps (capSpec w ℓ θ τ) E ℓ) ω₀) := by
  classical
  set cs := capSpec w ℓ θ (τ : ℝ≥0∞) with hcs
  have hT : instrTime w ℓ = ⊤ := by simp only [instrTime, hwℓ]
  have hTc : instrTime cs ℓ = τ := instrTime_capSpec hℓ.le
  rw [hTc, pastSigma_capSpec_of_le hℓ.le E le_rfl]
  have hB := runMeasStatement.{u}
  have h𝒢 : pastSigma κ b jumps w E ℓ ≤ mΩ := hE.2.1 ℓ
  have hhm : Measurable h := hh.1
  have hpm : Measurable (pastMap κ b jumps w E ℓ) :=
    measurable_pastMap hB hb w (fun j _ => hE.1 j) (fun j _ => hreg j) ℓ le_rfl
  have hcont := StagedDet.piecesContinuous_of_stagedPiecesRegular hR
  obtain ⟨Y, hYm, hY⟩ := StagedDet.exists_stageField hb hE.1 hreg hcont ℓ
  have hYm' : Measurable Y := hYm.mono (StagedDet.pastFieldSigma_le hpm hhm) le_rfl
  obtain ⟨Wd, hWdm, hrec⟩ := StagedDet.ae_recOf_eq_stageRec h12p h13 hκ hκ4 hb hh hE hreg hcont ℓ hYm' hY
  rw [hT] at hrec
  obtain ⟨bc, jc, hcond⟩ := hE.exists_isCondFlowLineDriverOn ℓ θ
  -- the good samples
  set L : Set Ω := {ω | (ExplState.run κ b jumps w (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none} with hLdef
  have hLm : MeasurableSet L := measurableSet_launch_self hB hb (fun j _ => hE.1 j) (fun j _ => hreg j)
  set Bad : Set Ω := {ω | ¬ ∀ (j : ℕ) (c : Chart) (θ' : ℝ),
    (ExplState.run κ b jumps w (fun i => E i ω) (j + 1)).2.2.2.1 j = some (c, θ') →
      GW1P.PieceRegular (E j ω).1 (min (instrTime w j) (E j ω).2)} with hBaddef
  have hBad : P Bad = 0 := ae_iff.1 hR.ae_pieceRegular
  set M : Set Ω := L ∩ (toMeasurable P Bad)ᶜ with hMdef
  have hMm : MeasurableSet M := hLm.inter (measurableSet_toMeasurable P Bad).compl
  have hgoodR : ∀ ω, ω ∉ toMeasurable P Bad → ∀ (j : ℕ) (c : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps w (fun i => E i ω) (j + 1)).2.2.2.1 j = some (c, θ') →
        GW1P.PieceRegular (E j ω).1 (min (instrTime w j) (E j ω).2) := fun ω hω => by
    by_contra hc
    exact hω (subset_toMeasurable P Bad hc)
  have hMreg : ∀ ω ∈ M, GW1P.PieceRegular (E ℓ ω).1 (E ℓ ω).2 := fun ω hω => by
    obtain ⟨⟨c, θ'⟩, hl⟩ := Option.ne_none_iff_exists'.1 hω.1
    have := hgoodR ω hω.2 ℓ c θ' hl
    rwa [hT, min_top_left] at this
  have hBae : ∀ᵐ ω ∂P, ω ∉ toMeasurable P Bad := by
    have h0 : P (toMeasurable P Bad) = 0 := by rw [measure_toMeasurable]; exact hBad
    exact ae_iff.2 (by simpa only [not_not, ofPred_mem_eq] using h0)
  have hpc : ∀ ω, Continuous (WalkLeaf.piecePath E ℓ M ω) := WalkLeaf.continuous_piecePath hMreg
  have hpm' : ∀ t, Measurable fun ω => WalkLeaf.piecePath E ℓ M ω t :=
    WalkLeaf.measurable_piecePath hMm (hE.1 ℓ) (hreg ℓ)
  have hp0 : ∀ ω, WalkLeaf.piecePath E ℓ M ω 0 = 0 := WalkLeaf.piecePath_zero hMreg
  -- the facts under the regular conditional laws
  filter_upwards [hcond, hY, hBae, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hBae,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hrec, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hY,
    CondDriverBridge.ae_ae_run_eq_of_le (P := P) (κ := κ) (b := b) (jumps := jumps) w
      (fun j _ ω => hreg j ω) h𝒢 le_rfl] with ω₀ hc₀ hY₀ hB₀ hBν hrecν hYν hrun hl₀c
  have hl₀ : (ExplState.run κ b jumps w (fun j => E j ω₀) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
    rwa [launches_run_capSpec_succ hℓ.le hwℓ] at hl₀c
  obtain ⟨⟨c₀, θ₀⟩, hl⟩ := Option.ne_none_iff_exists'.1 hl₀
  obtain ⟨hspec, -, hc₀def⟩ :=
    eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) w (fun j => E j ω₀) hl
  have hθ : θ₀ = θ := by
    rw [hwℓ] at hspec
    simp only [Option.some.injEq, Sum.inl.injEq, Prod.mk.injEq] at hspec
    exact hspec.1.symm
  subst hθ
  obtain ⟨hcc₀, hℓc₀, -⟩ := hY₀ hl₀
  rw [← hc₀def] at hcc₀ hℓc₀
  have hℓ₀ : LocallyIntegrableOn (fun w => c₀.2.2 (c₀.2.1 w)) H :=
    hℓc₀.locallyIntegrableOn QuantumZipper.isOpen_H.measurableSet
  have hlc : SB.launchChart κ b jumps w (fun j => E j ω₀) ℓ = c₀ := by
    simp only [SB.launchChart, hl, Option.elim]
  obtain ⟨hbp, h', ht', hfl⟩ := hc₀ ⟨c₀, hl⟩
  rw [hlc] at ht'
  have e' : h' = fun ω => Chart.chartTransport hcc₀ 1 0 (chiC κ) (h ω) :=
    funext fun ω => (ht' ω).eq_chartTransport hcc₀ hℓ₀
  rw [e'] at hfl
  -- the good event under the kernel
  have hgood : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps w E ℓ) ω₀),
      ExplState.run κ b jumps w (fun j => E j ω) ℓ = ExplState.run κ b jumps w (fun j => E j ω₀) ℓ ∧
      (ExplState.run κ b jumps w (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ = some (c₀, θ₀) ∧ ω ∈ M ∧
      recOf ⊤ (E ℓ ω) = StagedDet.stageRec h12p hκ Wd (instrAngle w ℓ) ⊤ (pastMap κ b jumps w E ℓ ω₀)
        (Chart.chartTransport hcc₀ 1 0 (chiC κ) (h ω)) := by
    filter_upwards [hrun, hBν, hrecν, hYν] with ω hr h1 h2 h3
    have hlω : (ExplState.run κ b jumps w (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ = some (c₀, θ₀) := by
      rw [congrFun (launches_run_succ_of_run_eq w hr) ℓ, hl]
    have hLω : ω ∈ L := by
      show _ ≠ none
      rw [hlω]
      exact Option.some_ne_none _
    have hpast : pastMap κ b jumps w E ℓ ω = pastMap κ b jumps w E ℓ ω₀ := by
      unfold pastMap
      rw [hr]
    obtain ⟨-, -, htr⟩ := h3 hLω
    rw [hr, ← hc₀def] at htr
    refine ⟨hr, hlω, ⟨hLω, h1⟩, ?_⟩
    rw [h2 hLω, hpast, htr.eq_chartTransport hcc₀ hℓ₀]
  -- the capped kernel statement
  rw [stageSet_capSpec_of_le hℓ.le ω₀ le_rfl]
  refine isHistoryAvoidanceLocalOff_of_chartFlow_cap hκ hκ4 hhm u₀ hcc₀ ?_ hbp hfl hpc hpm' hp0 ?_ ?_ τ ?_
  · intro z hzH hzcl hzD
    rw [hc₀def] at hzcl hzD
    exact WalkLeaf.mem_stageSet_of_frontier w E ω₀ (hgoodR ω₀ hB₀) ℓ z hzH hzcl hzD
  · filter_upwards [hgood] with ω hω
    obtain ⟨-, -, hM, -⟩ := hω
    have hr := hMreg ω hM
    refine ⟨WalkLeaf.isGeneratingTrace_piecePath hM hr, hr.2.1, fun t => ?_⟩
    obtain ⟨-, -, α, hα, -⟩ := id hr
    rw [WalkLeaf.piecePath_eq hM hr hα, WalkLeaf.piecePath_eq hM hr hα,
      ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)), min_assoc, min_self]
  · intro t
    refine ⟨fun X => WalkLeaf.recPath (StagedDet.stageRec h12p hκ Wd (instrAngle w ℓ) ⊤
      (pastMap κ b jumps w E ℓ ω₀) X) t, ?_, ?_⟩
    · have hsr := StagedDet.measurable_stageRec h12p hκ hWdm (instrAngle w ℓ) ⊤
      have e : (fun X : DistOn upperHalfPlaneOpens => StagedDet.stageRec h12p hκ Wd (instrAngle w ℓ) ⊤
          (pastMap κ b jumps w E ℓ ω₀) X) = (fun q : PastData ℓ × DistOn upperHalfPlaneOpens =>
            StagedDet.stageRec h12p hκ Wd (instrAngle w ℓ) ⊤ q.1 q.2) ∘
          (fun X : DistOn upperHalfPlaneOpens => (pastMap κ b jumps w E ℓ ω₀, X)) := rfl
      have hX : Measurable fun X : DistOn upperHalfPlaneOpens => StagedDet.stageRec h12p hκ Wd (instrAngle w ℓ) ⊤
          (pastMap κ b jumps w E ℓ ω₀) X := by
        rw [e]
        exact hsr.comp (measurable_const.prodMk measurable_id)
      exact (WalkLeaf.measurable_recPath t).comp hX
    · filter_upwards [hgood] with ω hω
      obtain ⟨-, -, hM, hrω⟩ := hω
      rw [WalkLeaf.piecePath_of_mem hM, hrω]
  · intro U hUH hKU
    filter_upwards [hgood] with ω hω
    obtain ⟨hr, hlω, hM, -⟩ := hω
    have hrg := hMreg ω hM
    obtain ⟨-, -, α, hα, -⟩ := id hrg
    have hstage : WalkLaw.stageSet κ b jumps cs E ℓ ω = WalkLaw.stageSet κ b jumps w E ℓ ω₀ := by
      rw [stageSet_capSpec_of_le hℓ.le ω le_rfl]
      unfold WalkLaw.stageSet
      rw [hr]
    have hlωc : (ExplState.run κ b jumps cs (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ = some (c₀, θ₀) := by
      rw [launches_run_capSpec_succ hℓ.le hwℓ]
      exact hlω
    have hregc := pieceRegular_capSpec (κ := κ) (b := b) (jumps := jumps) (fun j => E j ω) hℓ.le hwℓ
      (hgoodR ω hM.2) τ
    have hα' : IsGeneratingTrace (E ℓ ω).1 (min (instrTime cs ℓ) (E ℓ ω).2) α := by
      rw [hTc]
      exact isGeneratingTrace_min hα _
    rw [WalkLeaf.disjoint_pieceSet_iff cs E ω hregc hlωc hUH (hstage ▸ hKU) hα', ← WalkLeaf.forall_frozen_notMem_iff,
      hTc]
    refine forall_congr' fun t => ?_
    have e1 : frozenPath (WalkLeaf.piecePath E ℓ M ω) τ t = α (min ((min t τ : ℝ≥0) : ℝ≥0∞) (E ℓ ω).2).toNNReal :=
      WalkLeaf.piecePath_eq hM hrg hα _
    rw [e1, ENNReal.coe_min, min_assoc]

end Launch

end InteractingSLE.Theorem14.WalkInf
