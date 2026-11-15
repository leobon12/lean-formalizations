/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1ActiveRun

/-!
# Lemma GW1's active-word classification: the explicit word of a stage

Packet PROVE-T14-GW1W. The staged conditional law (PROVE-STAGEDLAW, `Exist.StagedLaw.stageLaw`) is proved one launch
at a time: the word of the conditional law at a launch `k` is the stop word of the last launch `ℓ < k`, recentred
(`shiftW a (βA (β_ℓ, θ_ℓ, record_ℓ))`). The landed induction step `Exist.StagedLaw.stageLaw_succ` builds that word
inside its proof and only exports its existence. **`isStageWitness_succ_expl`** is the same step (its proof is
PROVE-STAGEDLAW's, verbatim up to the statement) with the word exported, which the active-word classification needs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW1W

open Exist Exist.StagedLaw Exist.Staged Restart LQGMetric

section Step

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The induction step of the staged conditional law, with the word exported** (PROVE-STAGEDLAW's
`stageLaw_succ`): given witnesses `(β ℓ, Y ℓ)` of the invariant at every `ℓ < k`, there is a witness at `k` whose word,
at a launch `k` with last launch `ℓ`, is `shiftW a (βA (β ℓ, θ_ℓ, record_ℓ))`, `a` the recentring after piece `ℓ`. -/
theorem isStageWitness_succ_expl {βA : BoundaryWord × ℝ × RecData → BoundaryWord} (hβA : IsStopLaw.{u} κ βA)
    (hB : RunMeasStatement.{u}) (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {k : ℕ} (hk : 0 < k)
    (hEm : ∀ j < k, Measurable (E j)) (hreg : ∀ j < k, ∀ ω, IsRegularDriver (E j ω))
    (hok : ∀ j < k, StageOK κ b jumps P h spec E j) (β : ℕ → Ω → BoundaryWord)
    (Y : ℕ → Ω → DistOn upperHalfPlaneOpens) (hW : ∀ ℓ, ℓ < k → IsStageWitness κ b jumps P h spec E ℓ (β ℓ) (Y ℓ)) :
    ∃ (βk : Ω → BoundaryWord) (Yk : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h spec E k βk Yk ∧
      ∀ ℓ ω, ℓ < k → (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        (∀ j, ℓ < j → j < k → (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = none) →
        βk ω = BoundaryWord.shiftW (((ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.2.1.1 0 -
          (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.1 0).re)
          (βA (β ℓ ω, instrAngle spec ℓ, pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ))) := by
  classical
  have hEm' : ∀ ℓ < k, ∀ j < ℓ + 1, Measurable (E j) := fun ℓ hℓ j hj => hEm j (by omega)
  have hreg' : ∀ ℓ < k, ∀ j < ℓ + 1, ∀ ω, IsRegularDriver (E j ω) := fun ℓ hℓ j hj => hreg j (by omega)
  have hpost := fun ℓ (hℓ : ℓ < k) => post_stage hβA hB hκ hb hh (hEm' ℓ hℓ) (hreg' ℓ hℓ) (hok ℓ hℓ)
    (hW ℓ hℓ).1 (hW ℓ hℓ).2.1 (hW ℓ hℓ).2.2.1 (hW ℓ hℓ).2.2.2
  have h𝒢k : pastSigma κ b jumps spec E k ≤ mΩ := by
    rw [pastSigma_eq_comap]; exact (measurable_pastMap hB hb spec hEm hreg k le_rfl).comap_le
  -- the event of the last launch `ℓ`
  set A : ℕ → Set Ω := fun ℓ => {ω | ℓ < k ∧
    (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none ∧
    (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none ∧
    ∀ j, ℓ < j → j < k → (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = none} with hAdef
  -- the recentring after piece `ℓ`
  set a : ℕ → Ω → ℝ := fun ℓ ω => ((ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.2.1.1 0 -
    (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.1 0).re with hadef
  -- the field and the word right after piece `ℓ`
  set Zr : ℕ → Ω → DistOn upperHalfPlaneOpens := fun ℓ ω =>
    recField κ (pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ)) (Y ℓ ω) with hZrdef
  set γr : ℕ → Ω → BoundaryWord := fun ℓ ω =>
    βA (β ℓ ω, instrAngle spec ℓ, pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ)) with hγrdef
  set βk : Ω → BoundaryWord := finPw A (fun ℓ ω => BoundaryWord.shiftW (a ℓ ω) (γr ℓ ω)) (fun _ => default) k
    with hβkdef
  set Yk : Ω → DistOn upperHalfPlaneOpens := finPw A (fun ℓ ω => flowField (a ℓ ω) 0 (Zr ℓ ω)) (fun _ => 0) k
    with hYkdef
  -- the last launch is unique
  have hdisj : ∀ ℓ ω, ω ∈ A ℓ → ∀ j, j ≠ ℓ → ω ∉ A j := by
    rintro ℓ ω ⟨hℓ, -, hl, hn⟩ j hj ⟨hj', -, hl', hn'⟩
    exact hj (eq_of_last_launch hℓ hj' hl hl' hn hn').symm
  have hcover : ∀ ω, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none → ∃ ℓ, ω ∈ A ℓ := by
    intro ω hω
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hω
    obtain ⟨ℓ, hℓ, ⟨c', θ', hl'⟩, -, hn', -⟩ := exists_last_launch spec (fun j => E j ω) hk hcθ
    exact ⟨ℓ, hℓ, hω, by rw [hl']; simp, hn'⟩
  have hβk : ∀ ℓ ω, ω ∈ A ℓ → βk ω = BoundaryWord.shiftW (a ℓ ω) (γr ℓ ω) := fun ℓ ω hω =>
    finPw_eq hω (hdisj ℓ ω hω) k hω.1
  have hYk : ∀ ℓ ω, ω ∈ A ℓ → Yk ω = flowField (a ℓ ω) 0 (Zr ℓ ω) := fun ℓ ω hω =>
    finPw_eq hω (hdisj ℓ ω hω) k hω.1
  -- measurability
  have hAm : ∀ ℓ < k, MeasurableSet (A ℓ) := by
    intro ℓ hℓ
    have hset : A ℓ = {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} ∩
        ({ω | (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none} ∩
          ⋂ j ∈ (Finset.range k).filter (ℓ < ·),
            {ω | (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j ≠ none}ᶜ) := by
      ext ω
      simp only [hAdef, mem_ofPred_eq, mem_inter_iff, mem_iInter, Finset.mem_filter, Finset.mem_range, mem_compl_iff,
        not_not, hℓ, true_and]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun j hj => h3 j hj.2 hj.1⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun j hj hjk => h3 j ⟨hjk, hj⟩⟩
    rw [hset]
    refine (measurableSet_launch_self hB hb hEm hreg).inter ((measurableSet_launch hB hb spec hEm hreg hℓ).inter ?_)
    refine Finset.measurableSet_biInter _ fun j hj => (measurableSet_launch hB hb spec hEm hreg ?_).compl
    exact (Finset.mem_range.1 (Finset.mem_filter.1 hj).1)
  -- `A ℓ` is an event of the retained past before `k` and before `ℓ + 1`
  have hA𝒢 : ∀ ℓ < k, MeasurableSet[pastSigma κ b jumps spec E k] (A ℓ) := by
    intro ℓ hℓ
    refine measurableSet_pastSigma_of_runs hB hb hEm hreg (hAm ℓ hℓ) fun ω ω' he hω => ?_
    obtain ⟨-, hlk, hl, hn⟩ := hω
    refine ⟨hℓ, ?_, ?_, fun j hj hjk => ?_⟩
    · rw [← launches_run_succ_of_run_eq spec (he k le_rfl)]; exact hlk
    · rw [← launches_run_of_lt spec _ hℓ, ← he k le_rfl, launches_run_of_lt spec _ hℓ]; exact hl
    · rw [← launches_run_of_lt spec _ hjk, ← he k le_rfl, launches_run_of_lt spec _ hjk]; exact hn j hj hjk
  have hA𝒢ℓ : ∀ ℓ < k, MeasurableSet[pastSigma κ b jumps spec E (ℓ + 1)] (A ℓ) := by
    intro ℓ hℓ
    refine measurableSet_pastSigma_of_runs hB hb (hEm' ℓ hℓ) (hreg' ℓ hℓ) (hAm ℓ hℓ) fun ω ω' he hω => ?_
    obtain ⟨-, hlk, hl, hn⟩ := hω
    have hrun := run_eq_of_noLaunch_after spec (he (ℓ + 1) le_rfl) hn
    have hrunk : ExplState.run κ b jumps spec (fun j => E j ω) k =
        ExplState.run κ b jumps spec (fun j => E j ω') k := by
      have := hrun (k - (ℓ + 1)) (by omega)
      rwa [show ℓ + 1 + (k - (ℓ + 1)) = k by omega] at this
    refine ⟨hℓ, ?_, ?_, fun j hj hjk => ?_⟩
    · rw [← launches_run_succ_of_run_eq spec hrunk]; exact hlk
    · rw [← he (ℓ + 1) le_rfl]; exact hl
    · have hrj := hrun (j - ℓ) (by omega)
      rw [show ℓ + 1 + (j - ℓ) = j + 1 by omega] at hrj
      rw [← hrj]; exact hn j hj hjk
  have ham : ∀ ℓ < k, Measurable (a ℓ) := fun ℓ hℓ =>
    Complex.measurable_re.comp ((measurable_chart_apply hB hb spec hEm hreg (by omega) 0).sub
      (measurable_chart_apply hB hb spec hEm hreg le_rfl 0))
  have ha𝒢 : ∀ ℓ < k, Measurable[pastSigma κ b jumps spec E k] (a ℓ) := fun ℓ hℓ =>
    measurable_pastSigma_of_runs hB hb hEm hreg (ham ℓ hℓ) fun ω ω' he => by
      simp only [hadef, he (ℓ + 1) (by omega), he k le_rfl]
  have hlast𝒢 : ∀ ℓ < k, Measurable[pastSigma κ b jumps spec E k]
      fun ω => pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ) := by
    intro ℓ hℓ
    have h1 : Measurable[pastSigma κ b jumps spec E (ℓ + 1)]
        fun ω => pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ) := by
      rw [pastSigma_eq_comap]
      exact (measurable_pi_apply (X := fun _ : Fin (ℓ + 1) => RecData) (Fin.last ℓ)).comp
        (comap_measurable (pastMap κ b jumps spec E (ℓ + 1)))
    exact h1.mono (pastSigma_mono spec E (by omega)) le_rfl
  have hγ𝒢 : ∀ ℓ < k, Measurable[pastSigma κ b jumps spec E k] (γr ℓ) := by
    intro ℓ hℓ
    have hβ' : Measurable[pastSigma κ b jumps spec E k] (β ℓ) :=
      (hW ℓ hℓ).1.mono (pastSigma_mono spec E hℓ.le) le_rfl
    exact hβA.1.comp (hβ'.prodMk (measurable_const.prodMk (hlast𝒢 ℓ hℓ)))
  have hlastm : ∀ ℓ < k, Measurable fun ω => pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ) := fun ℓ hℓ =>
    (measurable_pi_apply (X := fun _ : Fin (ℓ + 1) => RecData) (Fin.last ℓ)).comp
      (measurable_pastMap hB hb spec hEm hreg (ℓ + 1) (by omega))
  have hZm : ∀ ℓ < k, Measurable (Zr ℓ) := fun ℓ hℓ => measurable_recField_comp κ (hlastm ℓ hℓ) (hW ℓ hℓ).2.1
  have hβkm : Measurable[pastSigma κ b jumps spec E k] βk :=
    measurable_finPw (mα := pastSigma κ b jumps spec E k) measurable_const k hA𝒢 fun ℓ hℓ =>
      BoundaryWord.measurable_shiftW.comp ((ha𝒢 ℓ hℓ).prodMk (hγ𝒢 ℓ hℓ))
  have hYkm : Measurable Yk := by
    refine measurable_finPw measurable_const k hAm fun ℓ hℓ => ?_
    have h1 := measurable_flowField_uncurry.comp ((ham ℓ hℓ).prodMk (hZm ℓ hℓ))
    exact h1
  -- the earlier stages, almost surely for all of them
  have hpathAll : ∀ᵐ ω ∂P, ∀ ℓ, ℓ < k →
      (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      (ExplState.run κ b jumps spec (fun j => E j ω) ℓ).2.2.2.2.1.IsConformal ∧
      ContinuousOn (fun w => (ExplState.run κ b jumps spec (fun j => E j ω) ℓ).2.2.2.2.1.2.2
        ((ExplState.run κ b jumps spec (fun j => E j ω) ℓ).2.2.2.2.1.2.1 w)) QuantumZipper.H ∧
      IsChartTransport (ExplState.run κ b jumps spec (fun j => E j ω) ℓ).2.2.2.2.1 1 0 (QuantumZipper.chiC κ)
        (h ω) (Y ℓ ω) := by
    refine ae_all_iff.2 fun ℓ => ?_
    by_cases hℓ : ℓ < k
    · exact (hW ℓ hℓ).2.2.1.mono fun ω hω _ => hω
    · exact Eventually.of_forall fun ω h' => absurd h' hℓ
  have hgoodAll : ∀ᵐ ω ∂P, ∀ ℓ, ℓ < k →
      (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      min (instrTime spec ℓ) (E ℓ ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf (instrTime spec ℓ) (E ℓ ω))) := by
    refine ae_all_iff.2 fun ℓ => ?_
    by_cases hℓ : ℓ < k
    · exact (hpost ℓ hℓ).1.mono fun ω hω _ => hω
    · exact Eventually.of_forall fun ω h' => absurd h' hℓ
  -- the chart right after piece `ℓ`, on the event of the last launch `ℓ`
  have hafter : ∀ ω, (∀ ℓ, ℓ < k →
      (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      (ExplState.run κ b jumps spec (fun j => E j ω) ℓ).2.2.2.2.1.IsConformal ∧
      ContinuousOn (fun w => (ExplState.run κ b jumps spec (fun j => E j ω) ℓ).2.2.2.2.1.2.2
        ((ExplState.run κ b jumps spec (fun j => E j ω) ℓ).2.2.2.2.1.2.1 w)) QuantumZipper.H ∧
      IsChartTransport (ExplState.run κ b jumps spec (fun j => E j ω) ℓ).2.2.2.2.1 1 0 (QuantumZipper.chiC κ)
        (h ω) (Y ℓ ω)) → (∀ ℓ, ℓ < k →
      (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      min (instrTime spec ℓ) (E ℓ ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf (instrTime spec ℓ) (E ℓ ω)))) →
      ∀ ℓ, ω ∈ A ℓ → (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.IsConformal ∧
        ContinuousOn (fun w => (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.2
          ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.1 w)) QuantumZipper.H ∧
        IsChartTransport (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1 1 0 (QuantumZipper.chiC κ)
          (h ω) (Yk ω) := by
    intro ω hp hg ℓ hωA
    obtain ⟨hℓ, hlk, hl, hn⟩ := hωA
    obtain ⟨hstop, a₀, ha₀⟩ := last_launch_props hℓ hlk hl hn
    obtain ⟨hconf, hlift, hT⟩ := hp ℓ hℓ hl
    have hgood := hg ℓ hℓ hl hstop
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
    obtain ⟨-, hrun, -⟩ := eq_launch_of_launches spec _ hcθ
    have hregℓ := hreg ℓ hℓ ω
    have hWc : Continuous fun x : ℝ => (retOf (instrTime spec ℓ) (E ℓ ω)).1 x.toNNReal :=
      (continuous_retOf hregℓ hgood).comp continuous_real_toNNReal
    have hW0 : (fun x : ℝ => (retOf (instrTime spec ℓ) (E ℓ ω)).1 x.toNNReal) 0 = 0 := by
      change (E ℓ ω).1 (min (((0 : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) (min (instrTime spec ℓ) (E ℓ ω).2)).toNNReal = 0
      rw [Real.toNNReal_zero, ENNReal.coe_zero, min_eq_left (zero_le (a := min (instrTime spec ℓ) (E ℓ ω).2)),
        ENNReal.toNNReal_zero]
      exact hregℓ.2.1
    have hchart1 : (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.2.1 =
        (ExplState.run κ b jumps spec (fun j => E j ω) ℓ).2.2.2.2.1.loewner
          (fun x : ℝ => (retOf (instrTime spec ℓ) (E ℓ ω)).1 x.toNNReal)
          ((min (instrTime spec ℓ) (E ℓ ω).2).toNNReal : ℝ) := by
      rw [hrun]
      exact chart_launch _ _ _ _ _ hstop
    have hconf1 : (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.2.1.IsConformal := by
      rw [hchart1]; exact hconf.loewner hWc hW0 (NNReal.coe_nonneg _)
    have hlift1 : ContinuousOn (fun w => (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.2.1.2.2
        ((ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.2.1.2.1 w)) QuantumZipper.H := by
      rw [hchart1]; exact hconf.continuousOn_loewner_lift hlift hWc hW0 (NNReal.coe_nonneg _)
    have hT1 : IsChartTransport (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.2.1 1 0
        (QuantumZipper.chiC κ) (h ω) (Zr ℓ ω) := by
      rw [hchart1, InteractingSLE.Chart.loewner_eq_trans, ← recChart_eq_loewner hregℓ hgood]
      have hZ : Zr ℓ ω = recField κ (recOf (instrTime spec ℓ) (E ℓ ω)) (Y ℓ ω) := by
        simp only [hZrdef, pastMap_last_of_launch hl]
      rw [hZ]
      exact IsChartTransport.trans hconf (isConformal_recChart _) hlift (continuousOn_recChart_lift _) hT
        (isChartTransport_recField κ _ _)
    have haω : a ℓ ω = a₀ := by
      simp only [hadef, ha₀, InteractingSLE.Chart.recenter, sub_sub_cancel, Complex.ofReal_re]
    rw [ha₀]
    refine ⟨hconf1.recenter a₀, Chart.continuousOn_recenter_lift hlift1, ?_⟩
    rw [hYk ℓ ω ⟨hℓ, hlk, hl, hn⟩, haω, Chart.recenter_eq_trans]
    exact IsChartTransport.trans hconf1 (isConformal_shiftChart a₀) hlift1 (continuousOn_shiftChart_lift a₀) hT1
      (isChartTransport_shiftChart a₀ _ _)
  refine ⟨βk, Yk, ⟨hβkm, hYkm, ?_, ?_⟩, fun ℓ ω hℓ hlk hl hn => hβk ℓ ω ⟨hℓ, hlk, hl, hn⟩⟩
  · filter_upwards [hpathAll, hgoodAll] with ω hp hg hω
    obtain ⟨ℓ, hωA⟩ := hcover ω hω
    exact hafter ω hp hg ℓ hωA
  · have hkerℓ : ∀ ℓ, ∀ᵐ ω₀ ∂P, ω₀ ∈ A ℓ → IsGFFWithBoundaryData
        (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) Yk (βk ω₀).fn (βk ω₀).jumps := by
      intro ℓ
      by_cases hℓ : ℓ < k
      swap
      · exact Eventually.of_forall fun ω₀ hω₀ => absurd hω₀.1 hℓ
      -- the conditional characteristic functional given the retained past before `k`, on `A ℓ`
      have hCF : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ A ℓ →
          P[fun ω' => Complex.exp (Complex.I * (Zr ℓ ω' φ : ℂ)) | pastSigma κ b jumps spec E k] ω =
            gaussCF (γr ℓ ω) φ := by
        intro φ
        have hXi : Integrable (fun ω' => Complex.exp (Complex.I * (Zr ℓ ω' φ : ℂ))) P :=
          GFF.integrable_exp_I_mul ((measurable_distOn_apply φ).comp (hZm ℓ hℓ))
        have htr : ∀ B, MeasurableSet[pastSigma κ b jumps spec E k] B →
            MeasurableSet[LocalSets.aeSigma (pastSigma κ b jumps spec E (ℓ + 1)) P] (B ∩ A ℓ) := by
          intro B hB
          refine ⟨B ∩ A ℓ, ?_, EventuallyEq.rfl⟩
          rw [pastSigma_eq_comap] at hB
          obtain ⟨C, hC, rfl⟩ := hB
          set pad : PastData (ℓ + 1) → PastData k := fun u i =>
            if hi : (i : ℕ) < ℓ + 1 then u ⟨i, hi⟩ else readRec (fun _ => 0, 0, false) with hpad
          have hpadm : Measurable pad := measurable_pi_iff.2 fun i => by
            by_cases hi : (i : ℕ) < ℓ + 1
            · simp only [hpad, hi, ↓reduceDIte]; exact measurable_pi_apply _
            · simp only [hpad, hi, ↓reduceDIte]; exact measurable_const
          have hset : pastMap κ b jumps spec E k ⁻¹' C ∩ A ℓ =
              pastMap κ b jumps spec E (ℓ + 1) ⁻¹' (pad ⁻¹' C) ∩ A ℓ := by
            ext ω
            simp only [mem_inter_iff, mem_preimage]
            constructor
            · rintro ⟨h1, h2⟩
              refine ⟨?_, h2⟩
              have key := pastMap_eq_pad (κ := κ) spec E (show ℓ + 1 ≤ k by omega) h2.2.2.2
              rw [key] at h1
              exact h1
            · rintro ⟨h1, h2⟩
              refine ⟨?_, h2⟩
              have key := pastMap_eq_pad (κ := κ) spec E (show ℓ + 1 ≤ k by omega) h2.2.2.2
              rw [key]
              exact h1
          rw [hset]
          refine MeasurableSet.inter ?_ (hA𝒢ℓ ℓ hℓ)
          rw [pastSigma_eq_comap]
          exact ⟨pad ⁻¹' C, hpadm hC, rfl⟩
        have htrace := Restart.ae_condExp_eq_of_trace (pastSigma_mono spec E (show ℓ + 1 ≤ k by omega)) h𝒢k
          htr hXi
        filter_upwards [htrace, (hpost ℓ hℓ).2 φ] with ω h1 h2 hω
        rw [h1 hω]
        obtain ⟨-, hlk, hl, hn⟩ := hω
        exact h2 hl (last_launch_props hℓ hlk hl hn).1
      have hK := ae_isGFFWithBoundaryData_condExpKernel h𝒢k (M := A ℓ) (β := γr ℓ)
        (Eventually.of_forall fun ω _ => hβA.2.1 _) (hZm ℓ hℓ) hCF
      filter_upwards [hK, Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢k (hA𝒢 ℓ hℓ),
        Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) h𝒢k (ha𝒢 ℓ hℓ)] with ω₀ hG hmem haK hω₀
      have hYe : (fun ω => flowField (a ℓ ω₀) 0 (Zr ℓ ω))
          =ᵐ[condExpKernel P (pastSigma κ b jumps spec E k) ω₀] Yk := by
        filter_upwards [hmem hω₀, haK] with ω hω ha
        rw [hYk ℓ ω hω, ha]
      rw [hβk ℓ ω₀ hω₀]
      exact isGFFWithBoundaryData_congr_ae (isGFFWithBoundaryData_shiftW (a ℓ ω₀) (hG hω₀)) hYkm hYe
    filter_upwards [ae_all_iff.2 hkerℓ] with ω₀ hk' hω₀
    obtain ⟨ℓ, hωA⟩ := hcover ω₀ hω₀
    exact hk' ℓ hωA

end Step

end GW1W

end Theorem14

end InteractingSLE
