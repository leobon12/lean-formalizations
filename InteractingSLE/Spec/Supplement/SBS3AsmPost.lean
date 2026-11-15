/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3TerminalAfterReg
import InteractingSLE.Spec.Supplement.SBS3TerminalExposed
import InteractingSLE.Spec.Supplement.SBS3MarkedIdentify

/-!
# Lemma S3: the post-stop actual mean with its explicit stop word

Worker PROVE-R6-CORNER (Theorem 1.4, Lemma S3, specification pp. 579–580). PROVE-T14-S3's
`exists_postMean_interiorStageSides(_reg)` selects an actual post-stop mean with a conditional word, but the word is
existential. Lemma S3 needs the **exact** exposed value `−λ − ϑχ` of the second history, which is a property of the
explicit stop word `stopWord κ (β₀, θ_k, record)` (`stopWord_exposed_value_from_real_seed`). The same construction
is re-run here and additionally exports:

* off both mark sets, the selected word equals the explicit stop word of a stage witness `β₀`
  (`ae_eq_word_values_of_common_chart`: both words describe the conditional law of the same transported field);
* the run chart after the launch is the previous run chart composed with the Loewner chart of the record.

`exists_postMean_stopWord` (everywhere-regular family), `exists_postMean_stopWord_reg` (R51 histories).
Theorems 1.2 (parametric) and 1.3 are the explicit R48 inputs, as in PROVE-T14-S3's original.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3.Asm

open Exist Exist.Staged Exist.StagedLaw Restart LocalSets

/-- **The post-stop actual mean with its explicit stop word** (everywhere-regular family). As
`exists_postMean_interiorStageSides`, and moreover: off both mark sets the selected word agrees with the explicit stop
word `stopWord κ (β₀, θ_k, record)` of a stage witness `β₀`, and the run chart after the launch is the previous run
chart composed with the Loewner chart of the record. -/
theorem exists_postMean_stopWord
    (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (k : ℕ) :
    ∃ (A : Ω → Set ℂ) (g : Ω → DistOn upperHalfPlaneOpens) (β β₀ : Ω → BoundaryWord),
      Measurable[mΩ, hittingSigma] A ∧ (∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) ∧
      (∀ᵐ ω ∂P, A ω = WalkLaw.stageSet κ b jumps spec E (k + 1) ω) ∧
      IsLocalSetMean A (WholeField.centredField h u₀) P g ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        min (instrTime spec k) (E k ω).2 ≠ ⊤ →
        (β ω).IsSorted ∧
        (∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
            g ω φ = ∫ z, v z * φ z) →
          EqOn (fun z => v z + u₀ z + chiC κ *
              (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.2.1.2.2 z)
            (fun z => (β ω).mean ((ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.2.1.1 z))
            (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.2.1.dom) ∧
        (∀ x : ℝ, x ∉ (β ω).jumps →
          x ∉ (stopWord κ (β₀ ω, instrAngle spec k,
            pastMap κ b jumps spec E (k + 1) ω (Fin.last k))).jumps →
          (β ω).fn x = (stopWord κ (β₀ ω, instrAngle spec k,
            pastMap κ b jumps spec E (k + 1) ω (Fin.last k))).fn x) ∧
        (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.2.1 =
          (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.loewner
            (rdrv (pastMap κ b jumps spec E (k + 1) ω (Fin.last k)))
            (rtime (pastMap κ b jumps spec E (k + 1) ω (Fin.last k))) := by
  obtain ⟨hAvoid, hOpen, hMarked⟩ :=
    Lcd.stageSet_markedLocal_of_thm12_thm13 h12p h13 hκ hκ4 hb hh hE hreg hu₀ (k + 1)
  let 𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ} := ⟨pastSigma κ b jumps spec E (k + 1), hE.2.1 (k + 1)⟩
  obtain ⟨A, hAm, hAc, hAeq, hAloc⟩ := Lcd.exists_lineVersion (P := P) 𝓜
    (fun ω => WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) hOpen hAvoid hMarked
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨g, hg, -⟩ := Lcd.exists_kernel_of_lineVersion 𝓜 hh0 hAm hAc hAloc
  have hA : Measurable[mΩ, hittingSigma] A := hAm.mono 𝓜.2 le_rfl
  have hLocal : IsLocalSet A (WholeField.centredField h u₀) P :=
    ((isLocalSet_tfae hh0 hA (Eventually.of_forall hAc)).out 4 1).2 hAloc.isAvoidanceLocal
  obtain ⟨β, Y, hβ, hY, hsort, hSide, β₀, Y₀, hW, hField⟩ :=
    exists_postWord_interiorStageSides hκ hb hh hE hR hreg k
  have hpost := post_stage (spec := spec) (E := E) (ℓ := k) (β := β₀) (Y := Y₀)
    (GW1W.isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb hh
    (fun j _ => hE.1 j) (fun j _ => hreg j) (hE.2.2.2 k)
    hW.1 hW.2.1 hW.2.2.1 hW.2.2.2
  let G : Set Ω := {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none ∧
    min (instrTime spec k) (E k ω).2 ≠ ⊤}
  have hRec := measurable_lastRetainedRecord (κ := κ) (b := b) (jumps := jumps) spec E k
  have hG : MeasurableSet[pastSigma κ b jumps spec E (k + 1)] G := by
    have he : G = {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} ∩
        {ω | (pastMap κ b jumps spec E (k + 1) ω (Fin.last k)).2.1 ≠ ⊤} := by
      ext ω
      constructor
      · intro hω
        refine ⟨hω.1, ?_⟩
        change (pastMap κ b jumps spec E (k + 1) ω (Fin.last k)).2.1 ≠ ⊤
        rw [pastMap_last_of_launch hω.1]
        exact hω.2
      · intro hω
        refine ⟨hω.1, ?_⟩
        have ht : (pastMap κ b jumps spec E (k + 1) ω (Fin.last k)).2.1 ≠ ⊤ := hω.2
        rw [pastMap_last_of_launch hω.1] at ht
        exact ht
    rw [he]
    exact ((pastSigma_mono spec E (Nat.le_succ k)) _
      (Lv.measurableSet_launch_pastSigma hb hE.1 hreg k)).inter
        (((measurable_fst.comp (measurable_snd.comp hRec)) (measurableSet_singleton ⊤)).compl)
  have hver := Lv.ae_verChart_eq_runChart hR hreg (k + 1)
  -- the chart after the launch, composed form
  have hchart : ∀ᵐ ω ∂P, ω ∈ G →
      (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.2.1 =
        (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.loewner
          (rdrv (pastMap κ b jumps spec E (k + 1) ω (Fin.last k)))
          (rtime (pastMap κ b jumps spec E (k + 1) ω (Fin.last k))) := by
    filter_upwards [hpost.1] with ω hgω hω
    have hrc : recChart (pastMap κ b jumps spec E (k + 1) ω (Fin.last k)) =
        Chart.id.loewner (fun x : ℝ => (retOf (instrTime spec k) (E k ω)).1 x.toNNReal)
          ((min (instrTime spec k) (E k ω).2).toNNReal : ℝ) := by
      rw [pastMap_last_of_launch hω.1]
      exact recChart_eq_loewner (hreg k ω) (hgω hω.1 hω.2)
    rw [← Sec5.CrossCond.Staged.trans_id_loewner, ← recChart_eq, hrc, Sec5.CrossCond.Staged.trans_id_loewner]
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hω.1
    obtain ⟨-, he, -⟩ := eq_launch_of_launches spec (fun j => E j ω) hcθ
    rw [he, chart_launch _ _ _ _ _ hω.2]
    rfl
  have htr' : ∀ {Z : Ω → DistOn upperHalfPlaneOpens}, Z =ᵐ[P] (fun ω => recField κ
      (pastMap κ b jumps spec E (k + 1) ω (Fin.last k)) (Y₀ ω)) → ∀ᵐ ω ∂P, ω ∈ G →
      IsChartTransport (WalkInf.verChart κ b jumps spec E (k + 1) ω) 1 0 (chiC κ) (h ω) (Z ω) := by
    intro Z hZ
    filter_upwards [ae_postTransport_of_stageWitness hW hZ, hpost.1, hver] with ω ht hgω hv hω
    have ht' := ht hω.1
    rw [pastMap_last_of_launch hω.1, recChart_eq_loewner (hreg k ω) (hgω hω.1 hω.2),
      Sec5.CrossCond.Staged.trans_id_loewner] at ht'
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hω.1
    obtain ⟨-, he, -⟩ := eq_launch_of_launches spec (fun j => E j ω) hcθ
    rw [hv]
    change IsChartTransport (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.2.1
      1 0 (chiC κ) (h ω) (Z ω)
    rw [he, chart_launch _ _ _ _ _ hω.2]
    exact ht'
  have htr := htr' hField
  have htrZ := htr' (EventuallyEq.refl _ _)
  have hAD : ∀ᵐ ω ∂P, ω ∈ G →
      ((WalkInf.verChart κ b jumps spec E (k + 1) ω).dom : Set ℂ) ⊆ H \ A ω ∧
        IsOpen ((H \ A ω) \ (WalkInf.verChart κ b jumps spec E (k + 1) ω).dom) := by
    filter_upwards [hver, hAeq, ae_clopen_runChart_stageSet_after_finite hR k] with ω hv ha hd hω
    rw [hv, ha]
    exact hd hω.1 hω.2
  have hm := ae_eqOn_mean_of_kernelWord (hE.2.1 (k + 1)) (retainedChartData_verChart hb hE.1 hreg (k + 1))
    hh hu₀ hY hG (Eventually.of_forall fun ω _ => hsort ω) htr
    (hSide.mono fun _ hs hω => (hs hω.1 hω.2).2) hA hLocal hAloc hAD hg
  -- the selected word is the explicit stop word off both mark sets
  have hconf : ∀ᵐ ω ∂P, ω ∈ G → (WalkInf.verChart κ b jumps spec E (k + 1) ω).IsConformal := by
    filter_upwards [hver, GW1W.regLaunches_of_stagedPiecesRegular hR] with ω hv hr _
    rw [hv]
    exact (GW2aCont.isConformal_runChart spec (fun j => E j ω) (k + 1) fun j _ c θ hl => hr j c θ hl).1
  have hid := ae_eq_word_values_of_common_chart (hE.2.1 (k + 1))
    (γ := fun ω => stopWord κ (β₀ ω, instrAngle spec k, pastMap κ b jumps spec E (k + 1) ω (Fin.last k)))
    hG hconf (Eventually.of_forall fun ω _ => ⟨hsort ω, isSorted_stopWord κ _⟩) htr htrZ
    (hSide.mono fun _ hs hω => (hs hω.1 hω.2).2)
    ((postWord_kernel_of_stageWitness hκ hb hh hE hreg hW).mono fun _ hs hω => hs hω.1 hω.2)
  refine ⟨A, g, β, β₀, hA, hAc, hAeq, hg, ?_⟩
  filter_upwards [hm, hver, hid, hchart] with ω hmω hv hidω hchω hl hfin
  refine ⟨hsort ω, ?_, hidω ⟨hl, hfin⟩, hchω ⟨hl, hfin⟩⟩
  intro v hvharm hrep
  have he := hmω ⟨hl, hfin⟩ v hvharm hrep
  rw [hv] at he
  exact he

/-- **The post-stop actual mean with its explicit stop word**, for the original R51 history (regular launched pieces
almost surely; the proof runs on the regularized drivers). -/
theorem exists_postMean_stopWord_reg
    (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (k : ℕ) :
    ∃ (A : Ω → Set ℂ) (g : Ω → DistOn upperHalfPlaneOpens) (β β₀ : Ω → BoundaryWord),
      Measurable[mΩ, hittingSigma] A ∧ (∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) ∧
      (∀ᵐ ω ∂P, A ω = WalkLaw.stageSet κ b jumps spec E (k + 1) ω) ∧
      IsLocalSetMean A (WholeField.centredField h u₀) P g ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        min (instrTime spec k) (E k ω).2 ≠ ⊤ →
        (β ω).IsSorted ∧
        (∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
            g ω φ = ∫ z, v z * φ z) →
          EqOn (fun z => v z + u₀ z + chiC κ *
              (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.2.1.2.2 z)
            (fun z => (β ω).mean ((ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.2.1.1 z))
            (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.2.1.dom) ∧
        (∀ x : ℝ, x ∉ (β ω).jumps →
          x ∉ (stopWord κ (β₀ ω, instrAngle spec k,
            pastMap κ b jumps spec E (k + 1) ω (Fin.last k))).jumps →
          (β ω).fn x = (stopWord κ (β₀ ω, instrAngle spec k,
            pastMap κ b jumps spec E (k + 1) ω (Fin.last k))).fn x) ∧
        (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.2.1 =
          (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.loewner
            (rdrv (pastMap κ b jumps spec E (k + 1) ω (Fin.last k)))
            (rtime (pastMap κ b jumps spec E (k + 1) ω (Fin.last k))) := by
  obtain ⟨A, g, β, β₀, hAm, hAc, hAeq, hg, hm⟩ :=
    exists_postMean_stopWord h12p h13 hκ hκ4 hb hh
      (StagedReg.isStagedHistory_regHist hb hE hR) (WalkLaw.stagedPiecesRegular_regHist hR)
      StagedReg.isRegularDriver_regHist hu₀ k
  refine ⟨A, g, β, β₀, hAm, hAc, ?_, hg, ?_⟩
  · filter_upwards [hAeq, StagedReg.ae_run_regHist hR] with ω ha hr
    rw [ha]
    unfold WalkLaw.stageSet
    rw [hr (k + 1)]
  · filter_upwards [hm, StagedReg.ae_run_regHist hR, StagedReg.ae_pastMap_regHist hR (k + 1)]
      with ω hs hr hp hl hfin
    have hl' : (ExplState.run κ b jumps spec
        (fun j => StagedReg.regHist spec E j ω) (k + 1)).2.2.2.1 k ≠ none := by
      rw [hr (k + 1)]
      exact hl
    have hfin' : min (instrTime spec k) (StagedReg.regHist spec E k ω).2 ≠ ⊤ := by
      simpa only [StagedReg.regHist_snd] using hfin
    obtain ⟨hsort, hmean, hid, hch⟩ := hs hl' hfin'
    rw [hr (k + 1)] at hmean
    rw [hp] at hid
    rw [hr (k + 1), hr k, hp] at hch
    exact ⟨hsort, hmean, hid, hch⟩

end InteractingSLE.Theorem14.SB.S3.Asm
