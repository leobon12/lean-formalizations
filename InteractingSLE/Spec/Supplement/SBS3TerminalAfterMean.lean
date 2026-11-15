/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3TerminalAfterChart
import InteractingSLE.Spec.Supplement.SBS3TerminalSelect
import InteractingSLE.Spec.Supplement.SBS3TerminalReg

/-!
# S3: an actual mean with physical labels at a finite terminal stop

Construct the actual explored-set mean after the finite stop. Identify it
with the physically labelled stopped word, using the Gaussian law for the
full post-stop past and the composed physical chart relation. No launch of
the next instruction occurs anywhere in this argument.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart LocalSets

/-- Select an actual post-stop mean and the same conditional word with
physical side labels, including a finite terminal nonlaunch. -/
theorem exists_postMean_interiorStageSides
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
    ∃ (A : Ω → Set ℂ) (g : Ω → DistOn upperHalfPlaneOpens)
        (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      Measurable[mΩ, hittingSigma] A ∧ (∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) ∧
      (∀ᵐ ω ∂P, A ω = WalkLaw.stageSet κ b jumps spec E (k + 1) ω) ∧
      IsLocalSetMean A (WholeField.centredField h u₀) P g ∧
      Measurable[pastSigma κ b jumps spec E (k + 1)] β ∧ Measurable Y ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        min (instrTime spec k) (E k ω).2 ≠ ⊤ →
        (β ω).IsSorted ∧ HasInteriorStageSides κ b jumps spec (fun j => E j ω) (k + 1) (β ω) ∧
        IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E (k + 1)) ω)
          Y (β ω).fn (β ω).jumps ∧
        ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
            g ω φ = ∫ z, v z * φ z) →
          EqOn (fun z => v z + u₀ z + chiC κ *
              (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.2.1.2.2 z)
            (fun z => (β ω).mean ((ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.2.1.1 z))
            (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.2.1.dom := by
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
  have htr : ∀ᵐ ω ∂P, ω ∈ G →
      IsChartTransport (WalkInf.verChart κ b jumps spec E (k + 1) ω) 1 0 (chiC κ) (h ω) (Y ω) := by
    filter_upwards [ae_postTransport_of_stageWitness hW hField, hpost.1, hver] with ω ht hgω hv hω
    have ht' := ht hω.1
    rw [pastMap_last_of_launch hω.1, recChart_eq_loewner (hreg k ω) (hgω hω.1 hω.2),
      Sec5.CrossCond.Staged.trans_id_loewner] at ht'
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hω.1
    obtain ⟨-, he, -⟩ := eq_launch_of_launches spec (fun j => E j ω) hcθ
    rw [hv]
    change IsChartTransport (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.2.1
      1 0 (chiC κ) (h ω) (Y ω)
    rw [he, chart_launch _ _ _ _ _ hω.2]
    exact ht'
  have hAD : ∀ᵐ ω ∂P, ω ∈ G →
      ((WalkInf.verChart κ b jumps spec E (k + 1) ω).dom : Set ℂ) ⊆ H \ A ω ∧
        IsOpen ((H \ A ω) \ (WalkInf.verChart κ b jumps spec E (k + 1) ω).dom) := by
    filter_upwards [hver, hAeq, ae_clopen_runChart_stageSet_after_finite hR k] with ω hv ha hd hω
    rw [hv, ha]
    exact hd hω.1 hω.2
  have hm := ae_eqOn_mean_of_kernelWord (hE.2.1 (k + 1)) (retainedChartData_verChart hb hE.1 hreg (k + 1))
    hh hu₀ hY hG (Eventually.of_forall fun ω _ => hsort ω) htr
    (hSide.mono fun _ hs hω => (hs hω.1 hω.2).2) hA hLocal hAloc hAD hg
  refine ⟨A, g, β, Y, hA, hAc, hAeq, hg, hβ, hY, ?_⟩
  filter_upwards [hSide, hm, hver] with ω hs hmω hv hl hfin
  refine ⟨hsort ω, (hs hl hfin).1, (hs hl hfin).2, ?_⟩
  intro v hvharm hrep
  have he := hmω ⟨hl, hfin⟩ v hvharm hrep
  rw [hv] at he
  exact he

end InteractingSLE.Theorem14.SB.S3
