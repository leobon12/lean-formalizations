/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3RetainedChart
import InteractingSLE.Spec.Supplement.SBS3TerminalSelect

/-!
# S3: the actual marked mean at every finite prefix
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

/-- Identify every harmonic representative of the actual explored-set
mean with the same full retained-word witness. The prefix need not launch. -/
theorem ae_eqOn_stageMean_of_retainedWordWitness
    (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {k : ℕ}
    (htime : HasFiniteOrdinaryTimes spec k)
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : RetainedWordWitness κ b jumps P h spec E k β Y)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hAeq : ∀ᵐ ω ∂P, A ω = WalkLaw.stageSet κ b jumps spec E k ω)
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean A (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
        g ω φ = ∫ z, v z * φ z) →
      EqOn (fun z => v z + u₀ z + chiC κ *
          (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.2 z)
        (fun z => (β ω).mean ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.1 z))
        (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.dom := by
  have hmark₀ := (Lcd.stageSet_markedLocal_of_thm12_thm13 h12p h13 hκ hκ4 hb hh hE hreg hu₀ k).2.2
  have hmark := WalkLaw.isHistoryAvoidanceLocal_congr_ae (hAeq.mono fun _ he => he.symm) hmark₀
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := by
    filter_upwards [hAeq, WalkLaw.ae_isOpen_H_diff_stageSet hR k] with ω he ho
    rw [he]
    exact ⟨WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω, ho⟩
  have hlocal : IsLocalSet A (WholeField.centredField h u₀) P :=
    ((isLocalSet_tfae (isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀) hA hAc).out 4 1).2
      hmark.isAvoidanceLocal
  have hver := Lv.ae_verChart_eq_runChart hR hreg k
  have htr : ∀ᵐ ω ∂P, ω ∈ (univ : Set Ω) →
      IsChartTransport (WalkInf.verChart κ b jumps spec E k ω) 1 0 (chiC κ) (h ω) (Y ω) := by
    filter_upwards [hver, hW.transport] with ω hv ht _
    rw [hv]
    exact ht
  have hAD : ∀ᵐ ω ∂P, ω ∈ (univ : Set Ω) →
      ((WalkInf.verChart κ b jumps spec E k ω).dom : Set ℂ) ⊆ H \ A ω ∧
        IsOpen ((H \ A ω) \ (WalkInf.verChart κ b jumps spec E k ω).dom) := by
    filter_upwards [hver, hAeq, ae_clopen_runChart_stageSet_finite_prefix hR k htime] with ω hv ha hd _
    rw [hv, ha]
    exact hd
  have hm := ae_eqOn_mean_of_kernelWord (hE.2.1 k) (retainedChartData_verChart hb hE.1 hreg k)
    hh hu₀ hW.measurable_field MeasurableSet.univ
    (hW.sorted.mono fun _ hs _ => hs) htr (hW.law.mono fun _ hl _ => hl)
    hA hlocal hmark hAD hg
  filter_upwards [hm, hver] with ω hmω hv v hharm hrep
  have he := hmω (mem_univ ω) v hharm hrep
  rw [hv] at he
  exact he

/-- Construct an actual mean and full physical conditional word together
at an arbitrary finite prefix, including after nonlaunch instructions. -/
theorem exists_retainedMean
    (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (k : ℕ) (htime : HasFiniteOrdinaryTimes spec k) :
    ∃ (A : Ω → Set ℂ) (g : Ω → DistOn upperHalfPlaneOpens)
        (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      Measurable[mΩ, hittingSigma] A ∧ (∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) ∧
      (∀ᵐ ω ∂P, A ω = WalkLaw.stageSet κ b jumps spec E k ω) ∧
      IsLocalSetMean A (WholeField.centredField h u₀) P g ∧
      RetainedWordWitness κ b jumps P h spec E k β Y ∧
      ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
          g ω φ = ∫ z, v z * φ z) →
        EqOn (fun z => v z + u₀ z + chiC κ *
            (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.2 z)
          (fun z => (β ω).mean ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.1 z))
          (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.dom := by
  obtain ⟨hAvoid, hOpen, hMarked⟩ :=
    Lcd.stageSet_markedLocal_of_thm12_thm13 h12p h13 hκ hκ4 hb hh hE hreg hu₀ k
  let 𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ} := ⟨pastSigma κ b jumps spec E k, hE.2.1 k⟩
  obtain ⟨A, hAm, hAc, hAeq, hAloc⟩ := Lcd.exists_lineVersion (P := P) 𝓜
    (fun ω => WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) hOpen hAvoid hMarked
  obtain ⟨g, hg, -⟩ := Lcd.exists_kernel_of_lineVersion 𝓜
    (isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀) hAm hAc hAloc
  have hA : Measurable[mΩ, hittingSigma] A := hAm.mono 𝓜.2 le_rfl
  obtain ⟨β, Y, hW⟩ := exists_retainedWordWitness hκ hb hh hE hR hreg k htime
  exact ⟨A, g, β, Y, hA, hAc, hAeq, hg, hW,
    ae_eqOn_stageMean_of_retainedWordWitness h12p h13 hκ hκ4 hb hh hE hR hreg htime hW hu₀ hA hAeq hg⟩

end InteractingSLE.Theorem14.SB.S3
