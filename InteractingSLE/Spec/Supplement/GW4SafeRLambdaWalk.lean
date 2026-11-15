/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRUnion

/-! # GW4: a closed field-determined version of the walk union -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField WalkLaw Sec5.GlueCond Sec5.Cond44Ref

/-- The actual walks have a measurable, everywhere relatively closed
field-determined local-set version. Regularization changes only its null
set version and retains the original walk union almost surely. -/
theorem exists_closed_walk_union_version
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b J)
    {D : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hD : ∀ spec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b J P h spec (D spec))
    (hreg : ∀ spec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b J P spec (D spec))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b J u₀) :
    ∃ A : Ω → Set ℂ, (∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) ∧
      Measurable[mΩ, hittingSigma] A ∧ A =ᵐ[P] walkUnionSet κ b J D ∧
      MeasurableSpace.comap A hittingSigma ≤
        aeSigma (MeasurableSpace.comap (centredField h u₀) inferInstance) P ∧
      IsLocalSet A (centredField h u₀) P := by
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  obtain ⟨hD₁, hreg₁', hrun⟩ := StagedReg.regFam_spec hb hD hreg
  let D₁ := StagedReg.regFam D
  have hreg₁ : ∀ spec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b J P spec (D₁ spec) := fun spec hs =>
    stagedPiecesRegular_regHist (hreg spec hs)
  have hdet := pastDetRegStatement_of_thm12_thm13 h12p h13
  have hR := WalkLeaf.walkMarkedLocalRegAEStatement_of_thm12_thm13 h12p h13
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hL := WalkLeaf.walkMarkedLocalRegAEStatement_of_thm12_thm13 h12p h13
    (θ := Real.pi / 2) ⟨by linarith [Real.pi_pos], le_rfl⟩ false
  obtain ⟨hAev, hAo, hAdet, hAloc⟩ :=
    walkUnion_markedAE hdet hR hL hκ hκ4 hb hh hD₁ hreg₁ hreg₁' hu₀
  have hprR := GW1X.isBoundaryContinuedProgram_walkR b J
  have hprL := GW1X.isBoundaryContinuedProgram_walkL b J
  have hjm : jointPast κ b J D₁ ≤ mΩ :=
    sup_le ((hD₁ _ hprR).2.1 _) ((hD₁ _ hprL).2.1 _)
  obtain ⟨A, hAH, hAeq, hAm⟩ := exists_version_of_aeSigma
    (A := walkUnionSet κ b J D₁)
    (fun ω => union_subset (walkSet_subset_H _ _ _ _ _ ω) (walkSet_subset_H _ _ _ _ _ ω)) hAo hAev
  have hAm' : Measurable[jointPast κ b J D₁, hittingSigma] A :=
    Sec5.Aux61ULoc.measurable_hitting_of_avoid fun U hU hUH => hAm ⟨U, hU⟩ hUH
  let A' := fun ω => relClosureH (A ω)
  have hA'm : Measurable[jointPast κ b J D₁, hittingSigma] A' := measurable_relClosureH.comp hAm'
  have hA'c : ∀ ω, A' ω ⊆ H ∧ IsOpen (H \ A' ω) := fun ω =>
    ⟨Supp8.GB6LineL.relClosureH_subset_H _, Supp8.GB6LineL.isOpen_H_diff_relClosureH _⟩
  have hA'eq : A' =ᵐ[P] walkUnionSet κ b J D₁ := by
    filter_upwards [hAeq, hAo] with ω hEq ho
    exact (relClosureH_eq (hAH ω) (hEq.symm ▸ ho)).trans hEq
  have hA'l := isHistoryAvoidanceLocal_congr_ae hA'eq.symm hAloc
  have hOrig : walkUnionSet κ b J D₁ =ᵐ[P] walkUnionSet κ b J D := by
    filter_upwards [hrun _ hprR, hrun _ hprL] with ω hRω hLω
    simp only [walkUnionSet, walkSet]
    rw [StagedReg.physSet_eq_of_run_eq (hRω _), StagedReg.physSet_eq_of_run_eq (hLω _)]
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  exact ⟨A', hA'c, hA'm.mono hjm le_rfl, hA'eq.trans hOrig,
    hA'm.comap_le.trans hAdet,
    ((isLocalSet_tfae hh0 (hA'm.mono hjm le_rfl) (Eventually.of_forall hA'c)).out 1 4).1 hA'l.isAvoidanceLocal⟩

end InteractingSLE.Theorem14.GW4Fix
