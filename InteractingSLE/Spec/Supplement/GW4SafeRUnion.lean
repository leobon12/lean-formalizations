/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkMeanAssembly
import InteractingSLE.Spec.Supplement.GB6LineL3
import InteractingSLE.Spec.Sec5.CrossCondTheta
import InteractingSLE.Spec.Sec5.PostContactLocal
import InteractingSLE.Spec.Sec5.Aux61ULocCore

/-!
# GW4: the walks and an original counterflow prefix form a marked local set

The global union law in Q3.2 of Astra's follow-up 3, before disintegration over the
walks. The incoming walks are field-determined, so their records are conditionally
independent of the counterflow record given the original full field. Proposition
3.7 with histories applies to these original records. Closing the union in the
half-plane preserves the marked locality.

This file does not identify the union mean or assert the relative law after
conditioning on the walks.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW4Fix

open WalkLaw LocalSets WholeField Sec5.GlueCond Sec5.Cond44Ref

/-- The retained walk records together with the original counterflow record at `t`. -/
@[instance_reducible]
def walkCfMarks {Ω : Type*} (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (t : ℝ≥0) : MeasurableSpace Ω :=
  jointPast κ b J E ⊔ MeasurableSpace.comap (cfHistory W ζ) (WangWu.stopSigma t)

/-- Global marked locality of the union at each deterministic original time,
for an everywhere regular staged family. No relative restart is assumed. -/
theorem exists_walkCfUnion_of_regular
    (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b J)
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W ζ)
    (hregW : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ W 0 ω = 0 ∧ Continuous fun t => W t ω)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b J P h spec (E spec))
    (hreg : ∀ spec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b J P spec (E spec))
    (hreg' : ∀ spec k ω, Exist.Staged.IsRegularDriver (E spec k ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b J u₀) :
    ∃ B : ℝ≥0 → Ω → Set ℂ,
      (∀ t, walkCfMarks κ b J E W ζ t ≤ mΩ) ∧
      (∀ t, Measurable[mΩ, hittingSigma] (B t)) ∧
      (∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω)) ∧
      (∀ t, ∀ᵐ ω ∂P, B t ω = relClosureH
        (walkUnionSet κ b J E ω ∪ cfHullQ t (cfHistory W ζ ω))) ∧
      ∀ t, IsHistoryAvoidanceLocal (walkCfMarks κ b J E W ζ t)
        (B t) (centredField h u₀) P := by
  have hdet := pastDetRegStatement_of_thm12_thm13 h12p h13
  have hR := WalkLeaf.walkMarkedLocalRegAEStatement_of_thm12_thm13 h12p h13
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hL := WalkLeaf.walkMarkedLocalRegAEStatement_of_thm12_thm13 h12p h13
    (θ := Real.pi / 2) ⟨by linarith [Real.pi_pos], le_rfl⟩ false
  obtain ⟨hAev, hAo, hAdet, hAloc⟩ :=
    walkUnion_markedAE hdet hR hL hκ hκ4 hb hh hE hreg hreg' hu₀
  have hJle : jointPast κ b J E ≤ mΩ :=
    sup_le ((hE _ (GW1X.isBoundaryContinuedProgram_walkR b J)).2.1 _)
      ((hE _ (GW1X.isBoundaryContinuedProgram_walkL b J)).2.1 _)
  obtain ⟨A, -, hAeq, hAm⟩ := exists_version_of_aeSigma
    (A := walkUnionSet κ b J E)
    (fun ω => union_subset (walkSet_subset_H _ _ _ _ _ ω)
      (walkSet_subset_H _ _ _ _ _ ω)) hAo hAev
  have hAm' : Measurable[jointPast κ b J E, hittingSigma] A :=
    Sec5.Aux61ULoc.measurable_hitting_of_avoid fun U hU hUH => hAm ⟨U, hU⟩ hUH
  have hlocA : IsHistoryAvoidanceLocal (jointPast κ b J E) A (centredField h u₀) P :=
    isHistoryAvoidanceLocal_congr_ae (hAeq.mono fun _ hω => hω.symm) hAloc
  have hXm := isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf
  have hKm : ∀ t, Measurable[MeasurableSpace.comap (cfHistory W ζ) (WangWu.stopSigma t),
      hittingSigma] (fun ω => cfHullQ t (cfHistory W ζ ω)) := fun t =>
    (WangWu.measurable_image_negInv.comp (Sec5.CrossCond.measurable_hullAt_stopSigma t)).comp
      (comap_measurable _)
  have hKle : ∀ t, MeasurableSpace.comap (cfHistory W ζ) (WangWu.stopSigma t) ≤ mΩ :=
    fun t => (MeasurableSpace.comap_mono (WangWu.stopSigma_le t)).trans
      (measurable_cfHistory hXm).comap_le
  have hlocK : ∀ t, IsHistoryAvoidanceLocal
      (MeasurableSpace.comap (cfHistory W ζ) (WangWu.stopSigma t))
      (fun ω => cfHullQ t (cfHistory W ζ ω)) (centredField h u₀) P := by
    intro t
    have hk := Sec5.CrossCond.Theta.isHistoryAvoidanceLocal_cfHullQT
      (θ := 0) hcf hκ hregW hu₀.1 t
    change IsHistoryAvoidanceLocal _ _ (fun ω => h ω -
      SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) P
    simpa only [Sec5.CrossCond.Theta.cenTT, zero_mul, Sec5.GlueCond.flowField_zero_zero] using hk
  have hci : ∀ t, LQGMetric.CondIndepEv
      (MeasurableSpace.comap (centredField h u₀) inferInstance) (jointPast κ b J E)
      (MeasurableSpace.comap (cfHistory W ζ) (WangWu.stopSigma t)) P := fun t =>
    Sec5.PostContact.condIndepEv_of_ae_measurableSet_left
      (measurable_centredField hh.1 u₀).comap_le (hKle t) (fun F hF => hAdet F hF)
  refine ⟨fun t ω => relClosureH (A ω ∪ cfHullQ t (cfHistory W ζ ω)),
    fun t => sup_le hJle (hKle t), fun t => ?_, fun t ω => ?_, fun t => ?_, fun t => ?_⟩
  · exact Supp8.GB6LineL.measurable_relClosureH_union (hAm'.mono hJle le_rfl)
      ((hKm t).mono (hKle t) le_rfl)
  · exact ⟨Supp8.GB6LineL.relClosureH_subset_H _,
      Supp8.GB6LineL.isOpen_H_diff_relClosureH _⟩
  · filter_upwards [hAeq] with ω hω
    rw [hω]
  · exact Supp8.GB6LineL.isHistoryAvoidanceLocal_relClosureH
      (WangWu.isHistoryAvoidanceLocal_union hJle (hKle t) le_rfl le_rfl
        hAm' (hKm t) (hci t) hlocA (hlocK t))

/-- The same global marked union for the actual staged family. Regularization
is used only to choose a measurable version of the union; both original walk
records remain among the marks. -/
theorem exists_walkCfUnion
    (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b J)
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b J P h spec (E spec))
    (hreg : ∀ spec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b J P spec (E spec))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b J u₀) :
    ∃ B : ℝ≥0 → Ω → Set ℂ,
      (∀ t, walkCfMarks κ b J E W ζ t ≤ mΩ) ∧
      (∀ t, Measurable[mΩ, hittingSigma] (B t)) ∧
      (∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω)) ∧
      (∀ t, ∀ᵐ ω ∂P, B t ω = relClosureH
        (walkUnionSet κ b J E ω ∪ cfHullQ t (cfHistory W ζ ω))) ∧
      ∀ t, IsHistoryAvoidanceLocal (walkCfMarks κ b J E W ζ t)
        (B t) (centredField h u₀) P := by
  obtain ⟨hE₁, hreg₁', hrun⟩ := StagedReg.regFam_spec hb hE hreg
  let E₁ := StagedReg.regFam E
  have hreg₁ : ∀ spec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b J P spec (E₁ spec) := fun spec hs =>
    stagedPiecesRegular_regHist (hreg spec hs)
  have hregW : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ W 0 ω = 0 ∧ Continuous fun t => W t ω := by
    obtain ⟨b', J', h', -, -, hfl⟩ := hcf
    filter_upwards [Supp8.GB6.ae_driver_zero_continuousOn hfl, hζ] with ω hω hζω
    refine ⟨hζω, hω.1, ?_⟩
    have he : {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} = univ := by
      simp only [hζω, ENNReal.coe_lt_top, ofPred_true]
    exact continuousOn_univ.1 (he ▸ hω.2)
  obtain ⟨B, -, hBm, hBc, hBeq, hBl⟩ := exists_walkCfUnion_of_regular h12p h13 hκ hκ4 hb hh
    hcf hregW hE₁ hreg₁ hreg₁' hu₀
  have hprR := GW1X.isBoundaryContinuedProgram_walkR b J
  have hprL := GW1X.isBoundaryContinuedProgram_walkL b J
  have hUeq : ∀ᵐ ω ∂P, walkUnionSet κ b J E₁ ω = walkUnionSet κ b J E ω := by
    filter_upwards [hrun _ hprR, hrun _ hprL] with ω hR hL
    simp only [walkUnionSet, walkSet]
    rw [StagedReg.physSet_eq_of_run_eq (hR _), StagedReg.physSet_eq_of_run_eq (hL _)]
  have hjp : ∀ D : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      jointPast κ b J D = MeasurableSpace.comap (fun ω =>
        (Exist.Staged.pastMap κ b J (boundaryWalkSpec b J (-(Real.pi / 2)) true)
          (D (boundaryWalkSpec b J (-(Real.pi / 2)) true))
          (boundaryWalkSpec b J (-(Real.pi / 2)) true).2.2.length ω,
        Exist.Staged.pastMap κ b J (boundaryWalkSpec b J (Real.pi / 2) false)
          (D (boundaryWalkSpec b J (Real.pi / 2) false))
          (boundaryWalkSpec b J (Real.pi / 2) false).2.2.length ω)) inferInstance :=
    fun _ => (MeasurableSpace.comap_prodMk _ _).symm
  have hJJ : jointPast κ b J E ≤ aeSigma (jointPast κ b J E₁) P := by
    rw [hjp E, hjp E₁]
    apply StagedReg.comap_le_aeSigma
    filter_upwards [StagedReg.ae_pastMap_regHist (hreg _ hprR)
      (boundaryWalkSpec b J (-(Real.pi / 2)) true).2.2.length,
      StagedReg.ae_pastMap_regHist (hreg _ hprL)
        (boundaryWalkSpec b J (Real.pi / 2) false).2.2.length] with ω hR hL
    exact Prod.ext hR hL
  have hle : ∀ t, walkCfMarks κ b J E W ζ t ≤ aeSigma (walkCfMarks κ b J E₁ W ζ t) P :=
    fun t => sup_le (hJJ.trans (WalkLaw.aeSigma_mono (P := P) le_sup_left))
      (le_sup_right.trans (le_aeSigma _ P))
  have hXm := isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf
  refine ⟨B, fun t => sup_le (sup_le ((hE _ hprR).2.1 _) ((hE _ hprL).2.1 _))
    ((MeasurableSpace.comap_mono (WangWu.stopSigma_le t)).trans
      (measurable_cfHistory hXm).comap_le), hBm, hBc, fun t => ?_, fun t => ?_⟩
  · filter_upwards [hBeq t, hUeq] with ω hB hU
    exact hB.trans (congrArg (fun S => relClosureH (S ∪ cfHullQ t (cfHistory W ζ ω))) hU)
  · exact WalkMean.isHistoryAvoidanceLocal_of_le_aeSigma (hle t) (hBl t)

end InteractingSLE.Theorem14.GW4Fix
