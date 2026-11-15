/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfStepZero
import InteractingSLE.Spec.Sec5.QSchedBase

/-!
# Integrability and record geometry under the two (4.4) height bounds

Packet PROVE-CFCHART2. Reuse the height-free integrability adapter and the
given-space (4.4) good-history construction. No uniform strip bound is needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CfStep

open CfConv CfGiven Exist Exist.Staged Exist.StagedLaw Restart LawUnique Lemma47Angle
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47
open Sec7.StripHeights44 (IsHeightBounded44)

/-- Image integrability follows from any positive chart base: its proof needs no
height bounds beyond the ones used to construct that base. -/
theorem converted44IntegrableOn_of_base (hBase : QSched.PositiveChartBase44Statement.{u}) :
    QSched.Converted44IntegrableOn.{u} := by
  intro κ b J Ω mΩ hSB P hP h W ζ hκ hκ4 hb hh hcf hζ θ hθ hθh hπh D hDm hDreg hD s hs η hη φ
  obtain ⟨d, h𝒢, _, _, _, _, _, _, hV0, hVc, _, _, hchart, _⟩ :=
    hBase κ b J P h W ζ hκ hκ4 hb hh hcf hζ θ hθ hθh hπh D hDm hDreg hD s hs η hη
  exact CfResume.integrable_imgField_of_chartConst hκ hh.1 h𝒢 hV0 hVc hchart φ

/-- The (4.4) integrability leaf is proved from Part A and the existing reference. -/
theorem converted44IntegrableOn (hA : PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) : QSched.Converted44IntegrableOn.{u} :=
  converted44IntegrableOn_of_base (QSched.positiveChartBase44Statement hA href)

/-- The (4.4) good histories supply infinite flow lifetime and interiority of the
supplied counterflow trace, including the facts required at prefix time zero. -/
theorem ae_top_and_interior_of44 {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' W : ℝ≥0 → Ω → ℝ} {ζ' ζ : Ω → ℝ≥0∞}
    {η : Ω → ℝ≥0 → ℂ} (hA : PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hθh : IsHeightBounded44 κ b J θ) (hπh : IsHeightBounded44 κ b J (π / 2))
    (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) (hD : IsFlowLineDriver κ b J θ P h W ζ)
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) :
    (∀ᵐ ω ∂P, ζ ω = ⊤) ∧
      ∀ᵐ ω ∂P, ∀ u : ℝ≥0, 0 < u → WangWu.negInv (η ω u) ∈ H := by
  obtain ⟨h', 𝓕, VL, VR, B, N, E, hι, _, _, _, _, _, hEg, _, hEae, _⟩ :=
    QSched.exists_chartCanon_omega44 hA href hκ hκ4 hb hcf hθh hπh hθ hD
      (s := 1) zero_lt_one
  constructor
  · filter_upwards [hEae] with ω hω
    exact (hEg _ hω).1.1
  · filter_upwards [hEae, CfConv.ae_histLine_cfHistory_eq hcf hζ' hη] with ω hω he u hu
    have hm := histLine_mem_H (hEg _ hω) (show (0 : ℝ) < u from hu)
    rw [he] at hm
    exact WangWu.negInv_mem_H (by simpa only [Real.toNNReal_coe] using hm)

/-- Strict separation for the literal source record marks under the two (4.4)
height bounds. The deterministic strict-image adapter is unchanged. -/
theorem ae_record_strict_of44 {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hA : PartAInputsSixteenDivOfClearance) (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hθh : IsHeightBounded44 κ b J θ) (hπh : IsHeightBounded44 κ b J (π / 2))
    (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hDreg : ∀ ω, IsRegularDriver (D ω))
    (hD : IsFlowLineDriver κ b J θ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2))
    {s : ℝ≥0} (hs : 0 < s) :
    let x := qxLT κ θ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0)
    let y := qxRT κ θ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0)
    ∀ᵐ ω ∂P, StrictAnti (recordXL s x (recOf (s : ℝ≥0∞) (D ω))) ∧
      StrictMono (recordXR s y (recOf (s : ℝ≥0∞) (D ω))) := by
  obtain ⟨h', 𝓕, VL, VR, B, N, E, hι, _, _, _, _, _, hEg, _, hEae, _⟩ :=
    QSched.exists_chartCanon_omega44 hA href hκ hκ4 hb hcf hθh hπh hθ hD hs
  dsimp only
  filter_upwards [hEae] with ω hω
  exact CfNext.record_strict_of_good
    (fun i => (isOrderedForceWord_qx_angle κ θ _ _ _ _).2.1 i)
    (fun j => (isOrderedForceWord_qx_angle κ θ _ _ _ _).2.2.2 j)
    (strictAnti_qxL_angle κ θ _ _ _ _) (strictMono_qxR_angle κ θ _ _ _ _)
    (hEg _ hω) (hDreg ω) hs

end InteractingSLE.Sec5.CfStep
