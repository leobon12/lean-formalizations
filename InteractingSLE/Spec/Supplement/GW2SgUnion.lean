/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SgLoc
import InteractingSLE.Spec.Supplement.GW2RdLocPre
import InteractingSLE.Spec.Sec5.CfGivenBridge
import InteractingSLE.WangWu.ReverseContactMean

/-!
# GW2's stage identity: the counterflow hull with the explored set of a staged program is marked local

Packet PROVE-GW2-RELDET, ruling R106, item (γ6). The instance of `GW2Rd.isHistoryAvoidanceLocal_union_stageSet` for
GW2: the retained set is the inverted counterflow hull `retSet s W ζ`. Its marks come from Theorems 1.2–1.3
(`GW2Rd.exists_retained_marks_rec_gw2` at the angle `0`, i.e. for the original field `h` itself). The centred field
is that of the ORIGINAL boundary data (`u₀` a bounded harmonic extension of `b`, as in
`SB.Lcd.stageSet_markedLocal_of_thm12_thm13`): the angle-`0` flow data and `b` have the same bounded harmonic extension
on `ℍ` (`Exist.eqOn_flowLine_harmonicExtension`), so the two centred fields agree (`WangWu.smoothDist_congr`).

**`exists_union_stageSet_gw2`**: for the original GFF `h`, its counterflow `(W, ζ)` at `s` and ANY staged program
`(spec, E)` of `h` (in particular a GW2 schedule truncated after piece `n` and capped at the current own time), there
are marks `ℋ` of the counterflow (containing the null sets and the counterflow record) such that
`retSet s W ζ ∪ stageSet n` is a history-marked local set of the centred field for `ℋ ⊔ pastSigma n`, with its
avoidance events in `aeSigma (ℋ ⊔ pastSigma n) P`, field-determined marks, and an almost surely open complement.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4). Conditional helper with a distinct name.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Restart Exist Exist.Staged Exist.StagedLaw LocalSets WholeField Supp8.GB6 Supp8.GB6LineL Supp8.GB6LMean
  Supp8.Q3Chain GW2Fb

variable {κ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h h' : Ω → DistOn upperHalfPlaneOpens} {b b' : ℝ → ℝ} {J J' : Finset ℝ} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The counterflow hull with the explored set of a staged program is a marked local set** (Theorems 1.2–1.3). -/
theorem exists_union_stageSet_gw2 (h12 : Exist.Theorem12Statement.{u}) (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hh : IsGFFWithBoundaryData P h b J) (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ) (s : ℝ≥0)
    (hE : IsStagedHistory κ b J P h spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω)) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b J u₀) (n : ℕ) :
    ∃ ℋ : {m : MeasurableSpace Ω // m ≤ mΩ}, Ito.nullSets P ≤ ℋ.1 ∧ Measurable[ℋ.1] (gb6Rec s W ζ) ∧
      (∀ U : Opens ℂ, (U : Set ℂ) ⊆ H →
        MeasurableSet[aeSigma (ℋ.1 ⊔ pastSigma κ b J spec E n) P]
          {ω | Disjoint (retSet s W ζ ω ∪ WalkLaw.stageSet κ b J spec E n ω) U}) ∧
      (∀ᵐ ω ∂P, IsOpen (H \ (retSet s W ζ ω ∪ WalkLaw.stageSet κ b J spec E n ω))) ∧
      ℋ.1 ⊔ pastSigma κ b J spec E n ≤
        aeSigma (MeasurableSpace.comap (centredField h u₀) inferInstance) P ∧
      IsHistoryAvoidanceLocal (ℋ.1 ⊔ pastSigma κ b J spec E n)
        (fun ω => retSet s W ζ ω ∪ WalkLaw.stageSet κ b J spec E n ω) (centredField h u₀) P := by
  -- the angle-`0` flow data and its bounded harmonic extension
  obtain ⟨uh, huh⟩ := Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData κ
    (flowLineRhoL κ b J 0 0) (flowLineRhoR κ b J 0 0) (flowLineXL b J 0) (flowLineXR b J 0)
  have huh' : IsBoundedHarmonicExtension (cfData κ b J) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) uh :=
    huh
  have heq : EqOn uh u₀ H := fun z hz => by
    have h1 := eqOn_flowLine_harmonicExtension hκ hb 0 0 hu₀ huh hz
    simpa only [Complex.ofReal_zero, add_zero, zero_mul] using h1
  have hcen : centredField h uh = centredField h u₀ := by
    funext ω
    simp only [centredField]
    rw [WangWu.smoothDist_congr huh.1.continuousOn hu₀.1.continuousOn heq]
  have hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h uh) P := by
    rw [hcen]
    exact isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have htr : ∀ ω, IsTranslateAddConst 0 (0 * chiC κ) (h ω) (h ω) := fun ω =>
    Sec5.CfGiven.isTranslateAddConst_zero_mul_self (h ω) (chiC κ)
  -- the retained marks
  obtain ⟨ℋ, hnull, hrec, hAr, hℋd, hloc⟩ :=
    exists_retained_marks_rec_gw2 (θ := 0) h12 h13 hκ hb hh hb' hT hcf htr huh' huh hh0 s
  rw [hcen] at hℋd hloc
  refine ⟨ℋ, hnull, hrec, ?_⟩
  exact isHistoryAvoidanceLocal_union_stageSet h12p h13 hκ hκ4 hb hh hE hreg hu₀ n
    (Eventually.of_forall fun ω => isOpen_H_diff_retSet s W ζ ω)
    (fun U hUH => hAr (measurableSet_avoid U.isOpen hUH)) hℋd hloc

end InteractingSLE.Theorem14.GW2Rd
