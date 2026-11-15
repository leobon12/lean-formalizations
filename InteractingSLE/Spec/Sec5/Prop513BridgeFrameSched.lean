/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513BridgeFrameWord
import InteractingSLE.Spec.Sec5.Prop59SchedWire

/-!
# Proposition 5.13 from the actual parameter field and canonical schedules

The source field is explicitly recovered from the recorded parameter field.
Its Gaussian law and chart transport are proved by the inverse-frame modules.
Input (B) is discharged by `Prop59Sched.prop513_comap_of_sched`. The only
additional identification premise is the exact recorded boundary-word equality;
no source field, source covariance, chart-transport or history-family input is
assumed here. First-hit, experiment and stage-law inputs remain unchanged.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped Real NNReal ENNReal
open QuantumZipper LQGMetric
open SupercriticalConformalCovariance.GM24 (smoothDist)
universe u v

namespace InteractingSLE.Sec5.Prop513Bridge
open Sec4 Sec7.StripSysField Prop513Schedule Prop513Target Prop513TreeExtract
open Prop513Asm Prop59Sched Prop59Stage Prop59System StripRevVisit
open Restart Exist Exist.Staged Exist.StagedLaw

/-- The concrete Fig. 5.1 field on the original sample space, with the actual
counterflow coefficients and inherited logarithmic branch. -/
def fig51Source {Ω : Type*} (κ x₀ : ℝ) (hP : Ω → DistOn upperHalfPlaneOpens) :
    Ω → DistOn upperHalfPlaneOpens :=
  fun ω => parameterSource (Real.exp_pos (π * x₀)) (-(π * chiC κ))
    (chiC (16 / κ)) (hP ω)

/-- Parameter-field determination through the canonical schedule assembly.
Both former frame hypotheses are discharged for `fig51Source`. -/
theorem prop513_comap_of_sched_frame
    (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{0} κ)
    (hFH : StagedPrefixFirstHitStatement.{u})
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {hP : Ω → DistOn upperHalfPlaneOpens} {bP : ℝ → ℝ} {JP : Finset ℝ}
    (hbP : IsPiecewiseConstantBoundaryData bP JP)
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hfl : IsFlowLineDriver (16 / κ) bP JP 0 P hP W ζ)
    (hword : ∀ x ∉ JP ∪ Prop513Field.jumps (Real.exp (π * x₀)) (stripHJumps {0} {x₀}),
      bP x = stripCounterflowData κ 0 (Real.exp (π * x₀))
        (fig51Lower a b) (fig51Upper x₀ a' b') x)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    {Ωa : Type v} [MeasurableSpace Ωa] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]
    (X₀ : HistExp κ P Pa (rootTgt W (extremeAngleTreeNode (capacityTree (driverTree
      (targetSched (theorem12ParamCond44Statement_of_lemma47Q_of_A2 h47 hA2 hA2') (x₀ := x₀) hκ hκ4 hb (fig51Source κ x₀ hP)))) treeTime))
      fun _ => univ)
    (hL₀ : ∀ r : ℚ, 0 < r → Prop59StageLawStatement κ (P.prod Pa) (X₀.rhoL r) (X₀.rhoR r) (X₀.system r))
    (X : ∀ n, HistExp κ P Pa
      (nodeTgt W (extremeAngleTreeDescendants (capacityTree (driverTree
        (targetSched (theorem12ParamCond44Statement_of_lemma47Q_of_A2 h47 hA2 hA2') (x₀ := x₀) hκ hκ4 hb (fig51Source κ x₀ hP)))) treeTime
        descendantIndex n))
      (nodeAct γ (extremeAngleTreeNode (capacityTree (driverTree
        (targetSched (theorem12ParamCond44Statement_of_lemma47Q_of_A2 h47 hA2 hA2') (x₀ := x₀) hκ hκ4 hb (fig51Source κ x₀ hP))))
        treeTime n)))
    (hL : ∀ n, ∀ r : ℚ, 0 < r →
      Prop59StageLawStatement κ (P.prod Pa) ((X n).rhoL r) ((X n).rhoR r) ((X n).system r)) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ,
      (∀ t, StronglyMeasurable[MeasurableSpace.comap hP inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = γ ω := by
  have hG := Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver
    (div_pos (by norm_num) hκ) hbP hfl
  have hGF := isStripGFF_parameterSource_of_word hκ hbP hG hword
  have hTF : ∀ ω, IsChartTransport (stripCounterflowChart (Real.exp (π * x₀)))
      (-1) (-(π * chiC κ)) (chiC (16 / κ)) (fig51Source κ x₀ hP ω) (hP ω) :=
    fun ω => isChartTransport_parameterSource (Real.exp_pos _) _ _ (hP ω)
  have hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P
      (fig51Source κ x₀ hP) W ζ := by
    refine ⟨bP, JP, hP, hbP, ?_, hfl⟩
    simpa only [zero_add] using hTF
  obtain ⟨Γ', hm, he⟩ := prop513_comap_of_sched
    h47 hA2 hA2' hFH hκ hκ4 hb hGF hcf htr X₀ hL₀ X hL
  refine ⟨Γ', ?_, he⟩
  intro t
  rw [← comap_eq_strip_parameter (Real.exp_pos _) hTF]
  exact hm t

/-- The centred-field `h513` used by the strip and Aux. 131 side-law consumers,
now through the canonical schedules and the concrete source frame. -/
theorem prop513_comap_centred_of_sched_frame
    (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{0} κ)
    (hFH : StagedPrefixFirstHitStatement.{u})
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {hP : Ω → DistOn upperHalfPlaneOpens} {bP : ℝ → ℝ} {JP : Finset ℝ}
    (hbP : IsPiecewiseConstantBoundaryData bP JP)
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hfl : IsFlowLineDriver (16 / κ) bP JP 0 P hP W ζ)
    (hword : ∀ x ∉ JP ∪ Prop513Field.jumps (Real.exp (π * x₀)) (stripHJumps {0} {x₀}),
      bP x = stripCounterflowData κ 0 (Real.exp (π * x₀))
        (fig51Lower a b) (fig51Upper x₀ a' b') x)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    {Ωa : Type v} [MeasurableSpace Ωa] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]
    (X₀ : HistExp κ P Pa (rootTgt W (extremeAngleTreeNode (capacityTree (driverTree
      (targetSched (theorem12ParamCond44Statement_of_lemma47Q_of_A2 h47 hA2 hA2') (x₀ := x₀) hκ hκ4 hb (fig51Source κ x₀ hP)))) treeTime))
      fun _ => univ)
    (hL₀ : ∀ r : ℚ, 0 < r → Prop59StageLawStatement κ (P.prod Pa) (X₀.rhoL r) (X₀.rhoR r) (X₀.system r))
    (X : ∀ n, HistExp κ P Pa
      (nodeTgt W (extremeAngleTreeDescendants (capacityTree (driverTree
        (targetSched (theorem12ParamCond44Statement_of_lemma47Q_of_A2 h47 hA2 hA2') (x₀ := x₀) hκ hκ4 hb (fig51Source κ x₀ hP)))) treeTime
        descendantIndex n))
      (nodeAct γ (extremeAngleTreeNode (capacityTree (driverTree
        (targetSched (theorem12ParamCond44Statement_of_lemma47Q_of_A2 h47 hA2 hA2') (x₀ := x₀) hκ hκ4 hb (fig51Source κ x₀ hP))))
        treeTime n)))
    (hL : ∀ n, ∀ r : ℚ, 0 < r →
      Prop59StageLawStatement κ (P.prod Pa) ((X n).rhoL r) ((X n).rhoR r) ((X n).system r))
    (u₀ u : ℂ → ℝ) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ,
      (∀ t, StronglyMeasurable[MeasurableSpace.comap
        (fun ω => WholeField.centredField hP u₀ ω + smoothDist upperHalfPlaneOpens u)
        inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = γ ω := by
  rw [comap_centredField_add]
  exact prop513_comap_of_sched_frame h47 hA2 hA2' hFH hκ hκ4 hb hbP hfl hword htr X₀ hL₀ X hL

end InteractingSLE.Sec5.Prop513Bridge
