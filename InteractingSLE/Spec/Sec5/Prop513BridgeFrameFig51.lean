/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513BridgeFrameQWord

/-!
# Proposition 5.13 for the canonical Fig. 5.1 counterflow word

The actual parameter field records the counterflow of the source Q-field.
The boundary identity, inverse transport and Gaussian law are all proved.
Only the first-hit, experiment and stage-law inputs of the canonical schedule
assembly remain. These theorems supply the parameter and centred `h513` forms.
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

/-- Parameter-field determination for the recorded counterflow of the canonical
Fig. 5.1 Q-field. No source field, frame law or boundary equality is assumed. -/
theorem prop513_comap_of_sched_fig51_frame
    (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{0} κ)
    (hFH : StagedPrefixFirstHitStatement.{u})
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {hP : Ω → DistOn upperHalfPlaneOpens}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hfl : IsFlowLineDriver (16 / κ)
      (counterflowData κ (stripQHData κ (Real.exp (π * x₀))
        (fig51Lower a b) (fig51Upper x₀ a' b')))
      (counterflowJumps (stripQHJumps (Real.exp (π * x₀)) {0} {x₀})) 0 P hP W ζ)
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
  exact prop513_comap_of_sched_frame h47 hA2 hA2' hFH hκ hκ4 hb
    (isPiecewiseConstant_counterflowData κ
      (isPiecewiseConstantBoundaryData_stripQHData (Real.exp_pos _)
        (isPiecewiseConstantBoundaryData_fig51Lower a b)
        (isPiecewiseConstantBoundaryData_fig51Upper x₀ a' b')))
    hfl (counterflowData_fig51_eq_off_union hκ) htr X₀ hL₀ X hL

/-- The literal centred-field `h513` used by the side-law consumers, now with
both concrete frame obligations and the canonical boundary identity discharged. -/
theorem prop513_comap_centred_of_sched_fig51_frame
    (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{0} κ)
    (hFH : StagedPrefixFirstHitStatement.{u})
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {hP : Ω → DistOn upperHalfPlaneOpens}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hfl : IsFlowLineDriver (16 / κ)
      (counterflowData κ (stripQHData κ (Real.exp (π * x₀))
        (fig51Lower a b) (fig51Upper x₀ a' b')))
      (counterflowJumps (stripQHJumps (Real.exp (π * x₀)) {0} {x₀})) 0 P hP W ζ)
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
  exact prop513_comap_of_sched_fig51_frame h47 hA2 hA2' hFH hκ hκ4 hb hfl htr X₀ hL₀ X hL

end InteractingSLE.Sec5.Prop513Bridge
