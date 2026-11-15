/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12LateA2
import InteractingSLE.Spec.Wire.Thm12LateKill
import InteractingSLE.Spec.Sec5.FrameQConsumers
import InteractingSLE.Spec.Sec5.Prop59SchedWire
import InteractingSLE.Spec.Sec5.Prop59NodesFarExp
import InteractingSLE.Spec.Sec5.CrossCondStagedCandFar
import InteractingSLE.Spec.Sec5.Prop513BridgeFrameFig51

/-! # R75: killed stage laws, canonical schedules and parameter-field determination -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal
universe u v
namespace InteractingSLE.Wire
open QuantumZipper LQGMetric Sec4 Sec5 Sec5.Prop59Stage Sec5.Prop59System Sec5.Prop59Tips
  Sec5.Prop513Asm Sec5.Prop59Nodes Sec5.Prop59Sched Sec5.Prop513Schedule
  Sec5.Prop513TreeExtract Sec5.Prop513Target Sec5.Prop513Wire Sec5.StripRevVisit
  Restart Exist Exist.Staged Exist.StagedLaw
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-- The same data-only HistExp is sufficient with R75's killed law, at every universe. -/
theorem late_histExp_unbounded
    (hCrossLeft : Late.CrossLeftKStatement) (hCrossRight : Late.CrossRightKStatement) {κ : ℝ} {Ω : Type u} {Ωa : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Ωa] {P : Measure Ω} {Pa : Measure Ωa}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Pa]
    {D : ℚ → Ω → Set ℂ} {A : ℚ → Set Ω}
    (hκ : 0 < κ) (hκ4 : κ < 4) (X : HistExp κ P Pa D A)
    (hLaw : ∀ r : ℚ, 0 < r → Late.StageLawK κ (P.prod Pa)
      (X.posL r) (X.posR r) (X.rhoL r) (X.rhoR r) (X.system r))
    (r : ℚ) (hr : 0 < r) : ∀ᵐ ω ∂P, ω ∈ A r → ¬ Bornology.IsBounded (D r ω) := by
  apply ae_fst_of_ae_prod (Pa := Pa)
  filter_upwards [Late.ae_not_isBounded_of_stageLawK_init hCrossLeft hCrossRight hκ hκ4 (hLaw r hr)
    (X.stages r hr) (X.initialWord r hr) (fun _ => 0), X.active r hr] with ω h₁ h₂ hω hD
  exact h₁ (h₂ hω) (X.image_bdd r hr ω hD)

/-- The root tip bound uses the killed law, without a threshold continuation. -/
theorem late_tip0UnboundedStatement_of_histExp
    (hCrossLeft : Late.CrossLeftKStatement) (hCrossRight : Late.CrossRightKStatement) {κ : ℝ} {Ω : Type u} {Ωa : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Ωa] {P : Measure Ω} {Pa : Measure Ωa}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Pa]
    {W : ℝ≥0 → Ω → ℝ} {z : ℕ → Ω → ℂ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (X : HistExp κ P Pa (rootTgt W z) fun _ => univ)
    (hLaw : ∀ r : ℚ, 0 < r → Late.StageLawK κ (P.prod Pa)
      (X.posL r) (X.posR r) (X.rhoL r) (X.rhoR r) (X.system r)) :
    Tip0UnboundedStatement P W z := by
  intro r hr
  filter_upwards [late_histExp_unbounded hCrossLeft hCrossRight hκ hκ4 X hLaw r hr] with ω hω
  exact hω (mem_univ ω)

/-- Each node tip bound uses the killed law in the same way. -/
theorem late_tipUnboundedStatement_of_histExp
    (hCrossLeft : Late.CrossLeftKStatement) (hCrossRight : Late.CrossRightKStatement) {κ : ℝ} {Ω : Type u} {Ωa : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Ωa] {P : Measure Ω} {Pa : Measure Ωa}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Pa]
    {W : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ} {z : Ω → ℂ} {S : Ω → Set ℂ}
    (hκ : 0 < κ) (hκ4 : κ < 4) (X : HistExp κ P Pa (nodeTgt W S) (nodeAct γ z))
    (hLaw : ∀ r : ℚ, 0 < r → Late.StageLawK κ (P.prod Pa)
      (X.posL r) (X.posR r) (X.rhoL r) (X.rhoR r) (X.system r)) :
    TipUnboundedStatement P W γ z S := by
  intro r hr
  exact late_histExp_unbounded hCrossLeft hCrossRight hκ hκ4 X hLaw r hr

/-- Canonical schedules discharge input (B); root and node laws are R75's killed laws. -/
theorem late_prop513_comap_of_sched
    (hCrossLeft : Late.CrossLeftKStatement) (hCrossRight : Late.CrossRightKStatement)
    (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{0} κ)
    (hFH : StagedPrefixFirstHitStatement.{u})
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    {Ωa : Type v} [MeasurableSpace Ωa] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]
    (X₀ : HistExp κ P Pa (rootTgt W (extremeAngleTreeNode (capacityTree (driverTree
      (targetSched (theorem12ParamCond44Statement_of_lemma47Q_of_A2 h47 hA2 hA2') (x₀ := x₀) hκ hκ4 hb h))) treeTime))
      fun _ => univ)
    (hL₀ : ∀ r : ℚ, 0 < r → Late.StageLawK κ (P.prod Pa) (X₀.posL r) (X₀.posR r) (X₀.rhoL r) (X₀.rhoR r) (X₀.system r))
    (X : ∀ n, HistExp κ P Pa
      (nodeTgt W (extremeAngleTreeDescendants (capacityTree (driverTree
        (targetSched (theorem12ParamCond44Statement_of_lemma47Q_of_A2 h47 hA2 hA2') (x₀ := x₀) hκ hκ4 hb h))) treeTime
        descendantIndex n))
      (nodeAct γ (extremeAngleTreeNode (capacityTree (driverTree
        (targetSched (theorem12ParamCond44Statement_of_lemma47Q_of_A2 h47 hA2 hA2') (x₀ := x₀) hκ hκ4 hb h)))
        treeTime n)))
    (hL : ∀ n, ∀ r : ℚ, 0 < r →
      Late.StageLawK κ (P.prod Pa) ((X n).posL r) ((X n).posR r) ((X n).rhoL r) ((X n).rhoR r) ((X n).system r)) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap h inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = γ ω := by
  have h44 := theorem12ParamCond44Statement_of_lemma47Q_of_A2 h47 hA2 hA2'
  have hA := partAInputsSixteenDivOfClearance_of_A2 hA2 hA2'
  have hE := isStagedHistory_targetSched h44 hκ hκ4 hb hG
  have hR := stagedPiecesRegular_targetSched h44 hκ hκ4 hb hG
  exact prop513_path_of_partA_reverseVisit_of_clearance h44 hA hκ hκ4 hb (𝒢 := MeasurableSpace.comap h inferInstance) (comap_measurable h)
    hG hcf htr hE hR
    (stripReverseVisitLaw_of_stagedPrefixFirstHit h44 hA hFH hκ hκ4 hb hG hcf htr hE hR)
    (fun n => late_tipUnboundedStatement_of_histExp hCrossLeft hCrossRight hκ hκ4 (X n) (hL n))
    (late_tip0UnboundedStatement_of_histExp hCrossLeft hCrossRight hκ hκ4 X₀ hL₀)

end InteractingSLE.Wire
