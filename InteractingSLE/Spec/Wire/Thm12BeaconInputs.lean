/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12BeaconA1
import InteractingSLE.Spec.Wire.Thm12RelayInputs
import InteractingSLE.Spec.Sec5.TwoMarkTrace12Assembly
import InteractingSLE.Spec.Sec7.PhaseContR7
import InteractingSLE.Spec.Sec7.Aux41OOMixedInf

/-! # R83 A.1, proved two-mark exclusion, and R.7 with outer geometry discharged -/
set_option autoImplicit false
noncomputable section
universe u
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open QuantumZipper (chiC)
open scoped NNReal ENNReal Real
namespace InteractingSLE.Wire.Beacon
open Sec7 Sec7.RefWire Sec7.R7Leaves

/-- S4's recovered root noise and bottom node bases, retaining arbitrary node noise and auxiliary space. -/
def stages (h44 : AdmCode.Theorem12ParamCond44Statement.{0}) (objects : Night.StageObjectsOn) :
    Night.StageObjectsOn :=
  fun {_ _ _ _ _ _} hκ hκ4 hb {_} _ _ P _ h W ζ γ hG hcf htr =>
    { Relay.stages h44 objects hκ hκ4 hb P h W ζ γ hG hcf htr with nodeBase := fun _ _ => ⊥ }

/-- Changing only node bases leaves the recovered root path proof unchanged. -/
theorem rootPath (h44 : AdmCode.Theorem12ParamCond44Statement.{0})
    (hA : Sec5.PartAInputsSixteenDivOfClearance) (objects : Night.StageObjectsOn) :
    Night.RootPathOn h44 (stages h44 objects) := Relay.rootPath h44 hA objects

/-- The concrete node bases satisfy the S4 measurability leaf unconditionally. -/
theorem nodeBase (h44 : AdmCode.Theorem12ParamCond44Statement.{0}) (objects : Night.StageObjectsOn) :
    Night.NodeBaseOn h44 (stages h44 objects) := by
  intro κ x₀ a b a' b' hκ hκ4 hb Ω mΩ hSB P hP h W ζ γ hG hcf htr d n q
  exact bot_le

/-- Proposition 5.1 with the negative two-mark reference proved through the terminal stop. -/
theorem prop51 (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin) :
    Sec5.Cond44Ref.Prop51QStatement.{u} := by
  have hreg := Sec5.CfLineRegQ.cfLineRegularQStatement_of_partA_of_clearance hA
  have htgt := Sec5.Aux61Act.fwdNoEastCrosscutTgtQOn_of_dyCover_refWin hreg hDy
    Sec5.TwoMark.Trace12.r5NegStatement
  apply Sec5.Prop51G.prop51QStatement_of_on Sec5.Prop51G.IsLargeGap
    (Sec5.Prop51H.prop51QOn_largeGap_of_partA_of_clearance hA)
  apply Sec5.Prop51Tgt.prop51QOn_smallGap_of_tgt hreg
  intro κ hκ hκ4 a b θ₁ θ₂ h12 hGap
  exact htgt κ hκ hκ4 a b θ₁ θ₂ h12 True.intro

/-- R.7 from the corrected A.1 cores, R.5 up to phase and the remaining outer phase/visits. -/
theorem r7Reference
    (hG : ∀ κ, ZhanGT4.A1Canon.A1DualCouplingG3CoreStatement κ)
    (hE : ∀ κ, ZhanGT4.A1Canon.A1DualCouplingEightCoreStatement κ)
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hQ : Sec5.FrameQ.QScheduleFirstHitStatement.{0})
    (hLaws : Hsd.Fig51CandLawsStatement (late_theorem12ParamCond44Statement hG hE))
    (hWordPhase : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      PhaseCont.R7PhaseWordRemaining.{0} k rL rR (π * chiC (16 / k)) 0)
    (hOuterCont : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      OuterPhNext.R7OuterPhaseContRemaining.{0} k rL rR)
    (hShared : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      ¬ (rL < k - 6 ∧ rR < k - 6) → OuterPhNext.R7OuterSharedVisitsRemaining.{0} k rL rR) :
    R7.R7ReferenceStatement.{0} := by
  have hA := late_partAInputs hG hE
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h47 hA
  have h51 := prop51 hA hDy
  have h44 := late_theorem12ParamCond44Statement hG hE
  have hFH := Sec5.FrameQ.stagedPrefixFirstHitStatement_of_qScheduleFirstHit hA hQ
  have haux7 : ∀ k : ℝ, 4 < k → Sec4.Aux7Statement.{0} k :=
    aux7_of_sixteen_div fun κ hκ hκ4 => Sec5.aux7Statement_sixteen_div_of_partA_of_clearance hA hκ hκ4
  have hOuter : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      k / 2 - 4 < max rL rR → OuterPocketCompletion.{0} k rL rR := by
    intro k hk rL rR hL hR hmax
    exact HOuter.outerPocketCompletion_of_remaining h411 h51 (haux7 k hk) hk hL hR hmax
      (Aux41OO.r7OuterRemaining_of_side h411 h51 h47
        (fun θ h1 h2 => late_lemma47QHitTStatement hA h1 h2) hA h44 hFH hLaws hk hL hR hmax
        (OuterIn.r7OuterSideRemaining_of_phase hk
          (OuterPhNext.r7OuterPhaseSideRemaining_of_cont_shared hk hL hR
            (hOuterCont k hk rL rR hL hR hmax) (hShared k hk rL rR hL hR hmax))))
  apply r7ReferenceStatement_of_remaining h411 h51 haux7 (fun k hk4 rL rR hL hR hmax => ?_) hOuter
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith only [hk4])
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hc : 0 ≤ π * chiC (16 / k) := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hconst : PhaseClause.R7PhaseConstRemaining.{0} k rL rR (π * chiC (16 / k)) 0 :=
    @PhaseCont.r7PhaseConstRemaining_of_word.{0} k rL rR (π * chiC (16 / k)) 0
      hk4 hc le_rfl (hWordPhase k hk4 rL rR hL hR hmax)
  have hmeans : PhaseSide.R7PhaseMeansRemaining.{0} k rL rR (π * chiC (16 / k)) 0 :=
    @PhaseClause.r7PhaseMeansRemaining_of_const.{0} k rL rR (π * chiC (16 / k)) 0 hk4 hc le_rfl hconst
  have hside : Hsd.R7PhaseSideRemaining.{0} k rL rR (π * chiC (16 / k)) 0 :=
    PhaseSide.r7PhaseSideRemaining_of_means hk4 hL
      (PhaseSide.lt_sub_six_of_max_eq hk4 hmax).1 hR
      (PhaseSide.lt_sub_six_of_max_eq hk4 hmax).2 hmeans
  have hsd : R7ExtremalSideDetRemaining.{0} k rL rR (π * chiC (16 / k)) 0 :=
    Hsd.r7ExtremalSideDetRemaining_of_phase h44 hA hFH hLaws hk4 hc le_rfl hside
  have hcore : R7ExtremalCoreRemaining.{0} k rL rR (π * chiC (16 / k)) 0 :=
    @r7ExtremalCoreRemaining_of_sideDet.{0} h411 h47
      (fun θ h1 h2 => late_lemma47QHitTStatement hA h1 h2)
      k rL rR (π * chiC (16 / k)) 0 hk4 hL hR hmax hc le_rfl hsd
  exact StripSafe.r7ExtremalRemaining_of_core h44 hk4 hL hR hmax hcore

end InteractingSLE.Wire.Beacon
