/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1AsmG3
import InteractingSLE.Spec.Sec5.WordSafeWire
import InteractingSLE.Spec.Sec5.TwoAngWire
import InteractingSLE.Spec.Sec5.StagedS3Wire
import InteractingSLE.Spec.Sec5.StagedRepLaterClause
import InteractingSLE.Spec.Sec7.StripMarksExpGood
import InteractingSLE.Spec.Wire.Thm12DawnInputs
import InteractingSLE.Spec.Sec7.PhaseClauseConst
import InteractingSLE.Spec.Sec7.Aux41OOWireInf
import InteractingSLE.Spec.Sec7.OuterPhNextR7

/-! # Rectangle A.1 and the newest R.7 reductions, with the actual-setting E1 route -/
set_option autoImplicit false
noncomputable section
universe u
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open QuantumZipper (chiC)
open scoped NNReal ENNReal Real
namespace InteractingSLE.Wire.Relay
open Sec7 Sec7.RefWire

/-- G3's rectangle rows, measurability and image laws supply its seeded field statement. -/
theorem field (hRow : ∀ κ, ZhanGT4.A1Asm.G3RectRow κ)
    (hMeas : ∀ κ, ZhanGT4.A1Asm.G3RectMeas κ) (hLaw : ∀ κ, ZhanGT4.A1Asm.G3RectLaw κ) :
    ∀ κ, ZhanGT4.A1Patch.A1DualCouplingG3FieldStatement κ :=
  dawn_fieldG3 fun κ => ZhanGT4.A1Asm.a1DualCouplingG3SeedGStatement_of_rect (hRow κ) (hMeas κ) (hLaw κ)

/-- Eight's rectangle measurability and image laws supply its seeded statement. -/
theorem seedEight (hMeas : ∀ κ, ZhanGT4.A1Asm.EightRectMeas κ)
    (hLaw : ∀ κ, ZhanGT4.A1Asm.EightRectLaw κ) :
    ∀ κ, ZhanGT4.A1EightSeed.A1DualCouplingEightSeedMStatement κ :=
  fun κ => ZhanGT4.A1Asm.a1DualCouplingEightSeedMStatement_of_rect (hMeas κ) (hLaw κ)

/-- The R74 Cond44 theorem is derived before any pocket or staged-law input is used. -/
theorem cond44 (hRow : ∀ κ, ZhanGT4.A1Asm.G3RectRow κ)
    (hMeas : ∀ κ, ZhanGT4.A1Asm.G3RectMeas κ) (hLaw : ∀ κ, ZhanGT4.A1Asm.G3RectLaw κ)
    (hMeas8 : ∀ κ, ZhanGT4.A1Asm.EightRectMeas κ) (hLaw8 : ∀ κ, ZhanGT4.A1Asm.EightRectLaw κ) :
    AdmCode.Theorem12ParamCond44Statement.{0} :=
  late_theorem12ParamCond44Statement (late_coreG3 (night_rectG3 (field hRow hMeas hLaw)))
    (late_coreEight (night_rectEight (seedEight hMeas8 hLaw8)))

/-- Explicit canonical two-angle experiments; physical wall/field objects are unchanged. -/
abbrev words (h44 : AdmCode.Theorem12ParamCond44Statement.{0})
    {Ωw : Current.BothLow → Type} [∀ i, MeasurableSpace (Ωw i)]
    (base : ∀ i, Now.StripObjects (Ωw i))
    (hb : ∀ i, IsPiecewiseConstantBoundaryData (base i).boundary (base i).jumps) :
    ∀ i, Now.StripObjects (Ωw i) :=
  fun i => Sec5.TwoAngle.withTwoAngle h44 i (base i) (hb i)

/-- The constructed experiments satisfy the two-angle strip-system leaf. -/
theorem wordT (h44 : AdmCode.Theorem12ParamCond44Statement.{0})
    {Ωw : Current.BothLow → Type} [∀ i, MeasurableSpace (Ωw i)] [∀ i, StandardBorelSpace (Ωw i)]
    (base : ∀ i, Now.StripObjects (Ωw i)) [∀ i, IsProbabilityMeasure (base i).measure]
    (hb : ∀ i, IsPiecewiseConstantBoundaryData (base i).boundary (base i).jumps)
    (hh : ∀ i, IsGFFWithBoundaryData (base i).measure (base i).field (base i).boundary (base i).jumps)
    (hcf : ∀ i, IsCenteredCounterflowDriver (16 / i.kappa) (base i).measure (base i).field
      (base i).driver (base i).lifetime)
    (hζ : ∀ i, ∀ᵐ ω ∂(base i).measure, (base i).lifetime ω = ⊤)
    (hl : ∀ i, ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ (base i).jumps →
      (base i).boundary y + a * chiC (16 / i.kappa) ≤ -sleLambda (16 / i.kappa))
    (hr : ∀ i, ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ (base i).jumps →
      sleLambda (16 / i.kappa) ≤ (base i).boundary y + a * chiC (16 / i.kappa)) :
    ∀ i, let x := words h44 base hb i; WordSafe.IsTwoAngleStripSystem (16 / i.kappa)
      x.boundary x.jumps x.measure x.field x.driver x.lifetime x.experiment :=
  fun i => (Sec5.TwoAngle.isTwoAngleStripSystem_withTwoAngle h44 i (base i) (hb i)
    (hh i) (hcf i) (hζ i) (hl i) (hr i)).1

open Sec4 Sec5 Sec5.Prop59Sched Sec5.Prop59Pieces Sec5.Prop59System Sec5.Prop59Stage
  Sec5.Prop513TreeExtract Sec5.Prop513Schedule Sec5.Prop513Target Sec5.CrossCond.StagedRepLater
  Restart LawUnique WangWu Sec5.GlueCond Sec5.CrossCond.Word49

/-- Use the recovered root noise while keeping the auxiliary space and node construction unrestricted. -/
def stages (h44 : AdmCode.Theorem12ParamCond44Statement.{0}) (objects : Night.StageObjectsOn) :
    Night.StageObjectsOn :=
  fun {_ x₀ _ _ _ _} hκ hκ4 hb {_} _ _ P _ h W ζ γ hG hcf htr =>
    { objects hκ hκ4 hb P h W ζ γ hG hcf htr with
      rootNoise := rootNoise x₀ h44 hκ hκ4 hb P h W ζ }

/-- The stage-zero root path clause follows from Part A for every supplied node/noise space. -/
theorem rootPath (h44 : AdmCode.Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDivOfClearance) (objects : Night.StageObjectsOn) :
    Night.RootPathOn h44 (stages h44 objects) := by
  intro κ x₀ a b a' b' hκ hκ4 hb Ω mΩ hSB P hP h W ζ γ hG hcf htr d q hq t
  let obj := objects hκ hκ4 hb P h W ζ γ hG hcf htr
  have hr : 0 < (q : ℝ).toNNReal := Real.toNNReal_pos.2 (by exact_mod_cast hq)
  have h1 := Night.rootGood_pieceZ_clearance x₀ h44 hκ hκ4 hb P obj.measure h W ζ
    (targetSched h44 (x₀ := x₀) hκ hκ4 hb h) hA hG hcf (isStagedHistory_targetSched h44 hκ hκ4 hb hG)
    (stagedPiecesRegular_targetSched h44 hκ hκ4 hb hG) (q : ℝ).toNNReal
  have h2 := Sec7.StripMarks.ae_cfHistory_mem_goodSet49_of_clearance hκ hκ4 hb hA hG hcf hr
  have h2' : ∀ᵐ ω' ∂(P.prod obj.measure), Cond44Ref.cfHistory W ζ ω'.1 ∈ goodSet49 (q : ℝ).toNNReal :=
    Measure.quasiMeasurePreserving_fst.ae h2
  show ∀ᵐ ω' ∂(P.prod obj.measure), _
  filter_upwards [h1, h2'] with ω' hω1 hω2 _
  exact clause1_rootCand_of_good x₀ h44 hκ hκ4 hb P h W ζ hG.1 hcf t hω1.1 hω2

/-- R.7 uses only the new continuous-phase, residual geometry and shared-visit leaves.
The determination law is shared; the actual-setting Proposition 5.1 route is retained. -/
theorem r7Reference
    (hRect : ∀ κ, ZhanGT4.A1Core.A1DualCouplingG3RectStatement κ)
    (hRect8 : ∀ κ, ZhanGT4.A1Core.A1DualCouplingEightRectStatement κ)
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hRetarget : Sec5.TwoMark.FirstMarkRetargetUpToStatement.{0})
    (hQ : Sec5.FrameQ.QScheduleFirstHitStatement.{0})
    (hLaws : Hsd.Fig51CandLawsStatement
      (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRect8)))
    (hCont : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      PhaseClause.R7PhaseContRemaining.{0} k rL rR (π * chiC (16 / k)) 0)
    (hGeom : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      Aux41OO.R7OuterGeomRestMixedInf.{0} k rL rR)
    (hOuterCont : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      OuterPhNext.R7OuterPhaseContRemaining.{0} k rL rR)
    (hShared : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      ¬ (rL < k - 6 ∧ rR < k - 6) → OuterPhNext.R7OuterSharedVisitsRemaining.{0} k rL rR) :
    R7.R7ReferenceStatement.{0} := by
  have hA := late_partAInputs (late_coreG3 hRect) (late_coreEight hRect8)
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h47 hA
  have h51 := night_prop51 hA hDy hRetarget
  have h44 := late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRect8)
  have hFH := Sec5.FrameQ.stagedPrefixFirstHitStatement_of_qScheduleFirstHit hA hQ
  have hOuter : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      k / 2 - 4 < max rL rR → OuterPocketCompletion.{0} k rL rR := by
    intro k hk rL rR hL hR hmax
    have haux7 : Sec4.Aux7Statement.{0} k :=
      (R7Leaves.aux7_of_sixteen_div fun κ hκ hκ4 => Sec5.aux7Statement_sixteen_div_of_partA_of_clearance hA hκ hκ4) k hk
    exact HOuter.outerPocketCompletion_of_remaining h411 h51 haux7 hk hL hR hmax
      (Aux41OO.r7OuterRemaining_of_mixedInf h411 h51 h47
        (fun θ h1 h2 => late_lemma47QHitTStatement hA h1 h2) hA h44 hFH hLaws hk hL hR hmax
        (hGeom k hk rL rR hL hR hmax)
        (OuterIn.r7OuterSideRemaining_of_phase hk
          (OuterPhNext.r7OuterPhaseSideRemaining_of_cont_shared hk hL hR
            (hOuterCont k hk rL rR hL hR hmax) (hShared k hk rL rR hL hR hmax))))
  apply night_r7Reference hRect hRect8 hDy hRetarget hQ hLaws (fun k hk rL rR hL hR hmax => ?_) hOuter
  have hc : 0 ≤ π * chiC (16 / k) := mul_nonneg Real.pi_pos.le
    (Sec4.chiC_pos (R7.sixteen_div_pos (by linarith)) (R7.sixteen_div_lt_four hk)).le
  have hconst : PhaseClause.R7PhaseConstRemaining.{0} k rL rR (π * chiC (16 / k)) 0 :=
    PhaseClause.r7PhaseConstRemaining_of_cont hk (hCont k hk rL rR hL hR hmax)
  exact @PhaseClause.r7PhaseMeansRemaining_of_const.{0} k rL rR (π * chiC (16 / k)) 0 hk hc le_rfl hconst

end InteractingSLE.Wire.Relay
