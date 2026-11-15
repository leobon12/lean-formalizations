/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12NightInputs

/-!
# R.7 with constant-angle strips, determination and phase selection assembled

PROVE-WIRE-PARTA. The actual reference-setting route to Proposition 5.1 is used.
The extremal frontier consists of the phase means and the killed candidate laws.
The outer completion is still an independent mathematical input.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (chiC)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire
open Sec7 Sec7.R7Leaves Sec7.RefWire

/-- R.7 at the current frontier. The source constant-angle strip construction
discharges `hstrip`; Aux. 122 selects the extremal phase from the retained means. -/
theorem night_r7Reference
    (hRect : ∀ κ, ZhanGT4.A1Core.A1DualCouplingG3RectStatement κ)
    (hRectEight : ∀ κ, ZhanGT4.A1Core.A1DualCouplingEightRectStatement κ)
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hRetarget : Sec5.TwoMark.FirstMarkRetargetUpToStatement.{0})
    (hQ : Sec5.FrameQ.QScheduleFirstHitStatement.{0})
    (hlaws : Hsd.Fig51CandLawsStatement
      (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)))
    (hmeans : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      PhaseSide.R7PhaseMeansRemaining.{0} k rL rR (π * chiC (16 / k)) 0)
    (hOuter : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      k / 2 - 4 < max rL rR → OuterPocketCompletion.{0} k rL rR) :
    R7.R7ReferenceStatement.{0} := by
  have hA := late_partAInputs (late_coreG3 hRect) (late_coreEight hRectEight)
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h47 hA
  have h51 := night_prop51 hA hDy hRetarget
  have h44 : AdmCode.Theorem12ParamCond44Statement.{0} :=
    late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)
  have hFH := Sec5.FrameQ.stagedPrefixFirstHitStatement_of_qScheduleFirstHit hA hQ
  apply r7ReferenceStatement_of_remaining h411 h51
    (aux7_of_sixteen_div fun κ hκ hκ4 => Sec5.aux7Statement_sixteen_div_of_partA_of_clearance hA hκ hκ4)
    (fun k hk4 rL rR hL hR hmax => ?_) hOuter
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hc : 0 ≤ π * chiC (16 / k) :=
    mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hside : Hsd.R7PhaseSideRemaining.{0} k rL rR (π * chiC (16 / k)) 0 :=
    PhaseSide.r7PhaseSideRemaining_of_means hk4 hL
    (PhaseSide.lt_sub_six_of_max_eq hk4 hmax).1 hR
    (PhaseSide.lt_sub_six_of_max_eq hk4 hmax).2 (hmeans k hk4 rL rR hL hR hmax)
  have hsd : R7ExtremalSideDetRemaining.{0} k rL rR (π * chiC (16 / k)) 0 :=
    Hsd.r7ExtremalSideDetRemaining_of_phase h44 hA hFH hlaws hk4 hc le_rfl hside
  have hcore : R7ExtremalCoreRemaining.{0} k rL rR (π * chiC (16 / k)) 0 :=
    @r7ExtremalCoreRemaining_of_sideDet.{0} h411 h47
    (fun θ h1 h2 => late_lemma47QHitTStatement hA h1 h2)
    k rL rR (π * chiC (16 / k)) 0 hk4 hL hR hmax hc le_rfl hsd
  exact StripSafe.r7ExtremalRemaining_of_core h44 hk4 hL hR hmax hcore

end InteractingSLE.Wire
