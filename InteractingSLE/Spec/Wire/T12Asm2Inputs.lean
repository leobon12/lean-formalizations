/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T12Asm2Refs
import InteractingSLE.Spec.Sec5.ChartRawMembers
import InteractingSLE.Spec.Sec5.StagedRepJSatProof
import InteractingSLE.Spec.Sec5.StagedNTrMarks
import InteractingSLE.Spec.Wire.T12Asm2Amb

/-! # Landed discharges of the Theorem 1.2–1.3 assembly leaves

PROVE-T12-ASSEMBLE2. The leaves of `T12Asm.theorem12Statement_assembled` that landed work now proves:

* the three A.1 C-law directions (`A1G3L2.g3RectLawSndC_holds`, `A1G3Lg.g3RectLawFstC_holds`,
  `A1ESRec.eightRectLawSndC`), hence the R74 Cond44 theorem `cond44Holds` with no input;
* Prop. 5.9's later root stages and node transfer for the concrete node objects (`rootLater`,
  `nodeTransfer`; PROVE-STAGED-REPJ, PROVE-STAGED-NODETRANSFER);
* R.5's phase word from Lemma R.5's conditioned clauses (ruling R85; `wordPhase_of_r5On`, PROVE-R5-ENLARGED), and
  both R.5 binders from their ambient-cover forms (`wordR5On_of_amb`, `outerR5On_of_amb`; `T12Asm2Amb`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
noncomputable section

open scoped Real
open QuantumZipper (chiC)

namespace InteractingSLE.Wire.T12Asm2

open Sec7

/-- G3's small-curve C law on its parameter range (proved for every parameter). -/
theorem g3S : ∀ κ : ℝ, 4 < κ → κ < 8 → ZhanGT4.A1RLaw.G3RectLawSndC κ :=
  fun κ _ _ => ZhanGT4.A1G3L2.g3RectLawSndC_holds κ

/-- G3's large-curve C law on its parameter range (proved for every parameter). -/
theorem g3F : ∀ κ : ℝ, 4 < κ → κ < 8 → ZhanGT4.A1RLaw.G3RectLawFstC κ :=
  fun κ _ _ => ZhanGT4.A1G3Lg.g3RectLawFstC_holds κ

/-- Eight's small-curve C law on its parameter range (proved for every parameter). -/
theorem eightS : ∀ κ : ℝ, 8 ≤ κ → ZhanGT4.A1RLaw.EightRectLawSndC κ :=
  fun κ _ => ZhanGT4.A1ESRec.eightRectLawSndC κ

/-- **R74's Cond44 determination with no input**: `T12Asm.cond44` at the three proved C-law directions. -/
theorem cond44Holds : AdmCode.Theorem12ParamCond44Statement.{0} :=
  T12Asm.cond44 g3S g3F eightS

/-- **Prop. 5.9's later root stages** for the concrete node objects (the leaf does not read the node
noise, so it is PROVE-STAGED-REPJ's `rootLaterOn_s4Objects`). -/
theorem rootLater :
    Night.RootLaterOn cond44Holds (Sec5.CrossCond.StagedNode.nodeObjects cond44Holds) :=
  (Sec5.CrossCond.StagedNode.rootLaterOn_nodeObjects_iff cond44Holds).2
    (Sec5.CrossCond.StagedRepJ.rootLaterOn_s4Objects cond44Holds Sec5.ChartRaw.partAInputs)

/-- **Prop. 5.9's node transfer** (PROVE-STAGED-NODETRANSFER, from clearance Part A). -/
theorem nodeTransfer : Sec5.CrossCond.StagedNComp.NodeTransferStatement cond44Holds :=
  Sec5.CrossCond.StagedNTr.nodeTransferStatement_of_partA cond44Holds Sec5.ChartRaw.partAInputs

/-- Theorem 1.2's R.7 margin `πχ(16/k)` is nonnegative for `4 < k`. -/
theorem margin_nonneg {k : ℝ} (hk4 : 4 < k) : 0 ≤ π * chiC (16 / k) :=
  mul_nonneg Real.pi_pos.le
    (Sec4.chiC_pos (R7.sixteen_div_pos (by linarith)) (R7.sixteen_div_lt_four hk4)).le

/-- **R.5's phase word on the extremal pockets** from Lemma R.5's conditioned clauses (ruling R85) at Theorem 1.2's
margins `(πχ(16/k), 0)` (PROVE-R5-ENLARGED's `r7PhaseWordRemaining_of_r5On`). -/
theorem wordPhase_of_r5On
    (hR5 : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      R5Enl.R7R5RemainingOn.{0} k rL rR (π * chiC (16 / k)) 0) :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      PhaseCont.R7PhaseWordRemaining.{0} k rL rR (π * chiC (16 / k)) 0 :=
  fun k hk4 rL rR hL hR hmax => R5Enl.r7PhaseWordRemaining_of_r5On hk4 (margin_nonneg hk4) le_rfl
    (hR5 k hk4 rL rR hL hR hmax)

/-- The extremal R.5 binder from its ambient-cover form (`R5AmbOn.r7R5RemainingOn_of_amb`). -/
theorem wordR5On_of_amb
    (hR5 : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      R5AmbOn.R7R5AmbRemainingOn.{0} k rL rR (π * chiC (16 / k)) 0) :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      R5Enl.R7R5RemainingOn.{0} k rL rR (π * chiC (16 / k)) 0 :=
  fun k hk4 rL rR hL hR hmax => R5AmbOn.r7R5RemainingOn_of_amb hk4 (margin_nonneg hk4) le_rfl
    (hR5 k hk4 rL rR hL hR hmax)

/-- The outer R.5 binder from its ambient-cover form (`R5AmbOn.r7OuterR5MRemainingOn_of_amb`). -/
theorem outerR5On_of_amb
    (hR5 : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      R5AmbOn.R7OuterR5AmbRemainingOn.{0} k rL rR (π * chiC (16 / k)) 0) :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      OuterContOn.R7OuterR5RemainingOn.{0} k rL rR :=
  fun k hk4 rL rR hL hR hmax => R5AmbOn.r7OuterR5MRemainingOn_of_amb hk4 (margin_nonneg hk4) le_rfl
    (hR5 k hk4 rL rR hL hR hmax)

end InteractingSLE.Wire.T12Asm2
