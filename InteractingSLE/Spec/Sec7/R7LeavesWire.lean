/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7LeavesFirst
import InteractingSLE.Spec.Wire.Thm12LateReference

/-!
# Theorem R.7's reference (`hR7Pocket`) with the extremal source leaves discharged

Packet PROVE-R7-LEAVES. A drop-in form of `Wire.late_r7ReferenceFamily` (PROVE-WIRE-PARTA): the same A.1 rectangle
families, reference cover/avoidance (for Proposition 5.1) and outer-pocket completion `hOuter`, but in place of the
extremal reference object `aux131` and its thirty-odd source, side and experiment leaves only

* `hsd` — on every R.7 configuration (heights `c = πχ(16/k)`, `c′ = 0`) and for every version of its walls and
  counterflow: the two-seed side limits and Proposition 5.13 for the counterflow
  (`R7Leaves.R7ExtremalSideDetRemaining`; the wall first exits are proved from Lemma 4.7, `R7Leaves.firstHit_r7`);
* `hstrip` — a strip system on every such configuration (`R7Leaves.R7StripOnConfig`; from Theorem 1.4's
  staged-history construction input by `R7Leaves.r7StripOnConfig_of_construction`), which supplies Aux. lemma 37.

Proposition 4.11 and 5.1 (chart `Q`), Lemma 4.7 (relative angles `π/2` and interior), Aux. lemma 7 at `16/κ` and
`Theorem12ParamCond44Statement` (R74) are obtained exactly as in `Wire.late_r7ReferenceFamily` and
`Wire.late_lemma47QHitTStatement`. The forms with the core inputs `hcore` (first exits included) are kept as
`r7ReferenceStatement_late_leaves` / `…_construction`. R48 is respected (no Theorem 1.2/1.3 input, no `*_of_param`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open QuantumZipper (chiC)
open scoped Real

namespace InteractingSLE.Sec7.R7Leaves

open Wire RefWire

/-- **Theorem R.7's reference** (`hR7Pocket` of Theorem 1.2's wiring) from the A.1 rectangle families, the reference
cover and avoidance of Proposition 5.1, the core extremal inputs `hcore`, strip systems on the R.7 configurations
`hstrip` and the outer-pocket completion `hOuter`. -/
theorem r7ReferenceStatement_late_leaves
    (hRect : ∀ κ, ZhanGT4.A1Core.A1DualCouplingG3RectStatement κ)
    (hRectEight : ∀ κ, ZhanGT4.A1Core.A1DualCouplingEightRectStatement κ)
    (Ref0 : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop)
    (hCover0 : Sec5.Aux61R2.RefClockFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Ref0)
    (hAvoid0 : ∀ κ b J I, Ref0 κ b J I → Sec5.Aux61Win.IsAvoidingRef.{0} κ b J I)
    (hcore : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      R7ExtremalCoreRemaining.{0} k rL rR (π * chiC (16 / k)) 0)
    (hstrip : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      R7StripOnConfig.{0} k rL rR (π * chiC (16 / k)) 0)
    (hOuter : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      κ / 2 - 4 < max rL rR → OuterPocketCompletion.{0} κ rL rR) :
    R7.R7ReferenceStatement.{0} := by
  have hA2 := late_fourForceCrosscutG3LifeStatement (late_coreG3 hRect)
  have hA2' := late_threeForceCrosscutEightStatement (late_coreEight hRectEight)
  have hA := Sec5.partAInputsSixteenDivOfClearance_of_A2 hA2 hA2'
  have h470 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h470 hA
  have h51 := late_prop51QStatement hA Ref0 hCover0 hAvoid0
  have h44 : AdmCode.Theorem12ParamCond44Statement.{0} :=
    late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)
  exact r7ReferenceStatement_of_remaining h411 h51
    (aux7_of_sixteen_div fun κ hκ hκ4 => Sec5.aux7Statement_sixteen_div_of_partA_of_clearance hA hκ hκ4)
    (fun k hk4 rL rR hL hR hmax => r7ExtremalRemaining_of_strip h44 hk4 hL hR hmax
      (hcore k hk4 rL rR hL hR hmax) (hstrip k hk4 rL rR hL hR hmax)) hOuter

/-- `r7ReferenceStatement_late_leaves` with the strip systems from Theorem 1.4's staged-history construction input. -/
theorem r7ReferenceStatement_late_construction
    (hRect : ∀ κ, ZhanGT4.A1Core.A1DualCouplingG3RectStatement κ)
    (hRectEight : ∀ κ, ZhanGT4.A1Core.A1DualCouplingEightRectStatement κ)
    (Ref0 : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop)
    (hCover0 : Sec5.Aux61R2.RefClockFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Ref0)
    (hAvoid0 : ∀ κ b J I, Ref0 κ b J I → Sec5.Aux61Win.IsAvoidingRef.{0} κ b J I)
    (hcore : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      R7ExtremalCoreRemaining.{0} k rL rR (π * chiC (16 / k)) 0)
    (hCon : Theorem14.StagedHistoryConstructionStatement.{0})
    (hOuter : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      κ / 2 - 4 < max rL rR → OuterPocketCompletion.{0} κ rL rR) :
    R7.R7ReferenceStatement.{0} :=
  r7ReferenceStatement_late_leaves hRect hRectEight Ref0 hCover0 hAvoid0 hcore
    (fun k hk4 _ _ _ _ _ => r7StripOnConfig_of_construction hCon hk4
      (mul_nonneg Real.pi_pos.le (Sec4.chiC_pos (R7.sixteen_div_pos (by linarith))
        (R7.sixteen_div_lt_four hk4)).le) le_rfl) hOuter

/-- **Theorem R.7's reference with the wall first exits proved**: as `r7ReferenceStatement_late_leaves`, the core
inputs replaced by the side limits and Proposition 5.13 (`hsd`). -/
theorem r7ReferenceStatement_late_sideDet
    (hRect : ∀ κ, ZhanGT4.A1Core.A1DualCouplingG3RectStatement κ)
    (hRectEight : ∀ κ, ZhanGT4.A1Core.A1DualCouplingEightRectStatement κ)
    (Ref0 : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop)
    (hCover0 : Sec5.Aux61R2.RefClockFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Ref0)
    (hAvoid0 : ∀ κ b J I, Ref0 κ b J I → Sec5.Aux61Win.IsAvoidingRef.{0} κ b J I)
    (hsd : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      R7ExtremalSideDetRemaining.{0} k rL rR (π * chiC (16 / k)) 0)
    (hstrip : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      R7StripOnConfig.{0} k rL rR (π * chiC (16 / k)) 0)
    (hOuter : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      κ / 2 - 4 < max rL rR → OuterPocketCompletion.{0} κ rL rR) :
    R7.R7ReferenceStatement.{0} := by
  have hA2 := late_fourForceCrosscutG3LifeStatement (late_coreG3 hRect)
  have hA2' := late_threeForceCrosscutEightStatement (late_coreEight hRectEight)
  have hA := Sec5.partAInputsSixteenDivOfClearance_of_A2 hA2 hA2'
  have h470 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h470 hA
  refine r7ReferenceStatement_late_leaves hRect hRectEight Ref0 hCover0 hAvoid0
    (fun k hk4 rL rR hL hR hmax => ?_) hstrip hOuter
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{0} θ :=
    fun θ h1 h2 => late_lemma47QHitTStatement hA h1 h2
  exact @r7ExtremalCoreRemaining_of_sideDet.{0} h411 h470 h47T k rL rR (π * chiC (16 / k)) 0 hk4 hL hR hmax
    (mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le) le_rfl (hsd k hk4 rL rR hL hR hmax)

/-- `r7ReferenceStatement_late_sideDet` with the strip systems from Theorem 1.4's staged-history construction
input. -/
theorem r7ReferenceStatement_late_sideDet_construction
    (hRect : ∀ κ, ZhanGT4.A1Core.A1DualCouplingG3RectStatement κ)
    (hRectEight : ∀ κ, ZhanGT4.A1Core.A1DualCouplingEightRectStatement κ)
    (Ref0 : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop)
    (hCover0 : Sec5.Aux61R2.RefClockFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Ref0)
    (hAvoid0 : ∀ κ b J I, Ref0 κ b J I → Sec5.Aux61Win.IsAvoidingRef.{0} κ b J I)
    (hsd : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      R7ExtremalSideDetRemaining.{0} k rL rR (π * chiC (16 / k)) 0)
    (hCon : Theorem14.StagedHistoryConstructionStatement.{0})
    (hOuter : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      κ / 2 - 4 < max rL rR → OuterPocketCompletion.{0} κ rL rR) :
    R7.R7ReferenceStatement.{0} :=
  r7ReferenceStatement_late_sideDet hRect hRectEight Ref0 hCover0 hAvoid0 hsd
    (fun k hk4 _ _ _ _ _ => r7StripOnConfig_of_construction hCon hk4
      (mul_nonneg Real.pi_pos.le (Sec4.chiC_pos (R7.sixteen_div_pos (by linarith))
        (R7.sixteen_div_lt_four hk4)).le) le_rfl) hOuter

end InteractingSLE.Sec7.R7Leaves
