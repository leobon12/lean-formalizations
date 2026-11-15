/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.OuterInGeomAe
import InteractingSLE.Spec.Sec7.OuterInSide

/-!
# Theorem R.7's outer pockets: `HOuter.R7OuterRemaining` from the open source steps, and the drop-ins

Packet PROVE-R7-OUTERIN. PROVE-HOUTER reduced Theorem 1.2's outer-pocket completion `hOuter` to
`HOuter.R7OuterRemaining` (the inputs `geom`, `geomInf`, `side`, `det` of `HOuter.R7OuterInputs` on every R.7
configuration). Here:

* `det` is **proved** (`Hsd.r7_det`: Proposition 5.13 for the R.7 counterflow from Proposition 5.9's per-candidate
  laws `Hsd.Fig51CandLawsStatement`, the same named input as the extremal `hsd.det`);
* `geom`, `geomInf` are **proved** from `R7OuterGeomRemaining` (`OuterGeomInputs` on every configuration: Aux. lemma
  37 along the contained side of the bounded mixed pockets; Aux. 37 along the clipped `β_R` and Aux. 41 for the
  two-outer pockets; Aux. 37, §5.4's gap equality and Aux. 41 for the mixed pockets opening at the flow seed), every
  pathwise configuration fact and the two-outer gap equalities being proved (`OuterInGeomAe`, `OuterInCollarInf`);
* `side` is the named `R7OuterSideRemaining` (or its three parts `R7OuterPhaseSideRemaining`, `OuterInSide`).

* `R7OuterGeomRemaining`; **`r7OuterRemaining_of_inputs`**;
* **`r7ReferenceStatement_late_outerIn`**: the drop-in for `HOuter.r7ReferenceStatement_late_sideDet_outer` with
  `R7OuterRemaining` replaced by `R7OuterGeomRemaining`, `R7OuterSideRemaining` and the per-candidate laws;
* **`r7ReferenceStatement_late_hsd_outerIn`**: the same together with PROVE-HSD's reduction of the extremal `hsd`
  (`Hsd.r7ReferenceStatement_late_hsd`), all side limits in the three-part form.

Conditional helpers; no source theorem is replaced. R48: the named statements are those of the late wiring (A.1's
rectangle families, the reference cover, `QScheduleFirstHitStatement`) and the named inputs listed above; nothing uses
Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open LQGMetric (DistOn)
open QuantumZipper (H Hbar chiC)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.OuterIn

open WholeField R7Outer R7Leaves RefWire HOuter Hsd Wire StripSafe

/-! ### `R7OuterRemaining` from the remaining inputs -/

section Remaining

/-- **The remaining inputs of the outer pockets' geometry on every R.7 configuration** (heights `c = πχ(16/k)`,
`c′ = 0`): for every configuration and every choice of versions of the arms `α_R`, `α_L` and of the counterflow's
trace, `OuterGeomInputs` (with the configuration's certified frontiers `β_R`, `β_L`). -/
def R7OuterGeomRemaining (k rL rR : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR (π * chiC (16 / k)) 0 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
      OuterGeomInputs k rL rR P βR βL R L η

/-- **`HOuter.R7OuterRemaining` from the open source steps**: `geom`, `geomInf` from `R7OuterGeomRemaining`
(`ae_outerGeom`, `ae_outerGeomInf`), `side` from `R7OuterSideRemaining`, `det` from Proposition 5.9's per-candidate
laws (`Hsd.r7_det`). -/
theorem r7OuterRemaining_of_inputs (h411 : Sec5.Cond44Ref.Prop411QStatement.{0})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{0}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{0} θ)
    (hA : Sec5.PartAInputsSixteenDivOfClearance) (h44 : AdmCode.Theorem12ParamCond44Statement.{0})
    (hFH : Sec5.StripRevVisit.StagedPrefixFirstHitStatement.{0}) (hlaws : Fig51CandLawsStatement h44)
    {k rL rR : ℝ} (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR) (hmax : k / 2 - 4 < max rL rR)
    (hgeom : R7OuterGeomRemaining.{0} k rL rR) (hside : R7OuterSideRemaining.{0} k rL rR) :
    R7OuterRemaining.{0} k rL rR := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hc : 0 ≤ π * chiC (16 / k) := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hin := hgeom P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV
  exact ⟨fun q hq => ae_outerGeom h411 h51 h47 h47T hA hk4 hL hR hmax hc le_rfl hcfg hD hV hin q hq,
    fun q hq => ae_outerGeomInf h411 h51 h47 h47T hk4 hL hR hmax hc le_rfl hcfg hD hV hin q hq,
    hside P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV,
    r7_det h44 hA hFH hlaws hk4 hc le_rfl hcfg.gff hcfg.counterflow hD hV.η_trace⟩

end Remaining

/-! ### The drop-ins for Theorem 1.2's late wiring -/

section Wiring

/-- **Theorem R.7's reference with the outer pockets reduced to their open source steps** (the drop-in for
`HOuter.r7ReferenceStatement_late_sideDet_outer`): `R7OuterRemaining` is replaced by the per-configuration geometric
inputs `R7OuterGeomRemaining`, the side field `R7OuterSideRemaining` and Proposition 5.9's per-candidate laws
(`Fig51CandLawsStatement` at the late wiring's `h44`); `hQ0` is Theorem 1.2's existing binder. -/
theorem r7ReferenceStatement_late_outerIn
    (hRect : ∀ κ, ZhanGT4.A1Core.A1DualCouplingG3RectStatement κ)
    (hRectEight : ∀ κ, ZhanGT4.A1Core.A1DualCouplingEightRectStatement κ)
    (Ref0 : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop)
    (hCover0 : Sec5.Aux61R2.RefClockFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Ref0)
    (hAvoid0 : ∀ κ b J I, Ref0 κ b J I → Sec5.Aux61Win.IsAvoidingRef.{0} κ b J I)
    (hQ0 : Sec5.FrameQ.QScheduleFirstHitStatement.{0})
    (hlaws : Fig51CandLawsStatement
      (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)))
    (hsd : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      R7ExtremalSideDetRemaining.{0} k rL rR (π * chiC (16 / k)) 0)
    (hgeom : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      R7OuterGeomRemaining.{0} k rL rR)
    (hside : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      R7OuterSideRemaining.{0} k rL rR) :
    R7.R7ReferenceStatement.{0} := by
  have hA := late_partAInputs (late_coreG3 hRect) (late_coreEight hRectEight)
  have hFH := Sec5.FrameQ.stagedPrefixFirstHitStatement_of_qScheduleFirstHit hA hQ0
  have h470 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h470 hA
  have h51 := late_prop51QStatement hA Ref0 hCover0 hAvoid0
  have h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{0} θ :=
    fun θ h1 h2 => late_lemma47QHitTStatement hA h1 h2
  exact r7ReferenceStatement_late_sideDet_outer hRect hRectEight Ref0 hCover0 hAvoid0 hsd
    fun k hk4 rL rR hL hR hmax => r7OuterRemaining_of_inputs h411 h51 h470 h47T hA _ hFH hlaws hk4 hL hR hmax
      (hgeom k hk4 rL rR hL hR hmax) (hside k hk4 rL rR hL hR hmax)

/-- **Theorem R.7's reference with both the extremal `hsd` and the outer pockets reduced** (PROVE-HSD's
`Hsd.r7ReferenceStatement_late_hsd` with `hOuter` from this packet): the remaining R.7 inputs are Proposition 5.9's
per-candidate laws, the three parts of the extremal and of the outer two-seed side limits, and the outer pockets'
geometric inputs `R7OuterGeomRemaining`; `hQ0` is Theorem 1.2's existing binder. -/
theorem r7ReferenceStatement_late_hsd_outerIn
    (hRect : ∀ κ, ZhanGT4.A1Core.A1DualCouplingG3RectStatement κ)
    (hRectEight : ∀ κ, ZhanGT4.A1Core.A1DualCouplingEightRectStatement κ)
    (Ref0 : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop)
    (hCover0 : Sec5.Aux61R2.RefClockFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Ref0)
    (hAvoid0 : ∀ κ b J I, Ref0 κ b J I → Sec5.Aux61Win.IsAvoidingRef.{0} κ b J I)
    (hQ0 : Sec5.FrameQ.QScheduleFirstHitStatement.{0})
    (hlaws : Fig51CandLawsStatement
      (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)))
    (hsideExt : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      R7PhaseSideRemaining.{0} k rL rR (π * chiC (16 / k)) 0)
    (hgeom : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      R7OuterGeomRemaining.{0} k rL rR)
    (hsideOut : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      R7OuterPhaseSideRemaining.{0} k rL rR) :
    R7.R7ReferenceStatement.{0} := by
  have hA := late_partAInputs (late_coreG3 hRect) (late_coreEight hRectEight)
  have hFH := Sec5.FrameQ.stagedPrefixFirstHitStatement_of_qScheduleFirstHit hA hQ0
  have h470 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h470 hA
  have h51 := late_prop51QStatement hA Ref0 hCover0 hAvoid0
  have h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{0} θ :=
    fun θ h1 h2 => late_lemma47QHitTStatement hA h1 h2
  have haux7 : ∀ k : ℝ, 4 < k → Sec4.Aux7Statement.{0} k :=
    aux7_of_sixteen_div fun κ hκ hκ4 => Sec5.aux7Statement_sixteen_div_of_partA_of_clearance hA hκ hκ4
  exact r7ReferenceStatement_late_hsd hRect hRectEight Ref0 hCover0 hAvoid0 hQ0 hlaws hsideExt
    fun k hk4 rL rR hL hR hmax => outerPocketCompletion_of_remaining h411 h51 (haux7 k hk4) hk4 hL hR hmax
      (r7OuterRemaining_of_inputs h411 h51 h470 h47T hA _ hFH hlaws hk4 hL hR hmax
        (hgeom k hk4 rL rR hL hR hmax) (r7OuterSideRemaining_of_phase hk4 (hsideOut k hk4 rL rR hL hR hmax)))

end Wiring

end InteractingSLE.Sec7.OuterIn
