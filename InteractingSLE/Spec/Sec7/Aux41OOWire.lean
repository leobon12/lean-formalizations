/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux41OOLoewner
import InteractingSLE.Spec.Sec7.OuterGeomWire

/-!
# Theorem R.7's two-outer bounded pockets: the field `relOuterOuter` of `OuterGeomRest`, and the drop-ins

Packet PROVE-R7-AUX41OO. `OuterGeom.OuterGeomRest` (PROVE-R7-OUTERGEOM) collected the outer pockets' remaining
geometry. Its field `relOuterOuter` (Aux. lemma 41 for the bounded pockets with two outer arms) is proved here almost
surely on every R.7 configuration (`ae_outerRelLoewner`, from the pathwise `outerRelLoewner_outerOuter`). The proof uses
Aux. 42 and the counterflow's interior trace, which need the counterflow decomposition `IsCfDecomp` (as OUTERIN's
`ae_outerGeom`); `R7OuterGeomRest` does not quantify over it, so the drop-ins go one level up, to
`HOuter.R7OuterRemaining`, where it is available:

* `OuterGeomRestOO` — what remains of `OuterGeomRest` (the flow-seed fields `infLeft`, `infRight`, `relInfOuterOuter`);
* **`outerGeomRest_of_restOO`**: `OuterGeomRest` on a configuration from `OuterGeomRestOO` and `IsCfDecomp`;
* `R7OuterGeomRestOO`, **`r7OuterRemaining_of_restOO`**: `HOuter.R7OuterRemaining` from it (the analogue of
  `OuterIn.r7OuterRemaining_of_inputs`);
* **`r7ReferenceStatement_late_restOO`**, **`r7ReferenceStatement_late_hsd_restOO`**: the drop-ins for
  `OuterGeom.r7ReferenceStatement_late_outerGeom` / `…_hsd_outerGeom` with `R7OuterGeomRest` replaced by
  `R7OuterGeomRestOO`.

R48: the named statements used are those of the late wiring and, through them, `h44` (R74), Propositions 4.11/5.1 in
chart `Q`, Lemma 4.7Q and Zhan's Part A, as in PROVE-R7-OUTERIN / PROVE-R7-OUTERGEOM; nothing uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open LQGMetric (DistOn)
open QuantumZipper (H Hbar chiC)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.Aux41OO

open WangWu Lemma71I PocketCoord PocketJordan R7StopIn HOuter R7Outer R7Leaves OuterIn OuterGeom
open WholeField RefWire Hsd Wire StripSafe
open Sec5.Prop55Half (IsSeedProper)

section Ae

variable {k rL rR c c' : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}
  {b' : ℝ → ℝ} {J' : Finset ℝ} {h' h'' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
  {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}

/-- **Aux. lemma 41 for the bounded pockets with two outer arms, on an R.7 configuration**: at every positive rational
change time, almost surely on the bounded change configuration, `OuterRelLoewner` holds (every pathwise input of
`outerRelLoewner_outerOuter` is supplied by the configuration, as in OUTERIN's `ae_outerGeom`). -/
theorem ae_outerRelLoewner (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hA : Sec5.PartAInputsSixteenDivOfClearance) (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B) (hV : IsR7Versions P W' αR αL R L η)
    (hθR : R7.thetaR k rL < -(π / 2)) (hθL : π / 2 < R7.thetaL k rR) (q : ℚ) :
    ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
      OuterRelLoewner (R ω) (L ω) (StripSys.rt q) (η ω) := by
  have hpi := Real.pi_pos
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hreg := hcfg.regular
  have hβRs : ∀ᵐ ω ∂P, IsSimpleProper (βR ω) := hreg.mono fun ω hω => IsSeedProper.isSimpleProper hω.2.1
  have hβLs : ∀ᵐ ω ∂P, IsSimpleProper (βL ω) := hreg.mono fun ω hω => IsSeedProper.isSimpleProper hω.2.2.1
  have htrace := ae_isLoewnerTrace_counterflow_r7 hk4 hc hc' hcfg.gff hcfg.counterflow hV.η_trace
  have hH := ae_counterflow_mem_H_r7 hA hk4 hc hc' hcfg.gff hcfg.counterflow hD hV.η_trace
  have h42 := ae_noSimpleArc_counterflow_r7 hk4 hc hc' hcfg.gff hcfg.counterflow hD hV.η_trace
  have hav := ae_avoid_counterflow_r7 hk4 hc hc' hcfg hV.η_trace
  have hwβR := ae_walls_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow (θ := -(π / 2))
    ⟨le_rfl, by linarith⟩ hcfg.flow_βR hβRs hV.η_cont hV.η_zero hV.η_trace
  have hwβL := ae_walls_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow (θ := π / 2)
    ⟨by linarith, le_rfl⟩ hcfg.flow_βL hβLs hV.η_cont hV.η_zero hV.η_trace
  filter_upwards [hcfg.ae_outerOuter h55 hk4 hL hR hc hc' hθR hθL, hV.R_ae, hV.L_ae, htrace, hH, h42, hav,
    hwβR, hwβL] with ω hω hRe hLe htr hHω h42ω havω hwR hwL hconf hpos
  rw [← hRe, ← hLe] at hω
  obtain ⟨-, hβR, hβL, -, -, hO₁, hO₂, hc₁R, hc₁L, hc₂R, hc₂L, hoR, hoL, -⟩ := hω
  exact outerRelLoewner_outerOuter hconf hpos hβR hβL hO₁ hO₂ hc₁R hc₁L hc₂R hc₂L hoR hoL htr.1 htr.2.1
    (by simpa only [Real.toNNReal_zero] using htr.2.2) hHω havω hwR.1 hwL.1 hwR.2 h42ω

end Ae

section Rest

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **What remains of `OuterGeom.OuterGeomRest` after this packet** (per configuration, versions `R`, `L` of the arms
and `η` of the counterflow's trace), at every positive rational change time, almost surely on the change configuration
opening at the flow seed:
* `infLeft`, `infRight` — mixed pockets: §5.4's gap equality at infinity and Aux. lemma 41 (PROVE-R7-GAPEQ);
* `relInfOuterOuter` — pockets with two outer arms: Aux. lemma 41 at infinity.
The bounded two-outer field `relOuterOuter` is proved (`ae_outerRelLoewner`). -/
structure OuterGeomRestOO (k rL rR : ℝ) (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ) : Prop where
  infLeft : π / 2 < R7.thetaL k rR → ¬ R7.thetaR k rL < -(π / 2) → ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
    IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
    PocketGapEqInf (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
        (firstHit (η ω) (cfArcRInf (R ω) (L ω) (StripSys.rt q) 0)) ∧
      OuterRelLoewnerInf (R ω) (L ω) (StripSys.rt q) (η ω)
  infRight : R7.thetaR k rL < -(π / 2) → ¬ π / 2 < R7.thetaL k rR → ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
    IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
    PocketGapEqInf (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
        (firstHit (η ω) (cfArcRInf (R ω) (L ω) (StripSys.rt q) 0)) ∧
      OuterRelLoewnerInf (R ω) (L ω) (StripSys.rt q) (η ω)
  relInfOuterOuter : R7.thetaR k rL < -(π / 2) → π / 2 < R7.thetaL k rR → ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
    IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
    OuterRelLoewnerInf (R ω) (L ω) (StripSys.rt q) (η ω)

end Rest

section Inputs

variable {k rL rR : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}
  {b' : ℝ → ℝ} {J' : Finset ℝ} {h' h'' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
  {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}

/-- **`OuterGeom.OuterGeomRest` on an R.7 configuration from `OuterGeomRestOO`** and the counterflow decomposition:
the field `relOuterOuter` is `ae_outerRelLoewner`. -/
theorem outerGeomRest_of_restOO (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hA : Sec5.PartAInputsSixteenDivOfClearance) (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hcfg : IsR7OuterConfig k rL rR (π * chiC (16 / k)) 0 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B) (hV : IsR7Versions P W' αR αL R L η)
    (hrest : OuterGeomRestOO k rL rR P R L η) : OuterGeomRest k rL rR P R L η := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hc : 0 ≤ π * chiC (16 / k) := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  exact ⟨fun hθR hθL q _ => ae_outerRelLoewner h411 h51 h47 h47T hA hk4 hL hR hc le_rfl hcfg hD hV hθR hθL q,
    hrest.infLeft, hrest.infRight, hrest.relInfOuterOuter⟩

end Inputs

section Remaining

/-- **The remaining outer-pocket geometry on every R.7 configuration** (`OuterGeomRestOO`; replaces
`OuterGeom.R7OuterGeomRest`). -/
def R7OuterGeomRestOO (k rL rR : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR (π * chiC (16 / k)) 0 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η → OuterGeomRestOO k rL rR P R L η

/-- **`HOuter.R7OuterRemaining` from `R7OuterGeomRestOO`** (the analogue of `OuterIn.r7OuterRemaining_of_inputs`):
`geom`, `geomInf` from `OuterGeomInputs`, built by `OuterGeom.outerGeomInputs_of_rest` and `outerGeomRest_of_restOO`
with the configuration's counterflow decomposition; `side` from `R7OuterSideRemaining`; `det` from Proposition 5.9's
per-candidate laws (`Hsd.r7_det`). -/
theorem r7OuterRemaining_of_restOO (h411 : Sec5.Cond44Ref.Prop411QStatement.{0})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{0}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{0} θ)
    (hA : Sec5.PartAInputsSixteenDivOfClearance) (h44 : AdmCode.Theorem12ParamCond44Statement.{0})
    (hFH : Sec5.StripRevVisit.StagedPrefixFirstHitStatement.{0}) (hlaws : Fig51CandLawsStatement h44)
    {k rL rR : ℝ} (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR) (hmax : k / 2 - 4 < max rL rR)
    (hrest : R7OuterGeomRestOO.{0} k rL rR) (hside : R7OuterSideRemaining.{0} k rL rR) :
    R7OuterRemaining.{0} k rL rR := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hc : 0 ≤ π * chiC (16 / k) := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hin : OuterGeomInputs k rL rR P βR βL R L η :=
    outerGeomInputs_of_rest h44 h411 h51 h47 h47T hk4 hL hR hcfg hV
      (outerGeomRest_of_restOO h411 h51 h47 h47T hA hk4 hL hR hcfg hD hV
        (hrest P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV))
  exact ⟨fun q hq => ae_outerGeom h411 h51 h47 h47T hA hk4 hL hR hmax hc le_rfl hcfg hD hV hin q hq,
    fun q hq => ae_outerGeomInf h411 h51 h47 h47T hk4 hL hR hmax hc le_rfl hcfg hD hV hin q hq,
    hside P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV,
    r7_det h44 hA hFH hlaws hk4 hc le_rfl hcfg.gff hcfg.counterflow hD hV.η_trace⟩

end Remaining

section Wiring

/-- **Theorem R.7's reference with the bounded two-outer pockets' Aux. lemma 41 proved** (the drop-in for
`OuterGeom.r7ReferenceStatement_late_outerGeom` with `R7OuterGeomRest` replaced by `R7OuterGeomRestOO`). -/
theorem r7ReferenceStatement_late_restOO
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
    (hrest : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      R7OuterGeomRestOO.{0} k rL rR)
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
    fun k hk4 rL rR hL hR hmax => r7OuterRemaining_of_restOO h411 h51 h470 h47T hA _ hFH hlaws hk4 hL hR hmax
      (hrest k hk4 rL rR hL hR hmax) (hside k hk4 rL rR hL hR hmax)

/-- **Theorem R.7's reference with the extremal `hsd` reduced and the bounded two-outer pockets' Aux. lemma 41
proved** (the drop-in for `OuterGeom.r7ReferenceStatement_late_hsd_outerGeom` with `R7OuterGeomRest` replaced by
`R7OuterGeomRestOO`). -/
theorem r7ReferenceStatement_late_hsd_restOO
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
    (hrest : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      R7OuterGeomRestOO.{0} k rL rR)
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
      (r7OuterRemaining_of_restOO h411 h51 h470 h47T hA _ hFH hlaws hk4 hL hR hmax
        (hrest k hk4 rL rR hL hR hmax) (r7OuterSideRemaining_of_phase hk4 (hsideOut k hk4 rL rR hL hR hmax)))

end Wiring

end InteractingSLE.Sec7.Aux41OO
