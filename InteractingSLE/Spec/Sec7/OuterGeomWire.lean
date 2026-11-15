/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.OuterGeomExtInf
import InteractingSLE.Spec.Sec7.OuterInWire

/-!
# Theorem R.7's outer pockets: `OuterGeomInputs` from the relative drivers and the gap at infinity

Packet PROVE-R7-OUTERGEOM. PROVE-R7-OUTERIN reduced the pocket geometry of R.7's mixed and outer pockets to the
per-configuration residual `OuterIn.OuterGeomInputs`. Every Aux. lemma 37 part of it is proved in this packet:

* `attachLeft`, `attachRight` — Aux. 37 along the contained arm of the bounded mixed pockets (`ae_attachLeft`,
  `ae_attachRight`: the extremal sub-pockets of the contained arm with the certified frontier);
* the attachment conjuncts of `infLeft`, `infRight` — the same at the flow seed (`ae_attachLeftInf`,
  `ae_attachRightInf`);
* the attachment conjuncts of `outerOuter`, `infOuterOuter` — Aux. 37 along the clipped `β_R` (`outerOuterAttach`,
  `outerOuterAttachInf`, pathwise from `NoCommonArc`).

What remains is collected in **`OuterGeomRest`**: Aux. lemma 41's relative driver for the two-outer pockets (bounded
and at the flow seed) and for the mixed pockets at the flow seed, and §5.4's gap equality at the flow seed for the
mixed pockets (`PocketGapEqInf`; the two-outer one is PROVE-R7-OUTERIN's `pocketGapEqInf_outerOuter`).

* **`outerGeomInputs_of_rest`**: `OuterGeomInputs` on every R.7 configuration from `OuterGeomRest`;
* `R7OuterGeomRest`, **`r7OuterGeomRemaining_of_rest`**: `OuterIn.R7OuterGeomRemaining` from it;
* **`r7ReferenceStatement_late_outerGeom`**, **`r7ReferenceStatement_late_hsd_outerGeom`**: the drop-ins for
  `OuterIn.r7ReferenceStatement_late_outerIn` / `…_hsd_outerIn` with `R7OuterGeomRemaining` replaced by
  `R7OuterGeomRest`.

R48: the named statements used are those of the late wiring (A.1's rectangle families, the reference cover,
`QScheduleFirstHitStatement`) and, through them, `h44` (R74), Propositions 4.11/5.1 in chart `Q`, Lemma 4.7Q and Zhan's
Part A, as in PROVE-R7-OUTERIN; nothing uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any
`*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open LQGMetric (DistOn)
open QuantumZipper (H Hbar chiC)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.OuterGeom

open WangWu Lemma71I PocketCoord PocketJordan R7StopIn R7Outer R7Leaves HOuter Hsd OuterIn Wire
open Sec5.Prop55Half (IsSeedProper)

section Rest

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The remaining inputs of the outer pockets' geometry after Aux. lemma 37** (per configuration, versions `R`, `L`
of the arms and `η` of the counterflow's trace), at every positive rational change time, almost surely on the change
configuration:
* `relOuterOuter` — bounded pockets with two outer arms: Aux. lemma 41's relative driver;
* `infLeft`, `infRight` — mixed pockets opening at the flow seed: §5.4's gap equality at infinity and Aux. lemma 41;
* `relInfOuterOuter` — pockets with two outer arms opening at the flow seed: Aux. lemma 41. -/
structure OuterGeomRest (k rL rR : ℝ) (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ) : Prop where
  relOuterOuter : R7.thetaR k rL < -(π / 2) → π / 2 < R7.thetaL k rR → ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
    IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
    OuterRelLoewner (R ω) (L ω) (StripSys.rt q) (η ω)
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

variable {k rL rR : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞} {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}

omit [StandardBorelSpace Ω] in
/-- **Aux. lemma 37 along the clipped `β_R` of the pockets with two outer arms, on every R.7 configuration**
(bounded and at the flow seed; pathwise from the configuration, `outerOuterAttach(Inf)`). -/
theorem ae_outerOuterAttach (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hcfg : IsR7OuterConfig k rL rR (π * chiC (16 / k)) 0 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hV : IsR7Versions P W' αR αL R L η) (hθR : R7.thetaR k rL < -(π / 2)) (hθL : π / 2 < R7.thetaL k rR) :
    ∀ᵐ ω ∂P, ∀ r : ℝ≥0, IsChangeConfigInc (R ω) (L ω) r →
      (0 < rightLo (R ω) (L ω) r → OuterOuterAttach (R ω) (L ω) (βR ω) r (η ω)) ∧
      (rightLo (R ω) (L ω) r = 0 → OuterOuterAttachInf (R ω) (L ω) (βR ω) r (η ω)) := by
  have hpi := Real.pi_pos
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hc : 0 ≤ π * chiC (16 / k) := mul_nonneg hpi.le (Sec4.chiC_pos hκ hκ4).le
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hβRs : ∀ᵐ ω ∂P, IsSimpleProper (βR ω) := hcfg.regular.mono fun ω hω => IsSeedProper.isSimpleProper hω.2.1
  have hwβR := OuterIn.ae_walls_r7 h411 h47 h47T hk4 hc le_rfl hcfg.gff hcfg.counterflow (θ := -(π / 2))
    ⟨le_rfl, by linarith⟩ hcfg.flow_βR hβRs hV.η_cont hV.η_zero hV.η_trace
  filter_upwards [hcfg.ae_outerOuter h55 hk4 hL hR hc le_rfl hθR hθL, hV.R_ae, hV.L_ae, hwβR]
    with ω hω hRe hLe hwR
  rw [← hRe, ← hLe] at hω
  obtain ⟨-, hβR, -, -, -, hO₁, -, hc₁R, hc₁L, -⟩ := hω
  intro r hconf
  exact ⟨fun hpos => outerOuterAttach hconf hpos hβR hO₁ hc₁R hc₁L (hV.η_cont ω) (hV.η_zero ω) hwR.1 hwR.2,
    fun h0 => outerOuterAttachInf hconf h0 hβR hO₁ hc₁R hc₁L (hV.η_cont ω) (hV.η_zero ω) hwR.1 hwR.2⟩

/-- **`OuterIn.OuterGeomInputs` on every R.7 configuration from `OuterGeomRest`**: every Aux. lemma 37 part is proved
(`ae_attachLeft`, `ae_attachRight`, `ae_attachLeftInf`, `ae_attachRightInf`, `ae_outerOuterAttach`). -/
theorem outerGeomInputs_of_rest (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hcfg : IsR7OuterConfig k rL rR (π * chiC (16 / k)) 0 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hV : IsR7Versions P W' αR αL R L η) (hrest : OuterGeomRest k rL rR P R L η) :
    OuterGeomInputs k rL rR P βR βL R L η := by
  refine ⟨fun hθL hθR => ae_attachLeft h44 h411 h51 h47 h47T hk4 hL hR hcfg hV hθL hθR,
    fun hθR hθL => ae_attachRight h44 h411 h51 h47 h47T hk4 hL hR hcfg hV hθR hθL,
    fun hθR hθL q hq => ?_, fun hθL hθR q hq => ?_, fun hθR hθL q hq => ?_, fun hθR hθL q hq => ?_⟩
  · filter_upwards [ae_outerOuterAttach h411 h51 h47 h47T hk4 hL hR hcfg hV hθR hθL,
      hrest.relOuterOuter hθR hθL q hq] with ω hω hloc hconf hpos
    exact ⟨(hω _ hconf).1 hpos, hloc hconf hpos⟩
  · filter_upwards [ae_attachLeftInf h44 h411 h51 h47 h47T hk4 hL hR hcfg hV hθL hθR q hq,
      hrest.infLeft hθL hθR q hq] with ω hAC hrem hconf h0
    exact ⟨hAC hconf h0, hrem hconf h0⟩
  · filter_upwards [ae_attachRightInf h44 h411 h51 h47 h47T hk4 hL hR hcfg hV hθR hθL q hq,
      hrest.infRight hθR hθL q hq] with ω hAC hrem hconf h0
    exact ⟨hAC hconf h0, hrem hconf h0⟩
  · filter_upwards [ae_outerOuterAttach h411 h51 h47 h47T hk4 hL hR hcfg hV hθR hθL,
      hrest.relInfOuterOuter hθR hθL q hq] with ω hω hloc hconf h0
    exact ⟨(hω _ hconf).2 h0, hloc hconf h0⟩

end Inputs

section Remaining

/-- **The remaining outer-pocket geometry on every R.7 configuration** (`OuterGeomRest`; replaces
`OuterIn.R7OuterGeomRemaining`). -/
def R7OuterGeomRest (k rL rR : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR (π * chiC (16 / k)) 0 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η → OuterGeomRest k rL rR P R L η

/-- **`OuterIn.R7OuterGeomRemaining` from `R7OuterGeomRest`.** -/
theorem r7OuterGeomRemaining_of_rest (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    {k rL rR : ℝ} (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR) (hrest : R7OuterGeomRest.{u} k rL rR) :
    R7OuterGeomRemaining.{u} k rL rR := by
  intro Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV
  exact outerGeomInputs_of_rest h44 h411 h51 h47 h47T hk4 hL hR hcfg hV
    (hrest P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV)

end Remaining

section Wiring

/-- **Theorem R.7's reference with the outer pockets' Aux. lemma 37 proved** (the drop-in for
`OuterIn.r7ReferenceStatement_late_outerIn` with `R7OuterGeomRemaining` replaced by `R7OuterGeomRest`). -/
theorem r7ReferenceStatement_late_outerGeom
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
      R7OuterGeomRest.{0} k rL rR)
    (hside : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      R7OuterSideRemaining.{0} k rL rR) :
    R7.R7ReferenceStatement.{0} := by
  have hA := late_partAInputs (late_coreG3 hRect) (late_coreEight hRectEight)
  have h470 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h470 hA
  have h51 := late_prop51QStatement hA Ref0 hCover0 hAvoid0
  have h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{0} θ :=
    fun θ h1 h2 => late_lemma47QHitTStatement hA h1 h2
  exact r7ReferenceStatement_late_outerIn hRect hRectEight Ref0 hCover0 hAvoid0 hQ0 hlaws hsd
    (fun k hk4 rL rR hL hR hmax => r7OuterGeomRemaining_of_rest
      (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)) h411 h51 h470 h47T hk4
      hL hR (hrest k hk4 rL rR hL hR hmax)) hside

/-- **Theorem R.7's reference with the extremal `hsd` reduced and the outer pockets' Aux. lemma 37 proved** (the
drop-in for `OuterIn.r7ReferenceStatement_late_hsd_outerIn` with `R7OuterGeomRemaining` replaced by
`R7OuterGeomRest`). -/
theorem r7ReferenceStatement_late_hsd_outerGeom
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
      R7OuterGeomRest.{0} k rL rR)
    (hsideOut : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      R7OuterPhaseSideRemaining.{0} k rL rR) :
    R7.R7ReferenceStatement.{0} := by
  have hA := late_partAInputs (late_coreG3 hRect) (late_coreEight hRectEight)
  have h470 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h470 hA
  have h51 := late_prop51QStatement hA Ref0 hCover0 hAvoid0
  have h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{0} θ :=
    fun θ h1 h2 => late_lemma47QHitTStatement hA h1 h2
  exact r7ReferenceStatement_late_hsd_outerIn hRect hRectEight Ref0 hCover0 hAvoid0 hQ0 hlaws hsideExt
    (fun k hk4 rL rR hL hR hmax => r7OuterGeomRemaining_of_rest
      (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)) h411 h51 h470 h47T hk4
      hL hR (hrest k hk4 rL rR hL hR hmax)) hsideOut

end Wiring

end InteractingSLE.Sec7.OuterGeom
