/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux41OOWireInf
import InteractingSLE.Spec.Sec7.R7RelativeInfLeft
import InteractingSLE.Spec.Sec7.R7RelativeInfRight

/-!
# Theorem R.7's outer pockets: `OuterGeomRest` discharged on every R.7 configuration

Packet PROVE-R7-AUX41OO (wiring only, no new mathematics). After this packet's two-outer fields (`Aux41OOWire`,
`Aux41OOWireInf`) the remaining outer-pocket geometry is `OuterGeomRestMixedInf`: the mixed pockets opening at the flow
seed (§5.4's gap equality at infinity and Aux. lemma 41). Both are now available from landed or just-finished results:

* PROVE-R7-GAPEQ proved them pathwise from the contained attachment comparison `BarrierAttachConstInf` along the
  contained arm (`R7InfinityGap.isErasurePocketInf_{left,right}Outer_of_containedAttach`, whose `gap` field is
  `PocketGapEqInf`, and `R7RelativeInf.relLoewner_{left,right}Outer_of_containedAttach`);
* PROVE-R7-OUTERGEOM proved exactly that comparison almost surely on every R.7 configuration
  (`OuterGeom.ae_attachLeftInf`, `OuterGeom.ae_attachRightInf`, through the extremal sub-pockets of the contained arm).

So `OuterGeomRestMixedInf` holds on every configuration (`outerGeomRestMixedInf_of_config`), and
`HOuter.R7OuterRemaining` needs no outer-geometry input at all (`r7OuterRemaining_of_side`). The drop-ins
**`r7ReferenceStatement_late_outerDone`** / **`r7ReferenceStatement_late_hsd_outerDone`** replace
`OuterGeom.r7ReferenceStatement_late_outerGeom` / `…_hsd_outerGeom` with the binder `hrest` removed.

R48: as in `Aux41OOWire`; the additional named statement is `h44` (`AdmCode.Theorem12ParamCond44Statement`, R74, the
late wiring's own instance), used by `OuterGeom.ae_attach{Left,Right}Inf` exactly as in PROVE-R7-OUTERGEOM.
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

section Path

variable {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **A mixed pocket with an outer left arm opening at the flow seed** (pathwise): §5.4's gap equality at infinity and
Aux. lemma 41, from the contained attachment comparison (PROVE-R7-GAPEQ's results). -/
theorem mixedInf_leftOuter (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M) (Lemma71I.realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L) (houter : range L ⊆ leftSideOf (range M) ∪ range M)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hrevR : IsWallReverseVisit R η) (hvisR : IsWallVisited R η) (hrevM : IsWallReverseVisit M η)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ leftSideOf (range M))
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤)
    (hAC : BarrierAttachConstInf η (cfPocket R L r) (cfArcRInf R L r) (firstHit η (cfArcRInf R L r 0))) :
    PocketGapEqInf η (cfPocket R L r) (firstHit η (cfArcRInf R L r 0)) ∧ OuterRelLoewnerInf R L r η := by
  have hP := R7InfinityGap.isErasurePocketInf_leftOuter_of_containedAttach h h0 hM hO hcR hcL houter hη hW hW0
    hrevR hvisR hrevM havoid h42 hAC
  refine ⟨hP.gap, fun ψ hψ => ?_⟩
  have hψ' : Sec6.IsJordanCoordInf (cfPocket R L r) (cfArcRInf R L r 0) ψ := by
    rw [IsChangeConfigInc.cfArcRInf_zero]
    exact hψ
  exact R7RelativeInf.relLoewner_leftOuter_of_containedAttach h h0 hM hO hcR hcL houter hη hW hW0 hrevR hrevM
    havoid h42 hvisR hAC hψ'

/-- **A mixed pocket with an outer right arm opening at the flow seed** (pathwise), as `mixedInf_leftOuter`. -/
theorem mixedInf_rightOuter (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M) (Lemma71I.realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L) (houter : range R ⊆ rightSideOf (range M) ∪ range M)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hrevL : IsWallReverseVisit L η) (hvisL : IsWallVisited L η) (hrevM : IsWallReverseVisit M η)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M))
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤)
    (hAC : BarrierAttachConstInf η (cfPocket R L r) (cfArcLInf R L r) (firstHit η (cfArcRInf R L r 0))) :
    PocketGapEqInf η (cfPocket R L r) (firstHit η (cfArcRInf R L r 0)) ∧ OuterRelLoewnerInf R L r η := by
  have hP := R7InfinityGap.isErasurePocketInf_rightOuter_of_containedAttach h h0 hM hO hcR hcL houter hη hW hW0
    hrevL hvisL hrevM havoid h42 hAC
  refine ⟨hP.gap, fun ψ hψ => ?_⟩
  have hψ' : Sec6.IsJordanCoordInf (cfPocket R L r) (cfArcRInf R L r 0) ψ := by
    rw [IsChangeConfigInc.cfArcRInf_zero]
    exact hψ
  exact R7RelativeInf.relLoewner_rightOuter_of_containedAttach h h0 hM hO hcR hcL houter hη hW hW0 hrevL hrevM
    havoid h42 hvisL hAC hψ'

end Path

section Ae

variable {k rL rR : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}
  {b' : ℝ → ℝ} {J' : Finset ℝ} {h' h'' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
  {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}

/-- **The field `infLeft` of `OuterGeomRest` on an R.7 configuration**. -/
theorem ae_mixedInfLeft (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hcfg : IsR7OuterConfig k rL rR (π * chiC (16 / k)) 0 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B) (hV : IsR7Versions P W' αR αL R L η)
    (hθL : π / 2 < R7.thetaL k rR) (hθR : ¬ R7.thetaR k rL < -(π / 2)) (q : ℚ) (hq : 0 < q) :
    ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
      PocketGapEqInf (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
          (firstHit (η ω) (cfArcRInf (R ω) (L ω) (StripSys.rt q) 0)) ∧
        OuterRelLoewnerInf (R ω) (L ω) (StripSys.rt q) (η ω) := by
  have hpi := Real.pi_pos
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hc : 0 ≤ π * chiC (16 / k) := mul_nonneg hpi.le (Sec4.chiC_pos hκ hκ4).le
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hreg := hcfg.regular
  have hβLs : ∀ᵐ ω ∂P, IsSimpleProper (βL ω) := hreg.mono fun ω hω => IsSeedProper.isSimpleProper hω.2.2.1
  have htrace := ae_isLoewnerTrace_counterflow_r7 hk4 hc le_rfl hcfg.gff hcfg.counterflow hV.η_trace
  have h42 := ae_noSimpleArc_counterflow_r7 hk4 hc le_rfl hcfg.gff hcfg.counterflow hD hV.η_trace
  have hav := ae_avoid_counterflow_r7 hk4 hc le_rfl hcfg hV.η_trace
  have hwβL := ae_walls_r7 h411 h47 h47T hk4 hc le_rfl hcfg.gff hcfg.counterflow (θ := π / 2)
    ⟨by linarith, le_rfl⟩ hcfg.flow_βL hβLs hV.η_cont hV.η_zero hV.η_trace
  have hθRm : R7.thetaR k rL ∈ Icc (-(π / 2)) (π / 2) :=
    ⟨not_lt.1 hθR, (R7.thetaR_lt_pi_div_two hk4 hL).le⟩
  have hRs : ∀ᵐ ω ∂P, IsSimpleProper (R ω) := by
    filter_upwards [hreg, hV.R_ae] with ω hω he
    rw [he]; exact IsSeedProper.isSimpleProper hω.1
  have hflR := IsFlowLine.congr_path (η' := R) hcfg.flow_αR (hV.R_ae.mono fun ω hω t _ => by rw [hω])
  have hwR := ae_walls_r7 h411 h47 h47T hk4 hc le_rfl hcfg.gff hcfg.counterflow hθRm hflR hRs hV.η_cont
    hV.η_zero hV.η_trace
  filter_upwards [hcfg.ae_leftOuter h55 hk4 hL hR hc le_rfl hθL, hV.R_ae, hV.L_ae, htrace, h42, hav, hwβL,
    hwR, ae_attachLeftInf h44 h411 h51 h47 h47T hk4 hL hR hcfg hV hθL hθR q hq]
    with ω hω hRe hLe htr h42ω havω hwM hwRω hACω hconf h0
  rw [← hRe, ← hLe] at hω
  obtain ⟨-, hM, -, -, hO, hcR, hcL, ho, -⟩ := hω
  exact mixedInf_leftOuter hconf h0 hM hO hcR hcL ho htr.1 htr.2.1
    (by simpa only [Real.toNNReal_zero] using htr.2.2) hwRω.1 hwRω.2 hwM.1
    (fun t ht hm => havω t ht (Or.inr hm)) h42ω (hACω hconf h0)

/-- **The field `infRight` of `OuterGeomRest` on an R.7 configuration**. -/
theorem ae_mixedInfRight (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hcfg : IsR7OuterConfig k rL rR (π * chiC (16 / k)) 0 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B) (hV : IsR7Versions P W' αR αL R L η)
    (hθR : R7.thetaR k rL < -(π / 2)) (hθL : ¬ π / 2 < R7.thetaL k rR) (q : ℚ) (hq : 0 < q) :
    ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
      PocketGapEqInf (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
          (firstHit (η ω) (cfArcRInf (R ω) (L ω) (StripSys.rt q) 0)) ∧
        OuterRelLoewnerInf (R ω) (L ω) (StripSys.rt q) (η ω) := by
  have hpi := Real.pi_pos
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hc : 0 ≤ π * chiC (16 / k) := mul_nonneg hpi.le (Sec4.chiC_pos hκ hκ4).le
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hreg := hcfg.regular
  have hβRs : ∀ᵐ ω ∂P, IsSimpleProper (βR ω) := hreg.mono fun ω hω => IsSeedProper.isSimpleProper hω.2.1
  have htrace := ae_isLoewnerTrace_counterflow_r7 hk4 hc le_rfl hcfg.gff hcfg.counterflow hV.η_trace
  have h42 := ae_noSimpleArc_counterflow_r7 hk4 hc le_rfl hcfg.gff hcfg.counterflow hD hV.η_trace
  have hav := ae_avoid_counterflow_r7 hk4 hc le_rfl hcfg hV.η_trace
  have hwβR := ae_walls_r7 h411 h47 h47T hk4 hc le_rfl hcfg.gff hcfg.counterflow (θ := -(π / 2))
    ⟨le_rfl, by linarith⟩ hcfg.flow_βR hβRs hV.η_cont hV.η_zero hV.η_trace
  have hθLm : R7.thetaL k rR ∈ Icc (-(π / 2)) (π / 2) :=
    ⟨(R7.neg_pi_div_two_lt_thetaL hk4 hR).le, not_lt.1 hθL⟩
  have hLs : ∀ᵐ ω ∂P, IsSimpleProper (L ω) := by
    filter_upwards [hreg, hV.L_ae] with ω hω he
    rw [he]; exact IsSeedProper.isSimpleProper hω.2.2.2.1
  have hflL := IsFlowLine.congr_path (η' := L) hcfg.flow_αL (hV.L_ae.mono fun ω hω t _ => by rw [hω])
  have hwL := ae_walls_r7 h411 h47 h47T hk4 hc le_rfl hcfg.gff hcfg.counterflow hθLm hflL hLs hV.η_cont
    hV.η_zero hV.η_trace
  filter_upwards [hcfg.ae_rightOuter h55 hk4 hL hR hc le_rfl hθR, hV.R_ae, hV.L_ae, htrace, h42, hav, hwβR,
    hwL, ae_attachRightInf h44 h411 h51 h47 h47T hk4 hL hR hcfg hV hθR hθL q hq]
    with ω hω hRe hLe htr h42ω havω hwM hwLω hACω hconf h0
  rw [← hRe, ← hLe] at hω
  obtain ⟨-, hM, -, -, hO, hcR, hcL, ho, -⟩ := hω
  exact mixedInf_rightOuter hconf h0 hM hO hcR hcL ho htr.1 htr.2.1
    (by simpa only [Real.toNNReal_zero] using htr.2.2) hwLω.1 hwLω.2 hwM.1
    (fun t ht hm => havω t ht (Or.inl hm)) h42ω (hACω hconf h0)

/-- **`OuterGeomRestMixedInf` holds on every R.7 configuration** (with its counterflow decomposition). -/
theorem outerGeomRestMixedInf_of_config (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hcfg : IsR7OuterConfig k rL rR (π * chiC (16 / k)) 0 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B) (hV : IsR7Versions P W' αR αL R L η) :
    OuterGeomRestMixedInf k rL rR P R L η :=
  ⟨fun hθL hθR q hq => ae_mixedInfLeft h44 h411 h51 h47 h47T hk4 hL hR hcfg hD hV hθL hθR q hq,
    fun hθR hθL q hq => ae_mixedInfRight h44 h411 h51 h47 h47T hk4 hL hR hcfg hD hV hθR hθL q hq⟩

end Ae

section Remaining

/-- **`HOuter.R7OuterRemaining` from the side limits alone** (the outer pockets' geometry is proved on every
configuration: `outerGeomRestMixedInf_of_config`, `outerGeomRestOO_of_mixedInf`, `outerGeomRest_of_restOO`,
`OuterGeom.outerGeomInputs_of_rest`). -/
theorem r7OuterRemaining_of_side (h411 : Sec5.Cond44Ref.Prop411QStatement.{0})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{0}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{0} θ)
    (hA : Sec5.PartAInputsSixteenDivOfClearance) (h44 : AdmCode.Theorem12ParamCond44Statement.{0})
    (hFH : Sec5.StripRevVisit.StagedPrefixFirstHitStatement.{0}) (hlaws : Fig51CandLawsStatement h44)
    {k rL rR : ℝ} (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR) (hmax : k / 2 - 4 < max rL rR)
    (hside : R7OuterSideRemaining.{0} k rL rR) :
    R7OuterRemaining.{0} k rL rR := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hc : 0 ≤ π * chiC (16 / k) := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hin : OuterGeomInputs k rL rR P βR βL R L η :=
    outerGeomInputs_of_rest h44 h411 h51 h47 h47T hk4 hL hR hcfg hV
      (outerGeomRest_of_restOO h411 h51 h47 h47T hA hk4 hL hR hcfg hD hV
        (outerGeomRestOO_of_mixedInf h411 h51 h47 h47T hk4 hL hR hcfg hD hV
          (outerGeomRestMixedInf_of_config h44 h411 h51 h47 h47T hk4 hL hR hcfg hD hV)))
  exact ⟨fun q hq => ae_outerGeom h411 h51 h47 h47T hA hk4 hL hR hmax hc le_rfl hcfg hD hV hin q hq,
    fun q hq => ae_outerGeomInf h411 h51 h47 h47T hk4 hL hR hmax hc le_rfl hcfg hD hV hin q hq,
    hside P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV,
    r7_det h44 hA hFH hlaws hk4 hc le_rfl hcfg.gff hcfg.counterflow hD hV.η_trace⟩

end Remaining

section Wiring

/-- **Theorem R.7's reference with the outer pockets' geometry proved** (the drop-in for
`OuterGeom.r7ReferenceStatement_late_outerGeom` without its binder `hrest`). -/
theorem r7ReferenceStatement_late_outerDone
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
    fun k hk4 rL rR hL hR hmax => r7OuterRemaining_of_side h411 h51 h470 h47T hA _ hFH hlaws hk4 hL hR hmax
      (hside k hk4 rL rR hL hR hmax)

/-- **Theorem R.7's reference with the extremal `hsd` reduced and the outer pockets' geometry proved** (the drop-in for
`OuterGeom.r7ReferenceStatement_late_hsd_outerGeom` without its binder `hrest`). -/
theorem r7ReferenceStatement_late_hsd_outerDone
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
      (r7OuterRemaining_of_side h411 h51 h470 h47T hA _ hFH hlaws hk4 hL hR hmax
        (r7OuterSideRemaining_of_phase hk4 (hsideOut k hk4 rL rR hL hR hmax)))

end Wiring

end InteractingSLE.Sec7.Aux41OO
