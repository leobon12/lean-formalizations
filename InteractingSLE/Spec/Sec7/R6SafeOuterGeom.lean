/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6SafeTwoCfg
import InteractingSLE.Spec.Sec7.Aux41OOMixedInf

/-!
# The outer pockets' geometry at arbitrary margins: `OuterGeomAeMRemaining` proved

PROVE-R6-SAFE. R.6's two-outer-arm case needs the outer pocket geometry (`HOuter.OuterGeom(Inf)` almost surely,
the `geom`/`geomInf` fields of `HOuter.R7OuterInputs`) for the intermediate mixed pocket `V`, an R.7 configuration
with enlarged margins. The landed chain (`OuterGeom.outerGeomInputs_of_rest` ← `Aux41OO.outerGeomRest_of_restOO` ←
`Aux41OO.outerGeomRestOO_of_mixedInf` ← `Aux41OO.outerGeomRestMixedInf_of_config`, with `OuterGeom.ae_attach*`,
`Aux41OO.ae_mixedInf*`, `OuterGeom.ae_outerOuterAttach`) is stated at the margins `(πχ(16/k), 0)` only; its proofs use
the margins only through margin-general lemmas, the constant-angle strip system and the strip heights. This file ports
those eleven theorems to margins `c ≥ πχ(16/k)`, `c' ≥ 0` (suffix `M`; the constant-angle strip system from
`StripSafe.exists_isConstStripSystem` with `R6Fin.r7_strip_heights_ge`) and proves

* **`outerGeomAeMRemaining_of_inputs`**: `OuterGeomAeMRemaining k r_L r_R c c'` on the outer range from the landed named
  inputs of the R.7 wiring (Props. 4.11Q/5.1Q, Lemma 4.7Q, `h44` (R74), Zhan's Part A).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open LQGMetric (DistOn)
open QuantumZipper (H Hbar chiC)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.R6Safe

open WangWu Lemma71I PocketCoord PocketJordan R7StopIn HOuter R7Outer R7Leaves OuterIn OuterGeom Aux41OO
open WholeField RefWire Hsd Wire StripSafe R6Fin
open Sec5.Prop55Half (IsSeedProper)

section Port0

variable {k rL rR : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞} {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}

/-- **Margin-general port of `OuterGeomExt.ae_attachLeft`**:
the same proof with the margins `(πχ(16/k), 0)` replaced by `(c, c')`, `c ≥ πχ(16/k)`, `c' ≥ 0`
(constant-angle strip system from `StripSafe.exists_isConstStripSystem`). -/
theorem ae_attachLeftM (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    {c c' : ℝ} (hcπ : π * chiC (16 / k) ≤ c) (hc' : 0 ≤ c')
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hV : IsR7Versions P W' αR αL R L η) (hθL : π / 2 < R7.thetaL k rR) (hθR : ¬ R7.thetaR k rL < -(π / 2)) :
    ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
      IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
      BarrierAttachConst (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q)) (cfArcR (R ω) (L ω) (StripSys.rt q))
        (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 1))
        (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 0)) := by
  intro q _
  have hpi := Real.pi_pos
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hχ := Sec4.chiC_pos hκ hκ4
  have hc : 0 ≤ c := nonneg_of_pi_chi_le hk4 hcπ
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hc2 : 0 ≤ c + (R7.thetaL k rR - π / 2) * chiC (16 / k) :=
    add_nonneg hc (mul_nonneg (by linarith) hχ.le)
  have hcfg' := isR7OuterConfig_leftExt h55 hk4 hL hc hc' hθL hcfg
  have hA := r7A_eq_d hk4 hθL c
  obtain ⟨hcumL, hcumR⟩ := r7_strip_heights_ge (rL := rL) (rR := rR) hk4 hcπ hc'
  obtain ⟨Es, hS, hreg⟩ := StripSafe.exists_isConstStripSystem h44 hκ hκ4
    (isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')) hcumL hcumR hcfg.gff hcfg.counterflow
    ((ae_counterflow_trace_r7 hk4 hc hc' hcfg.gff hcfg.counterflow).mono fun ω hω => hω.1)
  rw [← hA] at hS hcumL hcumR
  obtain ⟨-, M, hMc, hM0, hMm, hMae⟩ := exists_frontierVersion hcfg
  have hV' : IsR7Versions P W' αR βL R M η :=
    ⟨hV.R_cont, hV.R_zero, hV.R_meas, hV.R_ae, hMc, hM0, hMm, hMae, hV.η_cont, hV.η_zero, hV.η_meas, hV.η_trace⟩
  have hRs : ∀ᵐ ω ∂P, IsSimpleProper (R ω) := by
    filter_upwards [hcfg.regular, hV.R_ae] with ω hω he
    rw [he]; exact IsSeedProper.isSimpleProper hω.1
  have hMs : ∀ᵐ ω ∂P, IsSimpleProper (M ω) := by
    filter_upwards [hcfg.regular, hMae] with ω hω he
    rw [he]; exact IsSeedProper.isSimpleProper hω.2.2.1
  have hθRm : R7.thetaR k rL ∈ Icc (-(π / 2)) (π / 2) :=
    ⟨not_lt.1 hθR, (R7.thetaR_lt_pi_div_two hk4 hL).le⟩
  have hflR := IsFlowLine.congr_path (η' := R) hcfg.flow_αR (hV.R_ae.mono fun ω hω t _ => by rw [hω])
  have hflM := IsFlowLine.congr_path (η' := M) hcfg.flow_βL (hMae.mono fun ω hω t _ => by rw [hω])
  have hfirstR := firstHit_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow hθRm hflR hRs hV.η_zero
    hV.η_trace
  have hfirstM := firstHit_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow (θ := π / 2)
    ⟨by linarith, le_rfl⟩ hflM hMs hV.η_zero hV.η_trace
  have hd : -2 < k / 2 - 4 := by linarith
  have hmax : max rL (k / 2 - 4) = k / 2 - 4 := max_eq_right (not_lt.1 (mt (R7.d_lt_rL_iff hk4).1 hθR))
  have hext := StripSafe.r7Attach_of_constStrip h44 hk4 hL hd hmax hc2 hc' hcfg' hS hreg hcumL hcumR hV'
    hfirstR hfirstM
  have hsubAE : ∀ᵐ ω ∂P, ∀ q' : ℚ, 0 < q' → IsChangeConfigInc (R ω) (M ω) (StripSys.rt q') →
      0 < rightLo (R ω) (M ω) (StripSys.rt q') →
      Sec6.AttachmentConstancy (η ω) (cfPocket (R ω) (M ω) (StripSys.rt q')) (cfArcR (R ω) (M ω) (StripSys.rt q'))
        (cfArcL (R ω) (M ω) (StripSys.rt q')) (firstHit (η ω) (cfArcR (R ω) (M ω) (StripSys.rt q') 1))
        (firstHit (η ω) (cfArcR (R ω) (M ω) (StripSys.rt q') 0)) := by
    rw [ae_all_iff]
    intro q'
    by_cases hq' : 0 < q'
    · filter_upwards [hext.1 q' hq'] with ω hω _ using hω
    · exact ae_of_all _ fun ω h' => absurd h' hq'
  obtain ⟨ΦαR, _ΦβR, ΦβL, _ΦαL, hmαR, _, hmβL, _, he⟩ := hcfg.borel
  have hp := ae_pair_r7 h55 hk4 hc hc' (R7.thetaR_lt_pi_div_two hk4 hL) (thetaR_mem_r7 rR hk4 hL)
    (pi_div_two_mem_r7 k rL rR) hcfg.gff hcfg.flow_αR hcfg.flow_βL hmαR hmβL (fun ω => (he ω).1)
    (fun ω => (he ω).2.2.1) (hcfg.regular.mono fun _ h => ⟨h.2.2.2.2.1, h.2.2.2.2.2.2.1⟩)
  have hwR := OuterIn.ae_walls_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow hθRm hflR hRs hV.η_cont
    hV.η_zero hV.η_trace
  filter_upwards [hcfg.ae_leftOuter h55 hk4 hL hR hc hc' hθL, hp, hV.R_ae, hV.L_ae, hMae, hwR, hsubAE]
    with ω hω hpω hRe hLe hMe hwRω hsubω hconf hpos
  rw [← hRe, ← hLe] at hω
  rw [← hRe] at hpω
  rw [hMe] at hsubω
  obtain ⟨-, hM, -, -, hO, hcR, hcL, ho, -⟩ := hω
  exact barrierAttachConst_right_of_sub hconf hpos hM hO hcR hcL hpω.2.1 ho (hV.η_cont ω) (hV.η_zero ω) hwRω.1
    hwRω.2 fun q' hq' hc' hp' a b h1 h2 h3 h4 => (hsubω q' hq' hc' hp' a b h1 h2 h3 h4).1

end Port0

section Port1

variable {k rL rR : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞} {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}

/-- **Margin-general port of `OuterGeomExt.ae_attachRight`**:
the same proof with the margins `(πχ(16/k), 0)` replaced by `(c, c')`, `c ≥ πχ(16/k)`, `c' ≥ 0`
(constant-angle strip system from `StripSafe.exists_isConstStripSystem`). -/
theorem ae_attachRightM (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    {c c' : ℝ} (hcπ : π * chiC (16 / k) ≤ c) (hc' : 0 ≤ c')
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hV : IsR7Versions P W' αR αL R L η) (hθR : R7.thetaR k rL < -(π / 2)) (hθL : ¬ π / 2 < R7.thetaL k rR) :
    ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
      IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
      BarrierAttachConst (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q)) (cfArcL (R ω) (L ω) (StripSys.rt q))
        (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 1))
        (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 0)) := by
  intro q _
  have hpi := Real.pi_pos
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hχ := Sec4.chiC_pos hκ hκ4
  have hc : 0 ≤ c := nonneg_of_pi_chi_le hk4 hcπ
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hc3 : 0 ≤ c' + (-(π / 2) - R7.thetaR k rL) * chiC (16 / k) :=
    add_nonneg hc' (mul_nonneg (by linarith) hχ.le)
  have hcfg' := isR7OuterConfig_rightExt h55 hk4 hR hc hc' hθR hcfg
  have hB := r7B_eq_d hk4 hθR c'
  obtain ⟨hcumL, hcumR⟩ := r7_strip_heights_ge (rL := rL) (rR := rR) hk4 hcπ hc'
  obtain ⟨Es, hS, hreg⟩ := StripSafe.exists_isConstStripSystem h44 hκ hκ4
    (isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')) hcumL hcumR hcfg.gff hcfg.counterflow
    ((ae_counterflow_trace_r7 hk4 hc hc' hcfg.gff hcfg.counterflow).mono fun ω hω => hω.1)
  rw [← hB] at hS hcumL hcumR
  obtain ⟨⟨M, hMc, hM0, hMm, hMae⟩, -⟩ := exists_frontierVersion hcfg
  have hV' : IsR7Versions P W' βR αL M L η :=
    ⟨hMc, hM0, hMm, hMae, hV.L_cont, hV.L_zero, hV.L_meas, hV.L_ae, hV.η_cont, hV.η_zero, hV.η_meas, hV.η_trace⟩
  have hLs : ∀ᵐ ω ∂P, IsSimpleProper (L ω) := by
    filter_upwards [hcfg.regular, hV.L_ae] with ω hω he
    rw [he]; exact IsSeedProper.isSimpleProper hω.2.2.2.1
  have hMs : ∀ᵐ ω ∂P, IsSimpleProper (M ω) := by
    filter_upwards [hcfg.regular, hMae] with ω hω he
    rw [he]; exact IsSeedProper.isSimpleProper hω.2.1
  have hθLm : R7.thetaL k rR ∈ Icc (-(π / 2)) (π / 2) :=
    ⟨(R7.neg_pi_div_two_lt_thetaL hk4 hR).le, not_lt.1 hθL⟩
  have hflL := IsFlowLine.congr_path (η' := L) hcfg.flow_αL (hV.L_ae.mono fun ω hω t _ => by rw [hω])
  have hflM := IsFlowLine.congr_path (η' := M) hcfg.flow_βR (hMae.mono fun ω hω t _ => by rw [hω])
  have hfirstL := firstHit_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow hθLm hflL hLs hV.η_zero
    hV.η_trace
  have hfirstM := firstHit_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow (θ := -(π / 2))
    ⟨le_rfl, by linarith⟩ hflM hMs hV.η_zero hV.η_trace
  have hd : -2 < k / 2 - 4 := by linarith
  have hmax : max (k / 2 - 4) rR = k / 2 - 4 := max_eq_left (not_lt.1 (mt (R7.d_lt_rR_iff hk4).1 hθL))
  have hext := StripSafe.r7Attach_of_constStrip h44 hk4 hd hR hmax hc hc3 hcfg' hS hreg hcumL hcumR hV'
    hfirstM hfirstL
  have hsubAE : ∀ᵐ ω ∂P, ∀ q' : ℚ, 0 < q' → IsChangeConfigInc (M ω) (L ω) (StripSys.rt q') →
      0 < rightLo (M ω) (L ω) (StripSys.rt q') →
      Sec6.AttachmentConstancy (η ω) (cfPocket (M ω) (L ω) (StripSys.rt q')) (cfArcR (M ω) (L ω) (StripSys.rt q'))
        (cfArcL (M ω) (L ω) (StripSys.rt q')) (firstHit (η ω) (cfArcR (M ω) (L ω) (StripSys.rt q') 1))
        (firstHit (η ω) (cfArcR (M ω) (L ω) (StripSys.rt q') 0)) := by
    rw [ae_all_iff]
    intro q'
    by_cases hq' : 0 < q'
    · filter_upwards [hext.1 q' hq'] with ω hω _ using hω
    · exact ae_of_all _ fun ω h' => absurd h' hq'
  obtain ⟨_ΦαR, ΦβR, _ΦβL, ΦαL, _, hmβR, _, hmαL, he⟩ := hcfg.borel
  have hp := ae_pair_r7 h55 hk4 hc hc' (R7.neg_pi_div_two_lt_thetaL hk4 hR) (neg_pi_div_two_mem_r7 k rL rR)
    (thetaL_mem_r7 rL hk4 hR) hcfg.gff hcfg.flow_βR hcfg.flow_αL hmβR hmαL (fun ω => (he ω).2.1)
    (fun ω => (he ω).2.2.2) (hcfg.regular.mono fun _ h => ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩)
  have hwL := OuterIn.ae_walls_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow hθLm hflL hLs hV.η_cont
    hV.η_zero hV.η_trace
  filter_upwards [hcfg.ae_rightOuter h55 hk4 hL hR hc hc' hθR, hp, hV.R_ae, hV.L_ae, hMae, hwL, hsubAE]
    with ω hω hpω hRe hLe hMe hwLω hsubω hconf hpos
  rw [← hRe, ← hLe] at hω
  rw [← hLe] at hpω
  rw [hMe] at hsubω
  obtain ⟨-, hM, -, -, hO, hcR, hcL, ho, -⟩ := hω
  exact barrierAttachConst_left_of_sub hconf hpos hM hO hcR hcL hpω.2.2 ho (hV.η_cont ω) (hV.η_zero ω) hwLω.1
    hwLω.2 fun q' hq' hc' hp' a b h1 h2 h3 h4 => (hsubω q' hq' hc' hp' a b h1 h2 h3 h4).2

end Port1

section Port2

variable {k rL rR : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞} {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}

/-- **Margin-general port of `OuterGeomExtInf.ae_attachLeftInf`**:
the same proof with the margins `(πχ(16/k), 0)` replaced by `(c, c')`, `c ≥ πχ(16/k)`, `c' ≥ 0`
(constant-angle strip system from `StripSafe.exists_isConstStripSystem`). -/
theorem ae_attachLeftInfM (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    {c c' : ℝ} (hcπ : π * chiC (16 / k) ≤ c) (hc' : 0 ≤ c')
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hV : IsR7Versions P W' αR αL R L η) (hθL : π / 2 < R7.thetaL k rR) (hθR : ¬ R7.thetaR k rL < -(π / 2)) :
    ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
      IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
      BarrierAttachConstInf (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q)) (cfArcRInf (R ω) (L ω) (StripSys.rt q))
        (firstHit (η ω) (cfArcRInf (R ω) (L ω) (StripSys.rt q) 0)) := by
  intro q _
  have hpi := Real.pi_pos
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hχ := Sec4.chiC_pos hκ hκ4
  have hc : 0 ≤ c := nonneg_of_pi_chi_le hk4 hcπ
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hc2 : 0 ≤ c + (R7.thetaL k rR - π / 2) * chiC (16 / k) :=
    add_nonneg hc (mul_nonneg (by linarith) hχ.le)
  have hcfg' := isR7OuterConfig_leftExt h55 hk4 hL hc hc' hθL hcfg
  have hA := r7A_eq_d hk4 hθL c
  obtain ⟨hcumL, hcumR⟩ := r7_strip_heights_ge (rL := rL) (rR := rR) hk4 hcπ hc'
  obtain ⟨Es, hS, hreg⟩ := StripSafe.exists_isConstStripSystem h44 hκ hκ4
    (isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')) hcumL hcumR hcfg.gff hcfg.counterflow
    ((ae_counterflow_trace_r7 hk4 hc hc' hcfg.gff hcfg.counterflow).mono fun ω hω => hω.1)
  rw [← hA] at hS hcumL hcumR
  obtain ⟨-, M, hMc, hM0, hMm, hMae⟩ := exists_frontierVersion hcfg
  have hV' : IsR7Versions P W' αR βL R M η :=
    ⟨hV.R_cont, hV.R_zero, hV.R_meas, hV.R_ae, hMc, hM0, hMm, hMae, hV.η_cont, hV.η_zero, hV.η_meas, hV.η_trace⟩
  have hRs : ∀ᵐ ω ∂P, IsSimpleProper (R ω) := by
    filter_upwards [hcfg.regular, hV.R_ae] with ω hω he
    rw [he]; exact IsSeedProper.isSimpleProper hω.1
  have hMs : ∀ᵐ ω ∂P, IsSimpleProper (M ω) := by
    filter_upwards [hcfg.regular, hMae] with ω hω he
    rw [he]; exact IsSeedProper.isSimpleProper hω.2.2.1
  have hθRm : R7.thetaR k rL ∈ Icc (-(π / 2)) (π / 2) :=
    ⟨not_lt.1 hθR, (R7.thetaR_lt_pi_div_two hk4 hL).le⟩
  have hflR := IsFlowLine.congr_path (η' := R) hcfg.flow_αR (hV.R_ae.mono fun ω hω t _ => by rw [hω])
  have hflM := IsFlowLine.congr_path (η' := M) hcfg.flow_βL (hMae.mono fun ω hω t _ => by rw [hω])
  have hfirstR := firstHit_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow hθRm hflR hRs hV.η_zero
    hV.η_trace
  have hfirstM := firstHit_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow (θ := π / 2)
    ⟨by linarith, le_rfl⟩ hflM hMs hV.η_zero hV.η_trace
  have hd : -2 < k / 2 - 4 := by linarith
  have hmax : max rL (k / 2 - 4) = k / 2 - 4 := max_eq_right (not_lt.1 (mt (R7.d_lt_rL_iff hk4).1 hθR))
  have hext := StripSafe.r7Attach_of_constStrip h44 hk4 hL hd hmax hc2 hc' hcfg' hS hreg hcumL hcumR hV'
    hfirstR hfirstM
  have hsubAE : ∀ᵐ ω ∂P, ∀ q' : ℚ, 0 < q' → IsChangeConfigInc (R ω) (M ω) (StripSys.rt q') →
      0 < rightLo (R ω) (M ω) (StripSys.rt q') →
      Sec6.AttachmentConstancy (η ω) (cfPocket (R ω) (M ω) (StripSys.rt q')) (cfArcR (R ω) (M ω) (StripSys.rt q'))
        (cfArcL (R ω) (M ω) (StripSys.rt q')) (firstHit (η ω) (cfArcR (R ω) (M ω) (StripSys.rt q') 1))
        (firstHit (η ω) (cfArcR (R ω) (M ω) (StripSys.rt q') 0)) := by
    rw [ae_all_iff]
    intro q'
    by_cases hq' : 0 < q'
    · filter_upwards [hext.1 q' hq'] with ω hω _ using hω
    · exact ae_of_all _ fun ω h' => absurd h' hq'
  have hsubIAE : ∀ᵐ ω ∂P, ∀ q' : ℚ, 0 < q' → IsChangeConfigInc (R ω) (M ω) (StripSys.rt q') →
      rightLo (R ω) (M ω) (StripSys.rt q') = 0 →
      Sec6.AttachmentConstancyInf (η ω) (cfPocket (R ω) (M ω) (StripSys.rt q'))
        (cfArcRInf (R ω) (M ω) (StripSys.rt q')) (cfArcLInf (R ω) (M ω) (StripSys.rt q'))
        (firstHit (η ω) (cfArcRInf (R ω) (M ω) (StripSys.rt q') 0)) := by
    rw [ae_all_iff]
    intro q'
    by_cases hq' : 0 < q'
    · filter_upwards [hext.2 q' hq'] with ω hω _ using hω
    · exact ae_of_all _ fun ω h' => absurd h' hq'
  obtain ⟨ΦαR, _ΦβR, ΦβL, _ΦαL, hmαR, _, hmβL, _, he⟩ := hcfg.borel
  have hp := ae_pair_r7 h55 hk4 hc hc' (R7.thetaR_lt_pi_div_two hk4 hL) (thetaR_mem_r7 rR hk4 hL)
    (pi_div_two_mem_r7 k rL rR) hcfg.gff hcfg.flow_αR hcfg.flow_βL hmαR hmβL (fun ω => (he ω).1)
    (fun ω => (he ω).2.2.1) (hcfg.regular.mono fun _ h => ⟨h.2.2.2.2.1, h.2.2.2.2.2.2.1⟩)
  have hwR := OuterIn.ae_walls_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow hθRm hflR hRs hV.η_cont
    hV.η_zero hV.η_trace
  filter_upwards [hcfg.ae_leftOuter h55 hk4 hL hR hc hc' hθL, hp, hV.R_ae, hV.L_ae, hMae, hwR, hsubAE,
    hsubIAE] with ω hω hpω hRe hLe hMe hwRω hsubω hsubIω hconf h0
  rw [← hRe, ← hLe] at hω
  rw [← hRe] at hpω
  rw [hMe] at hsubω hsubIω
  obtain ⟨-, hM, -, -, hO, hcR, hcL, ho, -⟩ := hω
  exact barrierAttachConstInf_right_of_sub hconf h0 hM hO hcR hcL hpω.2.1 ho (hV.η_cont ω) (hV.η_zero ω) hwRω.1
    hwRω.2 (fun q' hq' hc' hp' a b h1 h2 h3 h4 => (hsubω q' hq' hc' hp' a b h1 h2 h3 h4).1)
    fun q' hq' hc' hp' a b h1 h2 h3 => (hsubIω q' hq' hc' hp' a b h1 h2 h3).1

end Port2

section Port3

variable {k rL rR : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞} {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}

/-- **Margin-general port of `OuterGeomExtInf.ae_attachRightInf`**:
the same proof with the margins `(πχ(16/k), 0)` replaced by `(c, c')`, `c ≥ πχ(16/k)`, `c' ≥ 0`
(constant-angle strip system from `StripSafe.exists_isConstStripSystem`). -/
theorem ae_attachRightInfM (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    {c c' : ℝ} (hcπ : π * chiC (16 / k) ≤ c) (hc' : 0 ≤ c')
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hV : IsR7Versions P W' αR αL R L η) (hθR : R7.thetaR k rL < -(π / 2)) (hθL : ¬ π / 2 < R7.thetaL k rR) :
    ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
      IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
      BarrierAttachConstInf (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q)) (cfArcLInf (R ω) (L ω) (StripSys.rt q))
        (firstHit (η ω) (cfArcRInf (R ω) (L ω) (StripSys.rt q) 0)) := by
  intro q _
  have hpi := Real.pi_pos
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hχ := Sec4.chiC_pos hκ hκ4
  have hc : 0 ≤ c := nonneg_of_pi_chi_le hk4 hcπ
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hc3 : 0 ≤ c' + (-(π / 2) - R7.thetaR k rL) * chiC (16 / k) :=
    add_nonneg hc' (mul_nonneg (by linarith) hχ.le)
  have hcfg' := isR7OuterConfig_rightExt h55 hk4 hR hc hc' hθR hcfg
  have hB := r7B_eq_d hk4 hθR c'
  obtain ⟨hcumL, hcumR⟩ := r7_strip_heights_ge (rL := rL) (rR := rR) hk4 hcπ hc'
  obtain ⟨Es, hS, hreg⟩ := StripSafe.exists_isConstStripSystem h44 hκ hκ4
    (isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')) hcumL hcumR hcfg.gff hcfg.counterflow
    ((ae_counterflow_trace_r7 hk4 hc hc' hcfg.gff hcfg.counterflow).mono fun ω hω => hω.1)
  rw [← hB] at hS hcumL hcumR
  obtain ⟨⟨M, hMc, hM0, hMm, hMae⟩, -⟩ := exists_frontierVersion hcfg
  have hV' : IsR7Versions P W' βR αL M L η :=
    ⟨hMc, hM0, hMm, hMae, hV.L_cont, hV.L_zero, hV.L_meas, hV.L_ae, hV.η_cont, hV.η_zero, hV.η_meas, hV.η_trace⟩
  have hLs : ∀ᵐ ω ∂P, IsSimpleProper (L ω) := by
    filter_upwards [hcfg.regular, hV.L_ae] with ω hω he
    rw [he]; exact IsSeedProper.isSimpleProper hω.2.2.2.1
  have hMs : ∀ᵐ ω ∂P, IsSimpleProper (M ω) := by
    filter_upwards [hcfg.regular, hMae] with ω hω he
    rw [he]; exact IsSeedProper.isSimpleProper hω.2.1
  have hθLm : R7.thetaL k rR ∈ Icc (-(π / 2)) (π / 2) :=
    ⟨(R7.neg_pi_div_two_lt_thetaL hk4 hR).le, not_lt.1 hθL⟩
  have hflL := IsFlowLine.congr_path (η' := L) hcfg.flow_αL (hV.L_ae.mono fun ω hω t _ => by rw [hω])
  have hflM := IsFlowLine.congr_path (η' := M) hcfg.flow_βR (hMae.mono fun ω hω t _ => by rw [hω])
  have hfirstL := firstHit_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow hθLm hflL hLs hV.η_zero
    hV.η_trace
  have hfirstM := firstHit_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow (θ := -(π / 2))
    ⟨le_rfl, by linarith⟩ hflM hMs hV.η_zero hV.η_trace
  have hd : -2 < k / 2 - 4 := by linarith
  have hmax : max (k / 2 - 4) rR = k / 2 - 4 := max_eq_left (not_lt.1 (mt (R7.d_lt_rR_iff hk4).1 hθL))
  have hext := StripSafe.r7Attach_of_constStrip h44 hk4 hd hR hmax hc hc3 hcfg' hS hreg hcumL hcumR hV'
    hfirstM hfirstL
  have hsubAE : ∀ᵐ ω ∂P, ∀ q' : ℚ, 0 < q' → IsChangeConfigInc (M ω) (L ω) (StripSys.rt q') →
      0 < rightLo (M ω) (L ω) (StripSys.rt q') →
      Sec6.AttachmentConstancy (η ω) (cfPocket (M ω) (L ω) (StripSys.rt q')) (cfArcR (M ω) (L ω) (StripSys.rt q'))
        (cfArcL (M ω) (L ω) (StripSys.rt q')) (firstHit (η ω) (cfArcR (M ω) (L ω) (StripSys.rt q') 1))
        (firstHit (η ω) (cfArcR (M ω) (L ω) (StripSys.rt q') 0)) := by
    rw [ae_all_iff]
    intro q'
    by_cases hq' : 0 < q'
    · filter_upwards [hext.1 q' hq'] with ω hω _ using hω
    · exact ae_of_all _ fun ω h' => absurd h' hq'
  have hsubIAE : ∀ᵐ ω ∂P, ∀ q' : ℚ, 0 < q' → IsChangeConfigInc (M ω) (L ω) (StripSys.rt q') →
      rightLo (M ω) (L ω) (StripSys.rt q') = 0 →
      Sec6.AttachmentConstancyInf (η ω) (cfPocket (M ω) (L ω) (StripSys.rt q'))
        (cfArcRInf (M ω) (L ω) (StripSys.rt q')) (cfArcLInf (M ω) (L ω) (StripSys.rt q'))
        (firstHit (η ω) (cfArcRInf (M ω) (L ω) (StripSys.rt q') 0)) := by
    rw [ae_all_iff]
    intro q'
    by_cases hq' : 0 < q'
    · filter_upwards [hext.2 q' hq'] with ω hω _ using hω
    · exact ae_of_all _ fun ω h' => absurd h' hq'
  obtain ⟨_ΦαR, ΦβR, _ΦβL, ΦαL, _, hmβR, _, hmαL, he⟩ := hcfg.borel
  have hp := ae_pair_r7 h55 hk4 hc hc' (R7.neg_pi_div_two_lt_thetaL hk4 hR) (neg_pi_div_two_mem_r7 k rL rR)
    (thetaL_mem_r7 rL hk4 hR) hcfg.gff hcfg.flow_βR hcfg.flow_αL hmβR hmαL (fun ω => (he ω).2.1)
    (fun ω => (he ω).2.2.2) (hcfg.regular.mono fun _ h => ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩)
  have hwL := OuterIn.ae_walls_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow hθLm hflL hLs hV.η_cont
    hV.η_zero hV.η_trace
  filter_upwards [hcfg.ae_rightOuter h55 hk4 hL hR hc hc' hθR, hp, hV.R_ae, hV.L_ae, hMae, hwL, hsubAE,
    hsubIAE] with ω hω hpω hRe hLe hMe hwLω hsubω hsubIω hconf h0
  rw [← hRe, ← hLe] at hω
  rw [← hLe] at hpω
  rw [hMe] at hsubω hsubIω
  obtain ⟨-, hM, -, -, hO, hcR, hcL, ho, -⟩ := hω
  exact barrierAttachConstInf_left_of_sub hconf h0 hM hO hcR hcL hpω.2.2 ho (hV.η_cont ω) (hV.η_zero ω) hwLω.1
    hwLω.2 (fun q' hq' hc' hp' a b h1 h2 h3 h4 => (hsubω q' hq' hc' hp' a b h1 h2 h3 h4).2)
    fun q' hq' hc' hp' a b h1 h2 h3 => (hsubIω q' hq' hc' hp' a b h1 h2 h3).2

end Port3

section Port4

variable {k rL rR : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}
  {b' : ℝ → ℝ} {J' : Finset ℝ} {h' h'' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
  {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}

/-- **Margin-general port of `Aux41OOMixedInf.ae_mixedInfLeft`**:
the same proof with the margins `(πχ(16/k), 0)` replaced by `(c, c')`, `c ≥ πχ(16/k)`, `c' ≥ 0`
(constant-angle strip system from `StripSafe.exists_isConstStripSystem`). -/
theorem ae_mixedInfLeftM (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    {c c' : ℝ} (hcπ : π * chiC (16 / k) ≤ c) (hc' : 0 ≤ c')
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B) (hV : IsR7Versions P W' αR αL R L η)
    (hθL : π / 2 < R7.thetaL k rR) (hθR : ¬ R7.thetaR k rL < -(π / 2)) (q : ℚ) (hq : 0 < q) :
    ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
      PocketGapEqInf (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
          (firstHit (η ω) (cfArcRInf (R ω) (L ω) (StripSys.rt q) 0)) ∧
        OuterRelLoewnerInf (R ω) (L ω) (StripSys.rt q) (η ω) := by
  have hpi := Real.pi_pos
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hc : 0 ≤ c := nonneg_of_pi_chi_le hk4 hcπ
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hreg := hcfg.regular
  have hβLs : ∀ᵐ ω ∂P, IsSimpleProper (βL ω) := hreg.mono fun ω hω => IsSeedProper.isSimpleProper hω.2.2.1
  have htrace := ae_isLoewnerTrace_counterflow_r7 hk4 hc hc' hcfg.gff hcfg.counterflow hV.η_trace
  have h42 := ae_noSimpleArc_counterflow_r7 hk4 hc hc' hcfg.gff hcfg.counterflow hD hV.η_trace
  have hav := ae_avoid_counterflow_r7 hk4 hc hc' hcfg hV.η_trace
  have hwβL := ae_walls_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow (θ := π / 2)
    ⟨by linarith, le_rfl⟩ hcfg.flow_βL hβLs hV.η_cont hV.η_zero hV.η_trace
  have hθRm : R7.thetaR k rL ∈ Icc (-(π / 2)) (π / 2) :=
    ⟨not_lt.1 hθR, (R7.thetaR_lt_pi_div_two hk4 hL).le⟩
  have hRs : ∀ᵐ ω ∂P, IsSimpleProper (R ω) := by
    filter_upwards [hreg, hV.R_ae] with ω hω he
    rw [he]; exact IsSeedProper.isSimpleProper hω.1
  have hflR := IsFlowLine.congr_path (η' := R) hcfg.flow_αR (hV.R_ae.mono fun ω hω t _ => by rw [hω])
  have hwR := ae_walls_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow hθRm hflR hRs hV.η_cont
    hV.η_zero hV.η_trace
  filter_upwards [hcfg.ae_leftOuter h55 hk4 hL hR hc hc' hθL, hV.R_ae, hV.L_ae, htrace, h42, hav, hwβL,
    hwR, ae_attachLeftInfM h44 h411 h51 h47 h47T hk4 hL hR hcπ hc' hcfg hV hθL hθR q hq]
    with ω hω hRe hLe htr h42ω havω hwM hwRω hACω hconf h0
  rw [← hRe, ← hLe] at hω
  obtain ⟨-, hM, -, -, hO, hcR, hcL, ho, -⟩ := hω
  exact mixedInf_leftOuter hconf h0 hM hO hcR hcL ho htr.1 htr.2.1
    (by simpa only [Real.toNNReal_zero] using htr.2.2) hwRω.1 hwRω.2 hwM.1
    (fun t ht hm => havω t ht (Or.inr hm)) h42ω (hACω hconf h0)

end Port4

section Port5

variable {k rL rR : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}
  {b' : ℝ → ℝ} {J' : Finset ℝ} {h' h'' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
  {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}

/-- **Margin-general port of `Aux41OOMixedInf.ae_mixedInfRight`**:
the same proof with the margins `(πχ(16/k), 0)` replaced by `(c, c')`, `c ≥ πχ(16/k)`, `c' ≥ 0`
(constant-angle strip system from `StripSafe.exists_isConstStripSystem`). -/
theorem ae_mixedInfRightM (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    {c c' : ℝ} (hcπ : π * chiC (16 / k) ≤ c) (hc' : 0 ≤ c')
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B) (hV : IsR7Versions P W' αR αL R L η)
    (hθR : R7.thetaR k rL < -(π / 2)) (hθL : ¬ π / 2 < R7.thetaL k rR) (q : ℚ) (hq : 0 < q) :
    ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
      PocketGapEqInf (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
          (firstHit (η ω) (cfArcRInf (R ω) (L ω) (StripSys.rt q) 0)) ∧
        OuterRelLoewnerInf (R ω) (L ω) (StripSys.rt q) (η ω) := by
  have hpi := Real.pi_pos
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hc : 0 ≤ c := nonneg_of_pi_chi_le hk4 hcπ
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hreg := hcfg.regular
  have hβRs : ∀ᵐ ω ∂P, IsSimpleProper (βR ω) := hreg.mono fun ω hω => IsSeedProper.isSimpleProper hω.2.1
  have htrace := ae_isLoewnerTrace_counterflow_r7 hk4 hc hc' hcfg.gff hcfg.counterflow hV.η_trace
  have h42 := ae_noSimpleArc_counterflow_r7 hk4 hc hc' hcfg.gff hcfg.counterflow hD hV.η_trace
  have hav := ae_avoid_counterflow_r7 hk4 hc hc' hcfg hV.η_trace
  have hwβR := ae_walls_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow (θ := -(π / 2))
    ⟨le_rfl, by linarith⟩ hcfg.flow_βR hβRs hV.η_cont hV.η_zero hV.η_trace
  have hθLm : R7.thetaL k rR ∈ Icc (-(π / 2)) (π / 2) :=
    ⟨(R7.neg_pi_div_two_lt_thetaL hk4 hR).le, not_lt.1 hθL⟩
  have hLs : ∀ᵐ ω ∂P, IsSimpleProper (L ω) := by
    filter_upwards [hreg, hV.L_ae] with ω hω he
    rw [he]; exact IsSeedProper.isSimpleProper hω.2.2.2.1
  have hflL := IsFlowLine.congr_path (η' := L) hcfg.flow_αL (hV.L_ae.mono fun ω hω t _ => by rw [hω])
  have hwL := ae_walls_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow hθLm hflL hLs hV.η_cont
    hV.η_zero hV.η_trace
  filter_upwards [hcfg.ae_rightOuter h55 hk4 hL hR hc hc' hθR, hV.R_ae, hV.L_ae, htrace, h42, hav, hwβR,
    hwL, ae_attachRightInfM h44 h411 h51 h47 h47T hk4 hL hR hcπ hc' hcfg hV hθR hθL q hq]
    with ω hω hRe hLe htr h42ω havω hwM hwLω hACω hconf h0
  rw [← hRe, ← hLe] at hω
  obtain ⟨-, hM, -, -, hO, hcR, hcL, ho, -⟩ := hω
  exact mixedInf_rightOuter hconf h0 hM hO hcR hcL ho htr.1 htr.2.1
    (by simpa only [Real.toNNReal_zero] using htr.2.2) hwLω.1 hwLω.2 hwM.1
    (fun t ht hm => havω t ht (Or.inl hm)) h42ω (hACω hconf h0)

end Port5

section Port6

variable {k rL rR : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}
  {b' : ℝ → ℝ} {J' : Finset ℝ} {h' h'' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
  {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}

/-- **Margin-general port of `Aux41OOMixedInf.outerGeomRestMixedInf_of_config`**:
the same proof with the margins `(πχ(16/k), 0)` replaced by `(c, c')`, `c ≥ πχ(16/k)`, `c' ≥ 0`
(constant-angle strip system from `StripSafe.exists_isConstStripSystem`). -/
theorem outerGeomRestMixedInf_of_configM (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    {c c' : ℝ} (hcπ : π * chiC (16 / k) ≤ c) (hc' : 0 ≤ c')
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B) (hV : IsR7Versions P W' αR αL R L η) :
    OuterGeomRestMixedInf k rL rR P R L η :=
  ⟨fun hθL hθR q hq => ae_mixedInfLeftM h44 h411 h51 h47 h47T hk4 hL hR hcπ hc' hcfg hD hV hθL hθR q hq,
    fun hθR hθL q hq => ae_mixedInfRightM h44 h411 h51 h47 h47T hk4 hL hR hcπ hc' hcfg hD hV hθR hθL q hq⟩

end Port6

section Port7

variable {k rL rR : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}
  {b' : ℝ → ℝ} {J' : Finset ℝ} {h' h'' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
  {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}

/-- **Margin-general port of `Aux41OOWireInf.outerGeomRestOO_of_mixedInf`**:
the same proof with the margins `(πχ(16/k), 0)` replaced by `(c, c')`, `c ≥ πχ(16/k)`, `c' ≥ 0`
(constant-angle strip system from `StripSafe.exists_isConstStripSystem`). -/
theorem outerGeomRestOO_of_mixedInfM (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    {c c' : ℝ} (hcπ : π * chiC (16 / k) ≤ c) (hc' : 0 ≤ c')
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B) (hV : IsR7Versions P W' αR αL R L η)
    (hrest : OuterGeomRestMixedInf k rL rR P R L η) : OuterGeomRestOO k rL rR P R L η := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hc : 0 ≤ c := nonneg_of_pi_chi_le hk4 hcπ
  exact ⟨hrest.infLeft, hrest.infRight,
    fun hθR hθL q _ => ae_outerRelLoewnerInf h411 h51 h47 h47T hk4 hL hR hc hc' hcfg hD hV hθR hθL q⟩

end Port7

section Port8

variable {k rL rR : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}
  {b' : ℝ → ℝ} {J' : Finset ℝ} {h' h'' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
  {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}

/-- **Margin-general port of `Aux41OOWire.outerGeomRest_of_restOO`**:
the same proof with the margins `(πχ(16/k), 0)` replaced by `(c, c')`, `c ≥ πχ(16/k)`, `c' ≥ 0`
(constant-angle strip system from `StripSafe.exists_isConstStripSystem`). -/
theorem outerGeomRest_of_restOOM (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hA : Sec5.PartAInputsSixteenDivOfClearance) (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    {c c' : ℝ} (hcπ : π * chiC (16 / k) ≤ c) (hc' : 0 ≤ c')
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B) (hV : IsR7Versions P W' αR αL R L η)
    (hrest : OuterGeomRestOO k rL rR P R L η) : OuterGeomRest k rL rR P R L η := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hc : 0 ≤ c := nonneg_of_pi_chi_le hk4 hcπ
  exact ⟨fun hθR hθL q _ => ae_outerRelLoewner h411 h51 h47 h47T hA hk4 hL hR hc hc' hcfg hD hV hθR hθL q,
    hrest.infLeft, hrest.infRight, hrest.relInfOuterOuter⟩

end Port8

section Port9

variable {k rL rR : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞} {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}

omit [StandardBorelSpace Ω] in
/-- **Margin-general port of `OuterGeomWire.ae_outerOuterAttach`**:
the same proof with the margins `(πχ(16/k), 0)` replaced by `(c, c')`, `c ≥ πχ(16/k)`, `c' ≥ 0`
(constant-angle strip system from `StripSafe.exists_isConstStripSystem`). -/
theorem ae_outerOuterAttachM (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    {c c' : ℝ} (hcπ : π * chiC (16 / k) ≤ c) (hc' : 0 ≤ c')
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hV : IsR7Versions P W' αR αL R L η) (hθR : R7.thetaR k rL < -(π / 2)) (hθL : π / 2 < R7.thetaL k rR) :
    ∀ᵐ ω ∂P, ∀ r : ℝ≥0, IsChangeConfigInc (R ω) (L ω) r →
      (0 < rightLo (R ω) (L ω) r → OuterOuterAttach (R ω) (L ω) (βR ω) r (η ω)) ∧
      (rightLo (R ω) (L ω) r = 0 → OuterOuterAttachInf (R ω) (L ω) (βR ω) r (η ω)) := by
  have hpi := Real.pi_pos
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hc : 0 ≤ c := nonneg_of_pi_chi_le hk4 hcπ
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hβRs : ∀ᵐ ω ∂P, IsSimpleProper (βR ω) := hcfg.regular.mono fun ω hω => IsSeedProper.isSimpleProper hω.2.1
  have hwβR := OuterIn.ae_walls_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow (θ := -(π / 2))
    ⟨le_rfl, by linarith⟩ hcfg.flow_βR hβRs hV.η_cont hV.η_zero hV.η_trace
  filter_upwards [hcfg.ae_outerOuter h55 hk4 hL hR hc hc' hθR hθL, hV.R_ae, hV.L_ae, hwβR]
    with ω hω hRe hLe hwR
  rw [← hRe, ← hLe] at hω
  obtain ⟨-, hβR, -, -, -, hO₁, -, hc₁R, hc₁L, -⟩ := hω
  intro r hconf
  exact ⟨fun hpos => outerOuterAttach hconf hpos hβR hO₁ hc₁R hc₁L (hV.η_cont ω) (hV.η_zero ω) hwR.1 hwR.2,
    fun h0 => outerOuterAttachInf hconf h0 hβR hO₁ hc₁R hc₁L (hV.η_cont ω) (hV.η_zero ω) hwR.1 hwR.2⟩

end Port9

section Port10

variable {k rL rR : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞} {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}

/-- **Margin-general port of `OuterGeomWire.outerGeomInputs_of_rest`**:
the same proof with the margins `(πχ(16/k), 0)` replaced by `(c, c')`, `c ≥ πχ(16/k)`, `c' ≥ 0`
(constant-angle strip system from `StripSafe.exists_isConstStripSystem`). -/
theorem outerGeomInputs_of_restM (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    {c c' : ℝ} (hcπ : π * chiC (16 / k) ≤ c) (hc' : 0 ≤ c')
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hV : IsR7Versions P W' αR αL R L η) (hrest : OuterGeomRest k rL rR P R L η) :
    OuterGeomInputs k rL rR P βR βL R L η := by
  refine ⟨fun hθL hθR => ae_attachLeftM h44 h411 h51 h47 h47T hk4 hL hR hcπ hc' hcfg hV hθL hθR,
    fun hθR hθL => ae_attachRightM h44 h411 h51 h47 h47T hk4 hL hR hcπ hc' hcfg hV hθR hθL,
    fun hθR hθL q hq => ?_, fun hθL hθR q hq => ?_, fun hθR hθL q hq => ?_, fun hθR hθL q hq => ?_⟩
  · filter_upwards [ae_outerOuterAttachM h411 h51 h47 h47T hk4 hL hR hcπ hc' hcfg hV hθR hθL,
      hrest.relOuterOuter hθR hθL q hq] with ω hω hloc hconf hpos
    exact ⟨(hω _ hconf).1 hpos, hloc hconf hpos⟩
  · filter_upwards [ae_attachLeftInfM h44 h411 h51 h47 h47T hk4 hL hR hcπ hc' hcfg hV hθL hθR q hq,
      hrest.infLeft hθL hθR q hq] with ω hAC hrem hconf h0
    exact ⟨hAC hconf h0, hrem hconf h0⟩
  · filter_upwards [ae_attachRightInfM h44 h411 h51 h47 h47T hk4 hL hR hcπ hc' hcfg hV hθR hθL q hq,
      hrest.infRight hθR hθL q hq] with ω hAC hrem hconf h0
    exact ⟨hAC hconf h0, hrem hconf h0⟩
  · filter_upwards [ae_outerOuterAttachM h411 h51 h47 h47T hk4 hL hR hcπ hc' hcfg hV hθR hθL,
      hrest.relInfOuterOuter hθR hθL q hq] with ω hω hloc hconf h0
    exact ⟨(hω _ hconf).2 h0, hloc hconf h0⟩

end Port10

section Final

/-- **`OuterGeomAeMRemaining` on the outer range at arbitrary margins `c ≥ πχ(16/k)`, `c' ≥ 0`**, from the landed
named inputs of the R.7 wiring (the margin-general ports of the landed std-margin chain, then
`OuterIn.ae_outerGeom`, `OuterIn.ae_outerGeomInf`). -/
theorem outerGeomAeMRemaining_of_inputs {k rL rR : ℝ} (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hA : Sec5.PartAInputsSixteenDivOfClearance) {c c' : ℝ} (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hmax : k / 2 - 4 < max rL rR) (hcπ : π * chiC (16 / k) ≤ c) (hc' : 0 ≤ c') :
    OuterGeomAeMRemaining.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD R L η hV q hq
  have hc := nonneg_of_pi_chi_le hk4 hcπ
  have hin : OuterGeomInputs k rL rR P βR βL R L η :=
    outerGeomInputs_of_restM h44 h411 h51 h47 h47T hk4 hL hR hcπ hc' hcfg hV
      (outerGeomRest_of_restOOM h411 h51 h47 h47T hA hk4 hL hR hcπ hc' hcfg hD hV
        (outerGeomRestOO_of_mixedInfM h411 h51 h47 h47T hk4 hL hR hcπ hc' hcfg hD hV
          (outerGeomRestMixedInf_of_configM h44 h411 h51 h47 h47T hk4 hL hR hcπ hc' hcfg hD hV)))
  exact ⟨ae_outerGeom h411 h51 h47 h47T hA hk4 hL hR hmax hc hc' hcfg hD hV hin q hq,
    ae_outerGeomInf h411 h51 h47 h47T hk4 hL hR hmax hc hc' hcfg hD hV hin q hq⟩

end Final

end InteractingSLE.Sec7.R6Safe
