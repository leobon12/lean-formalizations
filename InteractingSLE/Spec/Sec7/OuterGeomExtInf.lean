/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.OuterGeomExt
import InteractingSLE.Spec.Sec7.OuterGeomInf

/-!
# Theorem R.7's mixed pockets opening at the flow seed: Aux. lemma 37 on every R.7 configuration

Packet PROVE-R7-OUTERGEOM. As `OuterGeomExt`, for pockets opening at the flow seed: Aux. lemma 37 in the extremal
pockets of the contained arm with the certified frontier (bounded and at the flow seed, both parts of
`StripSafe.r7Attach_of_constStrip`) and the pathwise transfer of `OuterGeomInf` give

* **`ae_attachLeftInf`**, **`ae_attachRightInf`**: the attachment conjuncts of `OuterIn.OuterGeomInputs.infLeft` and
  `…infRight`.

R48: as `OuterGeomExt`.
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

open WangWu Lemma71I PocketCoord PocketJordan R7StopIn R7Outer R7Leaves
open Sec5.Prop55Half (IsSeedProper)

section AttachInf

variable {k rL rR : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞} {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}

/-- **Aux. lemma 37 along the contained right side of the mixed pockets opening at the flow seed with an outer left
arm, on every R.7 configuration** (the first conjunct of `OuterIn.OuterGeomInputs.infLeft`): from Aux. lemma 37 in
the extremal pockets of the contained right arm with `β_L` (`StripSafe.r7Attach_of_constStrip` on
`isR7OuterConfig_leftExt`, both parts) and the pathwise transfer `barrierAttachConstInf_right_of_sub`. -/
theorem ae_attachLeftInf (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hcfg : IsR7OuterConfig k rL rR (π * chiC (16 / k)) 0 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
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
  have hc : 0 ≤ π * chiC (16 / k) := mul_nonneg hpi.le hχ.le
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hc2 : 0 ≤ π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k) :=
    add_nonneg hc (mul_nonneg (by linarith) hχ.le)
  have hcfg' := isR7OuterConfig_leftExt h55 hk4 hL hc le_rfl hθL hcfg
  have hA := r7A_eq_d hk4 hθL (π * chiC (16 / k))
  obtain ⟨Es, hS, hreg⟩ := StripSafe.exists_isConstStripSystem_r7 h44 hk4 hcfg
  obtain ⟨hcumL, hcumR⟩ := r7_strip_heights (rL := rL) (rR := rR) hk4
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
  have hfirstR := firstHit_r7 h411 h47 h47T hk4 hc le_rfl hcfg.gff hcfg.counterflow hθRm hflR hRs hV.η_zero
    hV.η_trace
  have hfirstM := firstHit_r7 h411 h47 h47T hk4 hc le_rfl hcfg.gff hcfg.counterflow (θ := π / 2)
    ⟨by linarith, le_rfl⟩ hflM hMs hV.η_zero hV.η_trace
  have hd : -2 < k / 2 - 4 := by linarith
  have hmax : max rL (k / 2 - 4) = k / 2 - 4 := max_eq_right (not_lt.1 (mt (R7.d_lt_rL_iff hk4).1 hθR))
  have hext := StripSafe.r7Attach_of_constStrip h44 hk4 hL hd hmax hc2 le_rfl hcfg' hS hreg hcumL hcumR hV'
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
  have hp := ae_pair_r7 h55 hk4 hc le_rfl (R7.thetaR_lt_pi_div_two hk4 hL) (thetaR_mem_r7 rR hk4 hL)
    (pi_div_two_mem_r7 k rL rR) hcfg.gff hcfg.flow_αR hcfg.flow_βL hmαR hmβL (fun ω => (he ω).1)
    (fun ω => (he ω).2.2.1) (hcfg.regular.mono fun _ h => ⟨h.2.2.2.2.1, h.2.2.2.2.2.2.1⟩)
  have hwR := OuterIn.ae_walls_r7 h411 h47 h47T hk4 hc le_rfl hcfg.gff hcfg.counterflow hθRm hflR hRs hV.η_cont
    hV.η_zero hV.η_trace
  filter_upwards [hcfg.ae_leftOuter h55 hk4 hL hR hc le_rfl hθL, hp, hV.R_ae, hV.L_ae, hMae, hwR, hsubAE,
    hsubIAE] with ω hω hpω hRe hLe hMe hwRω hsubω hsubIω hconf h0
  rw [← hRe, ← hLe] at hω
  rw [← hRe] at hpω
  rw [hMe] at hsubω hsubIω
  obtain ⟨-, hM, -, -, hO, hcR, hcL, ho, -⟩ := hω
  exact barrierAttachConstInf_right_of_sub hconf h0 hM hO hcR hcL hpω.2.1 ho (hV.η_cont ω) (hV.η_zero ω) hwRω.1
    hwRω.2 (fun q' hq' hc' hp' a b h1 h2 h3 h4 => (hsubω q' hq' hc' hp' a b h1 h2 h3 h4).1)
    fun q' hq' hc' hp' a b h1 h2 h3 => (hsubIω q' hq' hc' hp' a b h1 h2 h3).1

/-- **Aux. lemma 37 along the contained left side of the mixed pockets opening at the flow seed with an outer right
arm, on every R.7 configuration** (the first conjunct of `OuterIn.OuterGeomInputs.infRight`; the mirror of
`ae_attachLeftInf` with `β_R`). -/
theorem ae_attachRightInf (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hcfg : IsR7OuterConfig k rL rR (π * chiC (16 / k)) 0 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
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
  have hc : 0 ≤ π * chiC (16 / k) := mul_nonneg hpi.le hχ.le
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hc3 : 0 ≤ (0 : ℝ) + (-(π / 2) - R7.thetaR k rL) * chiC (16 / k) :=
    add_nonneg le_rfl (mul_nonneg (by linarith) hχ.le)
  have hcfg' := isR7OuterConfig_rightExt h55 hk4 hR hc le_rfl hθR hcfg
  have hB := r7B_eq_d hk4 hθR (0 : ℝ)
  obtain ⟨Es, hS, hreg⟩ := StripSafe.exists_isConstStripSystem_r7 h44 hk4 hcfg
  obtain ⟨hcumL, hcumR⟩ := r7_strip_heights (rL := rL) (rR := rR) hk4
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
  have hfirstL := firstHit_r7 h411 h47 h47T hk4 hc le_rfl hcfg.gff hcfg.counterflow hθLm hflL hLs hV.η_zero
    hV.η_trace
  have hfirstM := firstHit_r7 h411 h47 h47T hk4 hc le_rfl hcfg.gff hcfg.counterflow (θ := -(π / 2))
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
  have hp := ae_pair_r7 h55 hk4 hc le_rfl (R7.neg_pi_div_two_lt_thetaL hk4 hR) (neg_pi_div_two_mem_r7 k rL rR)
    (thetaL_mem_r7 rL hk4 hR) hcfg.gff hcfg.flow_βR hcfg.flow_αL hmβR hmαL (fun ω => (he ω).2.1)
    (fun ω => (he ω).2.2.2) (hcfg.regular.mono fun _ h => ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩)
  have hwL := OuterIn.ae_walls_r7 h411 h47 h47T hk4 hc le_rfl hcfg.gff hcfg.counterflow hθLm hflL hLs hV.η_cont
    hV.η_zero hV.η_trace
  filter_upwards [hcfg.ae_rightOuter h55 hk4 hL hR hc le_rfl hθR, hp, hV.R_ae, hV.L_ae, hMae, hwL, hsubAE,
    hsubIAE] with ω hω hpω hRe hLe hMe hwLω hsubω hsubIω hconf h0
  rw [← hRe, ← hLe] at hω
  rw [← hLe] at hpω
  rw [hMe] at hsubω hsubIω
  obtain ⟨-, hM, -, -, hO, hcR, hcL, ho, -⟩ := hω
  exact barrierAttachConstInf_left_of_sub hconf h0 hM hO hcR hcL hpω.2.2 ho (hV.η_cont ω) (hV.η_zero ω) hwLω.1
    hwLω.2 (fun q' hq' hc' hp' a b h1 h2 h3 h4 => (hsubω q' hq' hc' hp' a b h1 h2 h3 h4).2)
    fun q' hq' hc' hp' a b h1 h2 h3 => (hsubIω q' hq' hc' hp' a b h1 h2 h3).2

end AttachInf

end InteractingSLE.Sec7.OuterGeom
