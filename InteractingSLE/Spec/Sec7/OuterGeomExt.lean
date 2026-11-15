/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.OuterGeomSub
import InteractingSLE.Spec.Sec7.OuterInGeomAe
import InteractingSLE.Spec.Sec7.StripSafeWire

/-!
# Theorem R.7's mixed pockets: Aux. lemma 37 along the contained arm on every R.7 configuration

Packet PROVE-R7-OUTERGEOM. In an R.7 configuration with exactly one outer arm, the contained arm and the certified
frontier of the outer side are the two walls of an *extremal* R.7 configuration on the same field and counterflow:
with an outer left arm (`θ_L > π/2`), `(α_R, β_L)` is the configuration of weights `(r_L, d)` with the left height
raised by `(θ_L − π/2)χ` (`isR7OuterConfig_leftExt`, `r7A_eq_d`); mirror for an outer right arm
(`isR7OuterConfig_rightExt`, `r7B_eq_d`). PROVE-STRIPSYS-SAFE's `StripSafe.r7Attach_of_constStrip` then gives Aux.
lemma 37 in all extremal pockets (from `h44` alone; the constant-angle strip system is the original configuration's,
whose boundary data is the same function), and the pathwise transfer of `OuterGeomSub` gives Aux. lemma 37 along the
contained arm of every bounded mixed pocket:

* **`ae_attachLeft`** = `OuterIn.OuterGeomInputs.attachLeft`, **`ae_attachRight`** = `…attachRight`.

R48: the named statements used are `h44` (`AdmCode.Theorem12ParamCond44Statement`, R74), Propositions 4.11 and 5.1 in
chart `Q` and Lemma 4.7Q (`Lemma47QHitStatement`, `Lemma47QHitTStatement`), as in PROVE-R7-OUTERIN and
PROVE-STRIPSYS-SAFE; nothing uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any
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

open WangWu Lemma71I PocketCoord PocketJordan R7StopIn R7Outer R7Leaves
open Sec5.Prop55Half (IsSeedProper)

section Ext

variable {k rL rR c c' : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}

theorem thetaL_d (hk4 : 4 < k) : R7.thetaL k (k / 2 - 4) = π / 2 := (R7.rR_eq_d_iff hk4).1 rfl

theorem thetaR_d (hk4 : 4 < k) : R7.thetaR k (k / 2 - 4) = -(π / 2) := (R7.rL_eq_d_iff hk4).1 rfl

/-- The left boundary value of a configuration with an outer left arm, read with the certified frontier `β_L` as the
left wall (`r_R = d`): `a(r_R) + c = a(d) + (c + (θ_L − π/2)χ)`. -/
theorem r7A_eq_d (hk4 : 4 < k) (hθL : π / 2 < R7.thetaL k rR) (c : ℝ) :
    r7A k (k / 2 - 4) + (c + (R7.thetaL k rR - π / 2) * chiC (16 / k)) = r7A k rR + c := by
  simp only [r7A, r7ThetaHi, thetaL_d hk4, max_self, max_eq_left hθL.le]
  ring

/-- The right boundary value of a configuration with an outer right arm, with `β_R` as the right wall (`r_L = d`). -/
theorem r7B_eq_d (hk4 : 4 < k) (hθR : R7.thetaR k rL < -(π / 2)) (c' : ℝ) :
    r7B k (k / 2 - 4) + (c' + (-(π / 2) - R7.thetaR k rL) * chiC (16 / k)) = r7B k rL + c' := by
  simp only [r7B, r7ThetaLo, thetaR_d hk4, min_self, min_eq_left hθR.le]
  ring

/-- **The extremal configuration of the contained right arm and `β_L`** inside an R.7 configuration with an outer
left arm: the same field and counterflow, with `β_L` as the left wall (weight `r_R = d`, height shifted by
`(θ_L − π/2)χ`). -/
theorem isR7OuterConfig_leftExt (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) (hk4 : 4 < k) (hL : -2 < rL)
    (hc : 0 ≤ c) (hc' : 0 ≤ c') (hθL : π / 2 < R7.thetaL k rR)
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL) :
    IsR7OuterConfig k rL (k / 2 - 4) (c + (R7.thetaL k rR - π / 2) * chiC (16 / k)) c' P h W' ζ'
      αR βR βL βL ζαR ζβR ζβL ζβL := by
  have hA := r7A_eq_d hk4 hθL c
  have hθd := thetaL_d hk4
  obtain ⟨ΦαR, ΦβR, ΦβL, ΦαL, hmαR, hmβR, hmβL, hmαL, he⟩ := hcfg.borel
  have hp := ae_pair_r7 h55 hk4 hc hc' (R7.thetaR_lt_pi_div_two hk4 hL) (thetaR_mem_r7 rR hk4 hL)
    (pi_div_two_mem_r7 k rL rR) hcfg.gff hcfg.flow_αR hcfg.flow_βL hmαR hmβL (fun ω => (he ω).1)
    (fun ω => (he ω).2.2.1) (hcfg.regular.mono fun _ h => ⟨h.2.2.2.2.1, h.2.2.2.2.2.2.1⟩)
  refine ⟨by rw [hA]; exact hcfg.gff, hcfg.counterflow, by rw [hA]; exact hcfg.flow_αR,
    by rw [hA]; exact hcfg.flow_βR, by rw [hA]; exact hcfg.flow_βL, by rw [hA, hθd]; exact hcfg.flow_βL,
    ⟨ΦαR, ΦβR, ΦβL, ΦβL, hmαR, hmβR, hmβL, hmβL, fun ω => ⟨(he ω).1, (he ω).2.1, (he ω).2.2.1, (he ω).2.2.1⟩⟩,
    hcfg.regular.mono fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.1⟩, ?_, hcfg.avoid⟩
  filter_upwards [hcfg.order, hp] with ω hω hpω
  refine ⟨hω.1, hpω.1, hω.2.2.1, fun h' => absurd h' (by rw [hθd]; exact lt_irrefl _), hω.2.2.2.2.1,
    fun h' => absurd h' (by rw [hθd]; exact lt_irrefl _)⟩

/-- **The extremal configuration of `β_R` and the contained left arm** inside an R.7 configuration with an outer
right arm: `β_R` as the right wall (weight `r_L = d`, height shifted by `(−π/2 − θ_R)χ`). -/
theorem isR7OuterConfig_rightExt (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) (hk4 : 4 < k) (hR : -2 < rR)
    (hc : 0 ≤ c) (hc' : 0 ≤ c') (hθR : R7.thetaR k rL < -(π / 2))
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL) :
    IsR7OuterConfig k (k / 2 - 4) rR c (c' + (-(π / 2) - R7.thetaR k rL) * chiC (16 / k)) P h W' ζ'
      βR βR βL αL ζβR ζβR ζβL ζαL := by
  have hB := r7B_eq_d hk4 hθR c'
  have hθd := thetaR_d hk4
  obtain ⟨ΦαR, ΦβR, ΦβL, ΦαL, hmαR, hmβR, hmβL, hmαL, he⟩ := hcfg.borel
  have hp := ae_pair_r7 h55 hk4 hc hc' (R7.neg_pi_div_two_lt_thetaL hk4 hR) (neg_pi_div_two_mem_r7 k rL rR)
    (thetaL_mem_r7 rL hk4 hR) hcfg.gff hcfg.flow_βR hcfg.flow_αL hmβR hmαL (fun ω => (he ω).2.1)
    (fun ω => (he ω).2.2.2) (hcfg.regular.mono fun _ h => ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩)
  refine ⟨by rw [hB]; exact hcfg.gff, hcfg.counterflow, by rw [hB, hθd]; exact hcfg.flow_βR,
    by rw [hB]; exact hcfg.flow_βR, by rw [hB]; exact hcfg.flow_βL, by rw [hB]; exact hcfg.flow_αL,
    ⟨ΦβR, ΦβR, ΦβL, ΦαL, hmβR, hmβR, hmβL, hmαL, fun ω => ⟨(he ω).2.1, (he ω).2.1, (he ω).2.2.1, (he ω).2.2.2⟩⟩,
    hcfg.regular.mono fun _ h => ⟨h.2.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2⟩, ?_, hcfg.avoid⟩
  filter_upwards [hcfg.order, hp] with ω hω hpω
  refine ⟨hω.1, hpω.1, fun h' => absurd h' (by rw [hθd]; exact lt_irrefl _), hω.2.2.2.1,
    fun h' => absurd h' (by rw [hθd]; exact lt_irrefl _), hω.2.2.2.2.2⟩

end Ext

section Attach

variable {k rL rR : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞} {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- Versions of the two certified frontiers of an R.7 configuration (continuous, `0` at `0` at every sample,
measurable at fixed times). -/
theorem exists_frontierVersion {c c' : ℝ}
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL) :
    (∃ M : Ω → ℝ≥0 → ℂ, (∀ ω, Continuous (M ω)) ∧ (∀ ω, M ω 0 = 0) ∧ (∀ t, Measurable fun ω => M ω t) ∧
      ∀ᵐ ω ∂P, M ω = βR ω) ∧
    ∃ M : Ω → ℝ≥0 → ℂ, (∀ ω, Continuous (M ω)) ∧ (∀ ω, M ω 0 = 0) ∧ (∀ t, Measurable fun ω => M ω t) ∧
      ∀ᵐ ω ∂P, M ω = βL ω := by
  obtain ⟨_ΦαR, ΦβR, ΦβL, _ΦαL, _, hΦβR, hΦβL, _, hΦ⟩ := hcfg.borel
  have hmR : ∀ t, Measurable fun ω => βR ω t := fun t => by
    have e : (fun ω => βR ω t) = fun ω => ΦβR (h ω) t := funext fun ω => by rw [(hΦ ω).2.1]
    rw [e]; exact (measurable_pi_apply t).comp (hΦβR.comp hcfg.gff.1)
  have hmL : ∀ t, Measurable fun ω => βL ω t := fun t => by
    have e : (fun ω => βL ω t) = fun ω => ΦβL (h ω) t := funext fun ω => by rw [(hΦ ω).2.2.1]
    rw [e]; exact (measurable_pi_apply t).comp (hΦβL.comp hcfg.gff.1)
  exact ⟨exists_wallVersion hmR (hcfg.regular.mono fun ω hω => hω.2.1),
    exists_wallVersion hmL (hcfg.regular.mono fun ω hω => hω.2.2.1)⟩

/-- **Aux. lemma 37 along the contained right side of the bounded mixed pockets with an outer left arm, on every R.7
configuration** (`OuterIn.OuterGeomInputs.attachLeft`): from Aux. lemma 37 in the extremal pockets of the contained
right arm with `β_L` (`StripSafe.r7Attach_of_constStrip` on `isR7OuterConfig_leftExt`) and the pathwise transfer
`barrierAttachConst_right_of_sub`. -/
theorem ae_attachLeft (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hcfg : IsR7OuterConfig k rL rR (π * chiC (16 / k)) 0 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
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
  obtain ⟨ΦαR, _ΦβR, ΦβL, _ΦαL, hmαR, _, hmβL, _, he⟩ := hcfg.borel
  have hp := ae_pair_r7 h55 hk4 hc le_rfl (R7.thetaR_lt_pi_div_two hk4 hL) (thetaR_mem_r7 rR hk4 hL)
    (pi_div_two_mem_r7 k rL rR) hcfg.gff hcfg.flow_αR hcfg.flow_βL hmαR hmβL (fun ω => (he ω).1)
    (fun ω => (he ω).2.2.1) (hcfg.regular.mono fun _ h => ⟨h.2.2.2.2.1, h.2.2.2.2.2.2.1⟩)
  have hwR := OuterIn.ae_walls_r7 h411 h47 h47T hk4 hc le_rfl hcfg.gff hcfg.counterflow hθRm hflR hRs hV.η_cont
    hV.η_zero hV.η_trace
  filter_upwards [hcfg.ae_leftOuter h55 hk4 hL hR hc le_rfl hθL, hp, hV.R_ae, hV.L_ae, hMae, hwR, hsubAE]
    with ω hω hpω hRe hLe hMe hwRω hsubω hconf hpos
  rw [← hRe, ← hLe] at hω
  rw [← hRe] at hpω
  rw [hMe] at hsubω
  obtain ⟨-, hM, -, -, hO, hcR, hcL, ho, -⟩ := hω
  exact barrierAttachConst_right_of_sub hconf hpos hM hO hcR hcL hpω.2.1 ho (hV.η_cont ω) (hV.η_zero ω) hwRω.1
    hwRω.2 fun q' hq' hc' hp' a b h1 h2 h3 h4 => (hsubω q' hq' hc' hp' a b h1 h2 h3 h4).1

/-- **Aux. lemma 37 along the contained left side of the bounded mixed pockets with an outer right arm, on every R.7
configuration** (`OuterIn.OuterGeomInputs.attachRight`; the mirror of `ae_attachLeft` with `β_R`). -/
theorem ae_attachRight (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hcfg : IsR7OuterConfig k rL rR (π * chiC (16 / k)) 0 P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
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
  obtain ⟨_ΦαR, ΦβR, _ΦβL, ΦαL, _, hmβR, _, hmαL, he⟩ := hcfg.borel
  have hp := ae_pair_r7 h55 hk4 hc le_rfl (R7.neg_pi_div_two_lt_thetaL hk4 hR) (neg_pi_div_two_mem_r7 k rL rR)
    (thetaL_mem_r7 rL hk4 hR) hcfg.gff hcfg.flow_βR hcfg.flow_αL hmβR hmαL (fun ω => (he ω).2.1)
    (fun ω => (he ω).2.2.2) (hcfg.regular.mono fun _ h => ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩)
  have hwL := OuterIn.ae_walls_r7 h411 h47 h47T hk4 hc le_rfl hcfg.gff hcfg.counterflow hθLm hflL hLs hV.η_cont
    hV.η_zero hV.η_trace
  filter_upwards [hcfg.ae_rightOuter h55 hk4 hL hR hc le_rfl hθR, hp, hV.R_ae, hV.L_ae, hMae, hwL, hsubAE]
    with ω hω hpω hRe hLe hMe hwLω hsubω hconf hpos
  rw [← hRe, ← hLe] at hω
  rw [← hLe] at hpω
  rw [hMe] at hsubω
  obtain ⟨-, hM, -, -, hO, hcR, hcL, ho, -⟩ := hω
  exact barrierAttachConst_left_of_sub hconf hpos hM hO hcR hcL hpω.2.2 ho (hV.η_cont ω) (hV.η_zero ω) hwLω.1
    hwLω.2 fun q' hq' hc' hp' a b h1 h2 h3 h4 => (hsubω q' hq' hc' hp' a b h1 h2 h3 h4).2

end Attach

end InteractingSLE.Sec7.OuterGeom
