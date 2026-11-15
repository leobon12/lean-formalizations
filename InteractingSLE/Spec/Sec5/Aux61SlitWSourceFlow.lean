/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWSourceSetting

/-! # Physical flow and geometric force coordinates in the source setting -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.Aux61SlitW
open Aux61Marks WangWu Cond44Ref LawUnique GlueCond CrossCond.Theta Coupling

/-- On an infinite integrated path, the physical force coordinates equal
the geometric images at every finite time. -/
theorem integrated_force_eq_geom {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w b : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ⊤) (hw : Continuous (Ito.rpath w)) (t : ℝ≥0) :
    (∀ i, vL i t - w t = Restart.FlowStopIdentCMI.geomL (Ito.rpath w) t (xL i)) ∧
    (∀ i, vR i t - w t = Restart.FlowStopIdentCMI.geomR (Ito.rpath w) t (xR i)) := by
  have hfr : ∀ r ∈ Icc (0 : ℝ) t, frozenDrive w t r = Ito.rpath w r :=
    fun r hr => frozenDrive_eq hr
  constructor
  · intro i
    have he := Sec7.SideHeight.vL_eq_neg_rightImg_frozenDrive hp (t₂ := t)
      ENNReal.ofReal_lt_top le_rfl i
    have hg := Supp8.GB6.rightImg_congr hw.neg t.coe_nonneg (x := -xL i)
      (fun r hr => congrArg Neg.neg (hfr r hr))
    rw [he, hg, Restart.FlowStopIdentCMI.geomL]
    simp only [Ito.rpath, Real.toNNReal_coe]
    rfl
  · intro i
    have he := Sec7.SideHeight.vR_eq_rightImg_frozenDrive hp (t₂ := t)
      ENNReal.ofReal_lt_top le_rfl i
    have hg := Supp8.GB6.rightImg_congr hw t.coe_nonneg (x := xR i) hfr
    rw [he, hg, Restart.FlowStopIdentCMI.geomR]
    simp only [Ito.rpath, Real.toNNReal_coe]

namespace SourceSetting
universe u
variable (S : SourceSetting.{u})

theorem cond44 : Sec4.Cond44 S.κ S.ρL S.ρR := by
  apply Sec7.Lemma71H.cond44_flowLine_prop74Data (θ := S.θ₂) S.κ_pos S.bound_left
  have hχ := Sec4.chiC_pos S.κ_pos S.κ_lt_four
  have hangle := mul_le_mul_of_nonneg_right S.angle_lt.le hχ.le
  linarith only [S.bound_right, hangle]

theorem admissible : Sec4.HasAdmissiblePartialSums S.κ S.ρL S.ρR S.xL S.xR :=
  Sec4.hasAdmissiblePartialSums_of_cond44 S.κ_lt_four
    (Theorem15.isOrderedForceWord_flowLine (Sec7.prop74Data S.a S.b) {0} 0) S.cond44

theorem own_infinite : ∀ᵐ ω ∂S.P, S.life ω = ⊤ :=
  (ae_seedLine_of_admissible S.κ_pos S.κ_lt_four.le
    (Theorem15.isOrderedForceWord_flowLine (Sec7.prop74Data S.a S.b) {0} 0)
    S.admissible S.own.coupling.1).mono fun _ h => h.1

abbrev θ : ℝ := S.θ₂ - S.θ₁ + π / 2

theorem theta_bounds : CfThetaBounds S.κ S.θ S.ρL S.ρR S.xL S.xR := by
  apply Prop51G.cfThetaBounds_prop74 (θ₁ := S.θ₁) (θ₂ := S.θ₂) S.κ_pos S.bound_right
  have hχ := Sec4.chiC_pos S.κ_pos S.κ_lt_four
  have hangle := mul_le_mul_of_nonneg_right S.angle_lt.le hχ.le
  linarith only [S.bound_left, hangle]

theorem counterField_eq : S.counterField = fun ω => cfFieldT S.κ S.θ (S.ownField ω) := by
  funext ω
  exact Prop51G.cfField_flowField_eq_cfFieldT S.κ S.θ₁ S.θ₂ (S.field ω)

theorem theta_measure : S.μ = glueMeasure S.P S.kernel (fun ω => cfFieldT S.κ S.θ (S.ownField ω))
    ((measurable_cfFieldT S.κ S.θ).comp S.own.coupling.2.1) := by
  change glueMeasure S.P S.kernel S.counterField S.measCounterField = _
  congr 1
  exact S.counterField_eq

theorem theta_field_law : S.P.map (fun ω => cfFieldT S.κ S.θ (S.ownField ω)) = S.P₂.map S.field₂ := by
  rw [← S.counterField_eq]
  exact S.field_law

/-- All physical path facts needed by the slit construction come from the
given flow line and its chosen coupling, without Theorem 1.3. -/
theorem physical_path : ∀ᵐ p ∂S.μ,
    Aux50Hit.IsGoodPath S.own.W S.own.VL S.own.VR S.life p.1 ∧
    IsLoewnerTrace (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal) ∧
    IsProperArc (fun t : ℝ => S.path p.1 t.toNNReal) := by
  have hgood := ae_glue_fst (μ := S.P) S.kernel S.measCounterField
    (Aux50Hit.ae_isGoodPath S.own.coupling.1 S.own_infinite)
  have htrace := ae_glue_fst (μ := S.P) S.kernel S.measCounterField S.own.trace
  have harc := ae_glue_fst (μ := S.P) S.kernel S.measCounterField
    (ae_isProperArc_of_isFlowLine S.κ_pos S.κ_lt_four.le S.admissible S.flow)
  filter_upwards [hgood, htrace, harc] with p hp ht ha
  have he : (fun t => S.path p.1 t - ((0 : ℝ) : ℂ)) = S.path p.1 :=
    funext fun t => sub_zero _
  rw [he, hp.1] at ht
  exact ⟨hp, isLoewnerTrace_of_isGeneratingTrace ht, ha⟩

theorem physical_forces : ∀ᵐ p ∂S.μ, ∀ t : ℝ≥0,
    (∀ i, S.own.VL i t p.1 - S.own.W t p.1 =
      Restart.FlowStopIdentCMI.geomL (fun v : ℝ => S.own.W v.toNNReal p.1) t (S.xL i)) ∧
    (∀ i, S.own.VR i t p.1 - S.own.W t p.1 =
      Restart.FlowStopIdentCMI.geomR (fun v : ℝ => S.own.W v.toNNReal p.1) t (S.xR i)) := by
  have hpath := ae_glue_fst (μ := S.P) S.kernel S.measCounterField S.own.coupling.1.ae_isIntegratedSLEPath
  filter_upwards [hpath, S.physical_path] with p hp hg t
  rw [hg.1.1] at hp
  exact integrated_force_eq_geom hp hg.1.continuous_rpath t

end SourceSetting
end InteractingSLE.Sec5.Aux61SlitW
