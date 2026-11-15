/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWSourceInputs
import InteractingSLE.Spec.Sec5.Aux61SlitWRestartFields
import InteractingSLE.Spec.Sec5.Aux61SlitWRetainedFields
import InteractingSLE.Spec.Sec5.Aux61RestartMarkHit

/-! # Physical input fields on the actual source probability space -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW.SourceSetting
open Aux61FibData Aux61GInst Aux61Restart LawUnique GlueCond
open WangWu Cond44Ref CrossCond.Theta CrossCond.Word49
universe u
variable (S : SourceSetting.{u})

/-- The actual glued counterflow record has the good hitting certificate,
without any restart, wiring or record-reading assumption. -/
theorem counterflow_good : ∀ᵐ p ∂S.μ, p.2 ∈ goodHitSet := by
  rw [S.theta_measure]
  exact cfGlueAE_mem_goodHitSetT S.θ S.κ S.κ_pos S.κ_lt_four S.xL S.xR S.ρL S.ρR
    (Theorem15.isOrderedForceWord_flowLine (Sec7.prop74Data S.a S.b) {0} 0)
    S.cond44 S.theta_bounds S.P S.own.filt S.own.W S.own.VL S.own.VR S.own.noise S.life S.ownField
    S.own.coupling S.P₂ S.field₂ S.W₂ S.life₂ S.counterflow S.theta_field_law S.kernel S.kernel_law

/-- At every retained time the physical counterflow hull is the R1 history
hull and protects the original target. Its topology is supplied by R1. -/
theorem counterflow_retained_geometry : ∀ᵐ p ∂S.μ, ∀ s : ℝ≥0,
    cfHullQ s p.2 = historyHull s (fun p : S.Ω × HistorySpace 0 0 => p.2) p ∧
    IsOpen (H \ cfHullQ s p.2) ∧
    (∀ z ∈ LocalSets.lowerUnion (cfHullQ s p.2),
      ¬ Bornology.IsBounded (connectedComponentIn (LocalSets.lowerUnion (cfHullQ s p.2)) z)) ∧
    (1 : ℂ) ∉ closure (cfHullQ s p.2) := by
  filter_upwards [S.counterflow_good] with p hp s
  have heq : cfHullQ s p.2 = historyHull s (fun p : S.Ω × HistorySpace 0 0 => p.2) p := by
    change cfHullQ s p.2 = negInv '' QuantumZipper.fwdHull (cfDrv0 s p.2) s
    rw [cfHullQ_eq_of_mem_goodCfSet hp.1, fwdHull_cfDrv0 hp.1 s]
  rw [heq]
  exact ⟨rfl, (historyHull_properties s (fun p : S.Ω × HistorySpace 0 0 => p.2) p).1,
    (historyHull_properties s (fun p : S.Ω × HistorySpace 0 0 => p.2) p).2,
    original_target_protected_of_goodHit hp s⟩

variable (F : SourceRestartData S.Ω S.nL S.nR)

/-- The injectivity input of the actual source follows almost surely from
the positive-time version identity and continuity of the chosen restart. -/
theorem ae_injective_restart
    (hs : ∀ i, IsRestartSpec (F.event i)
      (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i) (F.path i) (F.contact i))
    (hv : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → ∀ u : ℝ≥0, 0 < u →
      (u : ℝ≥0∞) < F.contact i p → F.path i p u = S.path p.1 (F.start i + u)) :
    ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → InjOn (F.path i p) {u | (u : ℝ≥0∞) < F.contact i p} := by
  intro i
  filter_upwards [S.physical_path, hv i] with p hp hvp he
  apply injOn_restart_of_pos_version ((hs i).contρ p he) hp.2.2.cont hp.2.2.inj
  intro u hu huT
  simpa only [← NNReal.coe_add, Real.toNNReal_coe] using hvp he u hu huT

/-- The original-target obstruction is discharged for every actual finite
positive source contact, using the same pre-contact path version. -/
theorem ae_contact_ne_target
    (hs : ∀ i, IsRestartSpec (F.event i)
      (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i) (F.path i) (F.contact i))
    (hv : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → ∀ u : ℝ≥0, 0 < u →
      (u : ℝ≥0∞) < F.contact i p → F.path i p u = S.path p.1 (F.start i + u)) :
    ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → 0 < F.contact i p → F.contact i p < ⊤ →
      F.path i p (F.contact i p).toNNReal ≠ 1 := by
  intro i
  filter_upwards [S.physical_path, hv i] with p hp hvp he hpos hfin
  apply restart_contact_ne_target ((hs i).contρ p he) hp.2.2 hpos hfin
  intro u hu huT
  simpa only [← NNReal.coe_add, Real.toNNReal_coe] using hvp he u hu huT

/-- The `chart_geometry` field of `Inputs` from the actual retained
component and the normalized R1 output. Counterflow topology/protection,
simple connectivity, target collar and current collar are all discharged. -/
theorem ae_chart_geometry_of_retained
    (hs : ∀ i, IsRestartSpec (F.event i)
      (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i) (F.path i) (F.contact i))
    (hr : ∀ i, 0 < F.start i)
    (hpos : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → 0 < F.contact i p)
    (hv : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → ∀ u : ℝ≥0, 0 < u →
      (u : ℝ≥0∞) < F.contact i p → F.path i p u = S.path p.1 (F.start i + u))
    (hdom : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → ∃ b : ℂ,
      ((sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ) =
        restartComponent (cfHullQ (rationalTime S.s) p.2) (fun t : ℝ => S.path p.1 t.toNNReal) (F.start i) b)
    (hmark : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → (1 : ℂ) ∈
      closure ((sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ))
    (hclear : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i →
      0 < infDist (S.path p.1 (F.start i)) (cfHullQ (rationalTime S.s) p.2))
    (hinfty : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → Tendsto
      (fun z : ℂ => ‖(sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).1 (z + 1)‖)
        (𝓝[H] 0) atTop)
    (hlift : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → ∀ z ∈
      ((sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ),
      (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).2.2 z =
        (physicalRestartLog (stripTargetHull
          (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom) z).im)
    (hcurrent : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → Tendsto
      (fun z => (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).1
        (QuantumZipper.fwdMapInv (fun t : ℝ => S.own.W t.toNNReal p.1) (F.start i) z))
      (𝓝[H] 0) (𝓝 0)) :
    ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (cfHullQ (rationalTime S.s) p.2) (F.start i)
        (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p) := by
  intro i
  filter_upwards [S.physical_path, S.counterflow_retained_geometry, hpos i, hv i, hdom i,
    hmark i, hclear i, hinfty i, hlift i, hcurrent i]
    with p hp hcf hT hvp hd hm hcl hi hl hcu he
  obtain ⟨b, hbdom⟩ := hd he
  have hb : b ∈ retainedDomain (cfHullQ (rationalTime S.s) p.2)
      (fun t : ℝ => S.path p.1 t.toNNReal) (F.start i) := by
    apply connectedComponentIn_nonempty_iff.1
    change (restartComponent (cfHullQ (rationalTime S.s) p.2)
      (fun t : ℝ => S.path p.1 t.toNNReal) (F.start i) b).Nonempty
    rw [← hbdom]
    exact Set.Nonempty.of_closure ⟨1, hm he⟩
  have hver : ∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < F.contact i p →
      F.path i p u = (fun t : ℝ => S.path p.1 t.toNNReal) (F.start i + (u : ℝ)) := by
    intro u hu huT
    simpa only [← NNReal.coe_add, Real.toNNReal_coe] using hvp he u hu huT
  have hnew := exists_fresh_segment_of_restart (hs i) he (hT he)
    (η := fun t : ℝ => S.path p.1 t.toNNReal) (r := F.start i) hver
  apply sourceChartGeometry_of_retained hp.1.continuous_rpath
    (by simpa only [Ito.rpath, Real.toNNReal_zero] using hp.1.2.1) hp.2.1 hp.2.2 (hr i)
    (hcf (rationalTime S.s)).2.1 (hcf (rationalTime S.s)).2.2.1 hb hbdom
    (hcf (rationalTime S.s)).2.2.2 (hm he) _ hnew (hi he) (hl he) (hcu he)
  simpa only [Real.toNNReal_coe] using hcl he

/-- Both lift fields on the source law follow from the proved chart
geometry, before any full `Inputs` object or wiring is available. -/
theorem ae_lift_fields
    (hg : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (cfHullQ (rationalTime S.s) p.2) (F.start i)
        (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)) :
    ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i →
      ContinuousOn (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).2.2
        (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom ∧
      InnerProductSpace.HarmonicOnNhd (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).2.2
        (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom := by
  intro i
  filter_upwards [hg i] with p hp he
  exact ⟨(hp he).continuous_lift, (hp he).harmonic_lift⟩

end InteractingSLE.Sec5.Aux61SlitW.SourceSetting
