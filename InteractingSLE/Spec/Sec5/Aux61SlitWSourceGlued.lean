/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWSourceAssemble
import InteractingSLE.Spec.Sec5.Aux61SlitWGeometry

/-! # The concrete physical source satisfies all positive-time slit facts -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H chiC fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW.SourceSetting
open Aux61Marks Aux61Asm Aux61ChLoc Aux61ULoc Aux61FibData Aux61GInst LawUnique GlueCond
open WangWu Cond44Ref CrossCond.Theta Coupling
universe u
variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR) (I : S.Inputs F)
include I

omit I in
/-- The force-word extension at a rational time has the geometric boundary
data required by the two physical sides of the slit. -/
theorem geometric_patch_mean : ∀ᵐ p ∂S.μ, ∀ j : ℚ,
    IsBoundedHarmonicExtension
      (forceBoundaryData S.κ S.ρL S.ρR
        (Restart.FlowStopIdentCMI.geomL (fun t : ℝ => S.own.W t.toNNReal p.1) (rationalTime j) ∘ S.xL)
        (Restart.FlowStopIdentCMI.geomR (fun t : ℝ => S.own.W t.toNNReal p.1) (rationalTime j) ∘ S.xR))
      (forceJumpSet
        (Restart.FlowStopIdentCMI.geomL (fun t : ℝ => S.own.W t.toNNReal p.1) (rationalTime j) ∘ S.xL)
        (Restart.FlowStopIdentCMI.geomR (fun t : ℝ => S.own.W t.toNNReal p.1) (rationalTime j) ∘ S.xR))
      (sourcePatchExtension S.own.W S.own.VL S.own.VR S.κ S.ρL S.ρR j p.1) := by
  filter_upwards [S.physical_forces] with p hp j
  have hL := funext (hp (rationalTime j)).1
  have hR := funext (hp (rationalTime j)).2
  change (fun i => S.own.VL i (rationalTime j) p.1 - S.own.W (rationalTime j) p.1) =
    Restart.FlowStopIdentCMI.geomL (fun t : ℝ => S.own.W t.toNNReal p.1) (rationalTime j) ∘ S.xL at hL
  change (fun i => S.own.VR i (rationalTime j) p.1 - S.own.W (rationalTime j) p.1) =
    Restart.FlowStopIdentCMI.geomR (fun t : ℝ => S.own.W t.toNNReal p.1) (rationalTime j) ∘ S.xR at hR
  rw [← hL, ← hR]
  exact Impl.isBoundedHarmonicExtension_forceExt S.κ (Ito.weightWord S.ρL S.ρR) _ _

/-- The actual selected-access code, physical trace and explicit comparison
means satisfy the positive-time clause of `MarksFacts`. -/
theorem gluedFacts : let D := S.marksData F;
    ∀ i (q : ℝ≥0), 0 < q → ∀ᵐ p ∂S.μ, D.Z i p ∈ D.B i → (q : ℝ≥0∞) < (D.code i p).life →
      GluedSlitFacts (D.data i).κ (D.code i p) q (D.physicalDriver i q p) (D.physicalPath i q p)
        (D.start i q p) (D.duration i q p) (D.chart i p) (D.domain i q p) (D.chartPath i q p) (D.chartLife i q p)
        (fun j => D.time j i q p) (fun j => D.patches j i q p) (D.baseSets i q p)
        (fun j => D.mean j i q p) (fun j => D.physicalMean j i q p) := by
  intro D i q hq0
  filter_upwards [S.physical_path, I.chart_geometry i, I.path_version i, S.geometric_patch_mean]
    with p hp hg hv hb hB hq
  have hx := mem_exitEv_of_lt_accessLife hq
  have hbefore : ∀ u : ℝ≥0,
      u < exitNN (F.event i) (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        (F.path i) (F.contact i) (F.data i).V p → (u : ℝ≥0∞) < F.contact i p :=
    fun u hu => (ENNReal.coe_lt_coe.2 hu).trans_le
      (IsRestartSpec.coe_exitNN hx ▸ IsRestartSpec.exitTime_le p)
  have hgl := source_isGluedSlit F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life S.κ S.ownField
    I.restart hq hq0 hp.1.continuous_rpath hp.1.2.1 hp.2.1 hp.2.2 (hg hx.1.1)
    (fun u hu hue => hv hx.1.1 u hu (hbefore u hue))
  have hgeo := sourceSets_geometry F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life S.κ S.ownField
    I.restart.spec i q p ⟨hB, hq⟩
  have hclosed := sourceSets_closed F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life S.κ S.ownField
    I.restart.spec i q p
  have hword := Theorem15.isOrderedForceWord_flowLine (Sec7.prop74Data S.a S.b) {0} 0
  have hf := gluedSlitFacts_of_bhe hgl hclosed.1 (inter_domain_subset_trace hgl hgeo)
    hword.2.1 hword.2.2.2 hb
  have hpatch : (fun j : ℚ => D.patches j i q p) =
      fun j => fwdHull (fun t : ℝ => S.own.W t.toNNReal p.1) (rationalTime j) := by
    funext j
    exact Aux50Hit.regHull_stopHistory_cstop hp.1 (rationalTime j)
  rw [← hpatch] at hf
  change GluedSlitFacts (F.data i).κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [I.restart.kappa i]
  exact hf

/-- All facts of the concrete source object, conditional only on the named
MARKS and restart/window/history inputs. -/
theorem marksFacts : MarksFacts S.μ (S.marksData F) :=
  source_marksFacts S.own.coupling S.κ_pos S.own_infinite S.theta_bounds
    S.counterflow S.theta_field_law S.kernel_law S.theta_measure F (rationalTime S.s)
    I.restart I.code_marks I.sets_marks (S.regular_contains F I) (S.gluedFacts F I)
    (S.comparison_cover F I) I.initial_data

end InteractingSLE.Sec5.Aux61SlitW.SourceSetting
