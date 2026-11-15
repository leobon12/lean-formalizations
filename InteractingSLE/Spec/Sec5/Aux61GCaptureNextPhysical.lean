/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWSourceGlued

/-! # Physical source facts independent of future capture

The landed physical containment proofs use only restart facts, source chart
geometry and the actual path version. This adapter exposes those precise
inputs, so neither history coverage nor all-index future completion is
needed to construct the marked source facts.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GCaptureNext
open Aux61SlitW Aux61SlitW.SourceSetting Aux61Marks Aux61Asm Aux61ChLoc Aux61ULoc Aux61FibData Aux61GInst LawUnique GlueCond
open WangWu Cond44Ref CrossCond.Theta Coupling
universe u
variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)
  (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life (μ := S.μ) S.κ)
  (hgeo : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i →
    SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
      (cfHullQ (rationalTime S.s) p.2) (F.start i)
      (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
  (hpath : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → ∀ v : ℝ≥0, 0 < v →
    (v : ℝ≥0∞) < F.contact i p → F.path i p v = S.path p.1 (F.start i + v))

include hpath in
/-- The canonical physical trace reads the original own killed history
before contact; no future-capture condition is used. -/
theorem restart_read (i : F.ι) : ∀ᵐ p ∂S.μ, p ∈ F.event i → ∀ v : ℝ≥0, 0 < v →
    (v : ℝ≥0∞) < F.contact i p → F.path i p v = Restart.FlowStopIdentG.histTrace 0
      (killedHistory S.own.W S.own.VL S.own.VR S.life p.1) (F.start i + v) := by
  have hr := ae_histTrace_killedHistory S.own.coupling.1 S.own.trace
    (glueMeasure_fst S.kernel S.measCounterField)
  filter_upwards [hpath i, hr, S.physical_path] with p hp hread hg he v hv ht
  rw [hp he v hv ht, hread _ (by rw [hg.1.1]; exact ENNReal.coe_lt_top)]

include hR hpath

/-- The causal rule is the physical selected-access code time, including zero. -/
theorem ruleTime_eq (i : F.ι) : ∀ᵐ p ∂S.μ, ∀ q : ℝ≥0,
    (q : ℝ≥0∞) < ((S.marksData F).code i p).life →
    capacityRule (F.chart i) (F.start i) q
      (stopRec (rationalTime S.s) p.2, killedHistory S.own.W S.own.VL S.own.VR S.life p.1) =
      ((F.start i + accessTime (E := F.event i)
        (c := sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        (ρ := F.path i) (T := F.contact i) (V := (F.data i).V) p q : ℝ≥0) : ℝ≥0∞) := by
  filter_upwards [restart_read S F hpath i] with p hr q hq
  have hx := mem_exitEv_of_lt_accessLife hq
  have hread : ∀ u : ℝ≥0, 0 < u →
      u < exitNN (F.event i) (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        (F.path i) (F.contact i) (F.data i).V p →
      F.path i p u = Restart.FlowStopIdentG.histTrace 0
        (killedHistory S.own.W S.own.VL S.own.VR S.life p.1) (F.start i + u) := by
    intro u hu hue
    exact hr hx.1.1 u hu ((ENNReal.coe_lt_coe.2 hue).trans_le
      (IsRestartSpec.coe_exitNN hx ▸ IsRestartSpec.exitTime_le p))
  by_cases hq0 : q = 0
  · subst q
    rw [capacityRule_zero, accessTime_zero (hR.spec i) (hR.open_window i)
      (hR.zero_window i) (hR.landing i) (hR.injective_path i) hq, add_zero]
  · exact capacityRule_eq_accessTime (hR.spec i) (hR.open_window i)
      (hR.zero_window i) (hR.landing i) (hR.injective_path i)
      (c := F.chart i) (r := F.start i) (a := 0) (k := chiC S.κ) (h := fun p => S.ownField p.1)
      rfl hread (pos_iff_ne_zero.2 hq0) hq

include hgeo in
/-- The source marked set contains the actual physical union at its own
causal stop. Off the live event the constructed set is all of `H`. -/
theorem physical_contains (i : F.ι) (q : ℝ≥0) : ∀ᵐ p ∂S.μ,
    unionAt (fun p => cfHullQ (rationalTime S.s) p.2)
      (fun t p => fwdHull (fun v : ℝ => S.own.W v.toNNReal p.1) t)
      (fun p => capacityRule (F.chart i) (F.start i) q
        (stopRec (rationalTime S.s) p.2, killedHistory S.own.W S.own.VL S.own.VR S.life p.1)) p ⊆
      (S.marksData F).baseSets i q p := by
  filter_upwards [S.physical_path, hgeo i, hpath i, restart_read S F hpath i]
    with p hp hg hv hr
  by_cases he : p ∈ liveEv ((S.marksData F).Z i) ((S.marksData F).B i) ((S.marksData F).code i) q
  · have hx := mem_exitEv_of_lt_accessLife he.2
    have hbefore : ∀ u : ℝ≥0,
        u < exitNN (F.event i) (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
          (F.path i) (F.contact i) (F.data i).V p → (u : ℝ≥0∞) < F.contact i p :=
      fun u hu => (ENNReal.coe_lt_coe.2 hu).trans_le
        (IsRestartSpec.coe_exitNN hx ▸ IsRestartSpec.exitTime_le p)
    exact source_union_subset F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life S.κ S.ownField
      hR hp.2.1 hp.2.2 (hg hx.1.1)
      (fun u hu hue => hr hx.1.1 u hu (hbefore u hue))
      (fun u hu hue => hv hx.1.1 u hu (hbefore u hue))
  · change _ ⊆ sourceSets F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life S.κ S.ownField i q p
    change p ∉ liveEv (sourceHistory F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
      (sourceHistoryEvent F i)
      (sourceCode F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life S.κ S.ownField i) q at he
    rw [sourceSets, liveSet_of_notMem he]
    by_cases hT : capacityRule (F.chart i) (F.start i) q
        (stopRec (rationalTime S.s) p.2, killedHistory S.own.W S.own.VL S.own.VR S.life p.1) < ⊤
    · simp only [unionAt, hT, ↓reduceIte]; exact inter_subset_left
    · simp only [unionAt, hT, ↓reduceIte, subset_refl]

include hgeo in
/-- The same containment in the regularized hull convention used by UNIONLOC. -/
theorem regular_contains (i : F.ι) (q : ℝ≥0) : ∀ᵐ p ∂S.μ,
    unionAt (fun p => cfHullQ (rationalTime S.s) p.2)
      (fun t p => Sec7.PocketStopWallsFin.regHull S.own.W S.life t p.1)
      (fun p => capacityRule (F.chart i) (F.start i) q
        (stopRec (rationalTime S.s) p.2, killedHistory S.own.W S.own.VL S.own.VR S.life p.1)) p ⊆
      (S.marksData F).baseSets i q p := by
  have hreg := ae_glue_fst (μ := S.P) S.kernel S.measCounterField
    (Sec7.PocketStopWallsFin.ae_regHull_eq S.own.coupling S.own_infinite)
  filter_upwards [physical_contains S F hR hgeo hpath i q, hreg] with p hp hr
  simpa only [unionAt, hr] using hp

/-- Every rational comparison time strictly before the physical code stop
belongs to the explicit, recorded comparison event. -/
theorem comparison_cover : let D := S.marksData F;
    ∀ i (q : ℝ≥0), 0 < q → ∀ᵐ p ∂S.μ, D.Z i p ∈ D.B i → (q : ℝ≥0∞) < (D.code i p).life →
      ∀ j, D.time j i q p < D.start i q p + D.duration i q p → p ∈ D.comparisonEvent j i q := by
  intro D i q _
  filter_upwards [ruleTime_eq S F hR hpath i] with p ht hB hq j hj
  refine ⟨⟨hB, lt_of_le_of_lt (by simp only [ENNReal.coe_zero, zero_le]) hq⟩, ?_⟩
  change (rationalTime j : ℝ≥0∞) ≤ capacityRule (F.chart i) (F.start i) q
    (stopRec (rationalTime S.s) p.2, killedHistory S.own.W S.own.VL S.own.VR S.life p.1)
  rw [ht q hq]
  apply ENNReal.coe_le_coe.2
  exact NNReal.coe_le_coe.1 hj.le

end InteractingSLE.Sec5.Aux61GCaptureNext
