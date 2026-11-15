/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWSourceInputs

/-! # Physical containment and comparison cover of the concrete source family -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW.SourceSetting
open Aux61Marks Aux61Asm Aux61ChLoc Aux61ULoc Aux61FibData Aux61GInst LawUnique GlueCond
open WangWu Cond44Ref CrossCond.Theta Coupling
universe u
variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR) (I : S.Inputs F)
include I

/-- The causal rule is the physical selected-access code time, including zero. -/
theorem ruleTime_eq (i : F.ι) : ∀ᵐ p ∂S.μ, ∀ q : ℝ≥0,
    (q : ℝ≥0∞) < ((S.marksData F).code i p).life →
    capacityRule (F.chart i) (F.start i) q
      (stopRec (rationalTime S.s) p.2, killedHistory S.own.W S.own.VL S.own.VR S.life p.1) =
      ((F.start i + accessTime (E := F.event i)
        (c := sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        (ρ := F.path i) (T := F.contact i) (V := (F.data i).V) p q : ℝ≥0) : ℝ≥0∞) := by
  filter_upwards [S.restart_read F I i] with p hr q hq
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
    rw [capacityRule_zero, accessTime_zero (I.restart.spec i) (I.restart.open_window i)
      (I.restart.zero_window i) (I.restart.landing i) (I.restart.injective_path i) hq, add_zero]
  · exact capacityRule_eq_accessTime (I.restart.spec i) (I.restart.open_window i)
      (I.restart.zero_window i) (I.restart.landing i) (I.restart.injective_path i)
      (c := F.chart i) (r := F.start i) (a := 0) (k := chiC S.κ) (h := fun p => S.ownField p.1)
      rfl hread (pos_iff_ne_zero.2 hq0) hq

/-- The source marked set contains the actual physical union at its own
causal stop. Off the live event the constructed set is all of `H`. -/
theorem physical_contains (i : F.ι) (q : ℝ≥0) : ∀ᵐ p ∂S.μ,
    unionAt (fun p => cfHullQ (rationalTime S.s) p.2)
      (fun t p => fwdHull (fun v : ℝ => S.own.W v.toNNReal p.1) t)
      (fun p => capacityRule (F.chart i) (F.start i) q
        (stopRec (rationalTime S.s) p.2, killedHistory S.own.W S.own.VL S.own.VR S.life p.1)) p ⊆
      (S.marksData F).baseSets i q p := by
  filter_upwards [S.physical_path, I.chart_geometry i, I.path_version i, S.restart_read F I i]
    with p hp hg hv hr
  by_cases he : p ∈ liveEv ((S.marksData F).Z i) ((S.marksData F).B i) ((S.marksData F).code i) q
  · have hx := mem_exitEv_of_lt_accessLife he.2
    have hbefore : ∀ u : ℝ≥0,
        u < exitNN (F.event i) (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
          (F.path i) (F.contact i) (F.data i).V p → (u : ℝ≥0∞) < F.contact i p :=
      fun u hu => (ENNReal.coe_lt_coe.2 hu).trans_le
        (IsRestartSpec.coe_exitNN hx ▸ IsRestartSpec.exitTime_le p)
    exact source_union_subset F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life S.κ S.ownField
      I.restart hp.2.1 hp.2.2 (hg hx.1.1)
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

/-- The same containment in the regularized hull convention used by UNIONLOC. -/
theorem regular_contains (i : F.ι) (q : ℝ≥0) : ∀ᵐ p ∂S.μ,
    unionAt (fun p => cfHullQ (rationalTime S.s) p.2)
      (fun t p => Sec7.PocketStopWallsFin.regHull S.own.W S.life t p.1)
      (fun p => capacityRule (F.chart i) (F.start i) q
        (stopRec (rationalTime S.s) p.2, killedHistory S.own.W S.own.VL S.own.VR S.life p.1)) p ⊆
      (S.marksData F).baseSets i q p := by
  have hreg := ae_glue_fst (μ := S.P) S.kernel S.measCounterField
    (Sec7.PocketStopWallsFin.ae_regHull_eq S.own.coupling S.own_infinite)
  filter_upwards [S.physical_contains F I i q, hreg] with p hp hr
  simpa only [unionAt, hr] using hp

/-- Every rational comparison time strictly before the physical code stop
belongs to the explicit, recorded comparison event. -/
theorem comparison_cover : let D := S.marksData F;
    ∀ i (q : ℝ≥0), 0 < q → ∀ᵐ p ∂S.μ, D.Z i p ∈ D.B i → (q : ℝ≥0∞) < (D.code i p).life →
      ∀ j, D.time j i q p < D.start i q p + D.duration i q p → p ∈ D.comparisonEvent j i q := by
  intro D i q _
  filter_upwards [S.ruleTime_eq F I i] with p ht hB hq j hj
  refine ⟨⟨hB, lt_of_le_of_lt (by simp only [ENNReal.coe_zero, zero_le]) hq⟩, ?_⟩
  change (rationalTime j : ℝ≥0∞) ≤ capacityRule (F.chart i) (F.start i) q
    (stopRec (rationalTime S.s) p.2, killedHistory S.own.W S.own.VL S.own.VR S.life p.1)
  rw [ht q hq]
  apply ENNReal.coe_le_coe.2
  exact NNReal.coe_le_coe.1 hj.le

end InteractingSLE.Sec5.Aux61SlitW.SourceSetting
