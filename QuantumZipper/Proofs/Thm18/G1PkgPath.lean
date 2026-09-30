import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.Compact

/-!
# G1 package: a measurable continuous regularization of paths

For the path-measurable selections of G1 (`G1PsiSelStmt`, G1RegRepRed.lean; trace part
`G1TraceSelStmt`, G1PkgSel.lean) the driving path lives in `ℝ≥0 → ℝ` with the product σ-algebra,
in which the set of continuous paths is not measurable. This file builds a map
`G1Pkg.pathReg : (ℝ≥0 → ℝ) → ℝ≥0 → ℝ` that

* is measurable (into the product σ-algebra): it only reads the path on a countable dense set;
* produces a continuous path for **every** input;
* is the identity on continuous paths.

Construction: fix a countable dense `S ⊆ ℝ≥0` and, for each `t`, a sequence `x t n ∈ S`
tending to `t`. A path is *good* if it is uniformly continuous on `S ∩ [0,N]` for every `N`
(a countable condition, hence measurable). For good `a`, `pathReg a t = lim_n a (x t n)`
(the continuous extension from `S`); otherwise `pathReg a = 0`.

Own elementary argument (standard: extension of a locally uniformly continuous function from a
dense set; cf. the version-construction in `CharFun.exists_good_version`).
-/

noncomputable section

open MeasureTheory Filter Set Function Topology
open scoped NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1Pkg

/-- A countable dense set of times. -/
def denseT : Set ℝ≥0 := (TopologicalSpace.exists_countable_dense ℝ≥0).choose

theorem denseT_countable : denseT.Countable :=
  (TopologicalSpace.exists_countable_dense ℝ≥0).choose_spec.1

theorem denseT_dense : Dense denseT :=
  (TopologicalSpace.exists_countable_dense ℝ≥0).choose_spec.2

/-- A sequence in `denseT` tending to `t`. -/
def apx (t : ℝ≥0) : ℕ → ℝ≥0 := (mem_closure_iff_seq_limit.1 (denseT_dense t)).choose

theorem apx_mem (t : ℝ≥0) (n : ℕ) : apx t n ∈ denseT :=
  (mem_closure_iff_seq_limit.1 (denseT_dense t)).choose_spec.1 n

theorem apx_tendsto (t : ℝ≥0) : Tendsto (apx t) atTop (𝓝 t) :=
  (mem_closure_iff_seq_limit.1 (denseT_dense t)).choose_spec.2

/-- Good paths: uniformly continuous on `denseT ∩ [0,N]` for every `N`. -/
def PathGood (a : ℝ≥0 → ℝ) : Prop :=
  ∀ N m : ℕ, ∃ k : ℕ, ∀ x ∈ denseT, ∀ y ∈ denseT, x ≤ N → y ≤ N →
    dist x y < 1 / ((k : ℝ) + 1) → |a x - a y| ≤ 1 / ((m : ℝ) + 1)

theorem measurableSet_pathGood : MeasurableSet {a : ℝ≥0 → ℝ | PathGood a} := by
  have hc : Countable denseT := denseT_countable.to_subtype
  have e : {a : ℝ≥0 → ℝ | PathGood a} = ⋂ N : ℕ, ⋂ m : ℕ, ⋃ k : ℕ, ⋂ x : denseT, ⋂ y : denseT,
      {a | (x : ℝ≥0) ≤ N → (y : ℝ≥0) ≤ N → dist (x : ℝ≥0) y < 1 / ((k : ℝ) + 1) →
        |a x - a y| ≤ 1 / ((m : ℝ) + 1)} := by
    ext a
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, PathGood, Subtype.forall]
  rw [e]
  refine MeasurableSet.iInter fun N => MeasurableSet.iInter fun m => MeasurableSet.iUnion
    fun k => MeasurableSet.iInter fun x => MeasurableSet.iInter fun y => ?_
  by_cases h : (x : ℝ≥0) ≤ N ∧ (y : ℝ≥0) ≤ N ∧ dist (x : ℝ≥0) y < 1 / ((k : ℝ) + 1)
  · have e2 : {a : ℝ≥0 → ℝ | (x : ℝ≥0) ≤ N → (y : ℝ≥0) ≤ N →
        dist (x : ℝ≥0) y < 1 / ((k : ℝ) + 1) → |a x - a y| ≤ 1 / ((m : ℝ) + 1)} =
        {a | |a x - a y| ≤ 1 / ((m : ℝ) + 1)} := by
      ext a; simp only [mem_ofPred_eq]; exact ⟨fun H => H h.1 h.2.1 h.2.2, fun H _ _ _ => H⟩
    rw [e2]
    have hm : Measurable fun a : ℝ≥0 → ℝ => |a x - a y| :=
      continuous_abs.measurable.comp ((measurable_pi_apply (x : ℝ≥0)).sub (measurable_pi_apply (y : ℝ≥0)))
    exact measurableSet_le hm measurable_const
  · have e2 : {a : ℝ≥0 → ℝ | (x : ℝ≥0) ≤ N → (y : ℝ≥0) ≤ N →
        dist (x : ℝ≥0) y < 1 / ((k : ℝ) + 1) → |a x - a y| ≤ 1 / ((m : ℝ) + 1)} = univ := by
      ext a; simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro h1 h2 h3; exact absurd ⟨h1, h2, h3⟩ h
    rw [e2]; exact MeasurableSet.univ

/-- The regularized path. -/
def pathReg (a : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  {a : ℝ≥0 → ℝ | PathGood a}.indicator (fun a => limUnder atTop fun n => a (apx t n)) a

theorem measurable_pathReg : Measurable pathReg := by
  refine measurable_pi_iff.2 fun t => ?_
  refine Measurable.indicator ?_ measurableSet_pathGood
  exact (StronglyMeasurable.limUnder fun n => (measurable_pi_apply (apx t n)).stronglyMeasurable
    ).measurable

/-- The key estimate: for a good path, along sequences in `denseT` inside `[0,N]` whose terms
are eventually `δ`-close, the values are eventually `ε`-close. -/
theorem PathGood.eventually_close {a : ℝ≥0 → ℝ} (ha : PathGood a) (N m : ℕ) :
    ∃ δ > (0 : ℝ), ∀ x ∈ denseT, ∀ y ∈ denseT, x ≤ N → y ≤ N → dist x y < δ →
      |a x - a y| ≤ 1 / ((m : ℝ) + 1) := by
  obtain ⟨k, hk⟩ := ha N m
  exact ⟨1 / ((k : ℝ) + 1), by positivity, hk⟩

/-- For a good path, `a` is Cauchy along every sequence in `denseT` converging in `ℝ≥0`. -/
theorem PathGood.cauchy {a : ℝ≥0 → ℝ} (ha : PathGood a) {t : ℝ≥0} {s : ℕ → ℝ≥0}
    (hs : ∀ n, s n ∈ denseT) (hst : Tendsto s atTop (𝓝 t)) :
    CauchySeq fun n => a (s n) := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := exists_nat_gt (t : ℝ)
  obtain ⟨δ, hδ, hclose⟩ := ha.eventually_close N m
  obtain ⟨n₁, hn₁⟩ := Metric.cauchySeq_iff.1 hst.cauchySeq δ hδ
  have hle : ∀ᶠ n in atTop, s n ≤ N := by
    have : Iio (N : ℝ≥0) ∈ 𝓝 t := Iio_mem_nhds (by exact_mod_cast hN)
    filter_upwards [hst this] with n hn using le_of_lt hn
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.1 hle
  refine ⟨max n₁ n₂, fun n hn => ?_⟩
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (hclose _ (hs n) _ (hs _) (hn₂ n (le_trans (le_max_right _ _) hn))
    (hn₂ _ (le_max_right _ _)) (hn₁ n (le_trans (le_max_left _ _) hn) _ (le_max_left _ _))) hm

/-- The continuous extension of a good path. -/
theorem PathGood.tendsto {a : ℝ≥0 → ℝ} (ha : PathGood a) (t : ℝ≥0) :
    Tendsto (fun n => a (apx t n)) atTop (𝓝 (limUnder atTop fun n => a (apx t n))) :=
  (ha.cauchy (apx_mem t) (apx_tendsto t)).tendsto_limUnder

theorem PathGood.continuous {a : ℝ≥0 → ℝ} (ha : PathGood a) :
    Continuous fun t => limUnder atTop fun n => a (apx t n) := by
  rw [Metric.continuous_iff]
  intro t ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((t : ℝ) + 1)
  obtain ⟨δ, hδ, hclose⟩ := ha.eventually_close N m
  refine ⟨min 1 δ, lt_min one_pos hδ, fun t' ht' => ?_⟩
  have h1 : dist t' t < 1 := lt_of_lt_of_le ht' (min_le_left _ _)
  have h2 : dist t' t < δ := lt_of_lt_of_le ht' (min_le_right _ _)
  have ht'N : (t' : ℝ) < N := by
    rw [NNReal.dist_eq] at h1
    have := (abs_lt.1 h1).2
    linarith
  have htN : (t : ℝ) < N := by linarith
  have hlt : ∀ u : ℝ≥0, (u : ℝ) < N → ∀ᶠ n in atTop, apx u n ≤ N := fun u hu => by
    have : Iio (N : ℝ≥0) ∈ 𝓝 u := Iio_mem_nhds (by exact_mod_cast hu)
    filter_upwards [apx_tendsto u this] with n hn using le_of_lt hn
  have hd : ∀ᶠ n in atTop, dist (apx t' n) (apx t n) < δ :=
    ((apx_tendsto t').dist (apx_tendsto t)).eventually (gt_mem_nhds h2)
  have hev : ∀ᶠ n in atTop, |a (apx t' n) - a (apx t n)| ≤ 1 / ((m : ℝ) + 1) := by
    filter_upwards [hlt t' ht'N, hlt t htN, hd] with n h1n h2n h3n
    exact hclose _ (apx_mem t' n) _ (apx_mem t n) h1n h2n h3n
  have hle := le_of_tendsto (((ha.tendsto t').sub (ha.tendsto t)).abs) hev
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hle hm

/-- Continuous paths are good. -/
theorem pathGood_of_continuous {a : ℝ≥0 → ℝ} (ha : Continuous a) : PathGood a := by
  intro N m
  have hu : UniformContinuousOn a (Icc 0 (N : ℝ≥0)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous ha.continuousOn
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1 hu (1 / ((m : ℝ) + 1)) (by positivity)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  refine ⟨k, fun x _ y _ hx hy hxy => ?_⟩
  have := hδu x ⟨by positivity, hx⟩ y ⟨by positivity, hy⟩ (lt_trans hxy hk)
  rw [Real.dist_eq] at this
  exact this.le

theorem pathReg_of_good {a : ℝ≥0 → ℝ} (ha : PathGood a) :
    pathReg a = fun t => limUnder atTop fun n => a (apx t n) := by
  funext t
  exact indicator_of_mem (show a ∈ {a : ℝ≥0 → ℝ | PathGood a} from ha) _

/-- **The regularization of paths**: measurable, continuous for every path, and the identity on
continuous paths. -/
theorem pathReg_spec : Measurable pathReg ∧ (∀ a, Continuous (pathReg a)) ∧
    ∀ a, Continuous a → pathReg a = a := by
  refine ⟨measurable_pathReg, fun a => ?_, fun a ha => ?_⟩
  · by_cases hg : PathGood a
    · rw [pathReg_of_good hg]; exact hg.continuous
    · have : pathReg a = fun _ => 0 := funext fun t =>
        indicator_of_notMem (show a ∉ {a : ℝ≥0 → ℝ | PathGood a} from hg) _
      rw [this]; exact continuous_const
  · rw [pathReg_of_good (pathGood_of_continuous ha)]
    funext t
    exact ((ha.tendsto t).comp (apx_tendsto t)).limUnder_eq

end G1Pkg
end Thm18Asm
end QuantumZipper
