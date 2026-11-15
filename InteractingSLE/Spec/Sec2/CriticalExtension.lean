/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.TerminalCritical
import InteractingSLE.Frozen.Spec.AdaptedBefore

/-!
# The monotone force coordinates extended through the lifetime

Packet PROVE-SEC2-TERM2. In the critical case of Aux. lemma 3 (Specification pp. 27–28) Itô's
formula is applied to `F(Q)` up to a localization time that may equal the lifetime `ζ` itself, so
the process must be defined, adapted and continuous at `ζ` on the paths that stay bounded up to
`ζ`. The frozen evolution says nothing about its coordinates at times `t ≥ ζ`. This file builds
the extension from the monotone force coordinates alone:

* `lowerExtPath ζ₀ v d u = ⨅_{r ∈ ℚ, r ≤ u, r < ζ₀} v r` (with the default value `d` for the
  other rationals), for a nonincreasing coordinate `v ≤ d`; it equals `v u` for `u < ζ₀`
  (`lowerExtPath_eq_of_lt`), equals `inf_{t < T} v t = lim_{t ↑ T} v t` for `T = ζ₀ ≤ u`
  (`lowerExtPath_eq_sInf`), and is continuous on `[0, T]` when `v` is bounded below
  (`continuousOn_lowerExtPath_Icc`);
* `upperExtPath`, the mirror image for nondecreasing coordinates;
* `lowerExt`, `upperExt`: the same at the level of processes; they are adapted for every time
  (`measurable_lowerExt`, `measurable_upperExt`) as soon as the coordinate is adapted before `ζ`
  (the frozen `AdaptedBefore`).

Only countably many rational times enter, so no path regularity is needed for measurability.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

/-- The rational time `r` as an element of `ℝ≥0` (`0` for negative `r`). -/
def ratTime (r : ℚ) : ℝ≥0 := (r : ℝ).toNNReal

theorem coe_ratTime_of_nonneg {r : ℚ} (hr : (0 : ℝ) ≤ r) : (ratTime r : ℝ) = r :=
  Real.coe_toNNReal _ hr

theorem ratTime_zero : ratTime 0 = 0 := by simp [ratTime]

/-- Between two times `t < T` of `ℝ≥0` there is a rational time. -/
theorem exists_ratTime_btwn {t T : ℝ≥0} (h : t < T) : ∃ r : ℚ, t < ratTime r ∧ ratTime r < T := by
  obtain ⟨r, h1, h2⟩ := exists_rat_btwn (show (t : ℝ) < T from h)
  have hr : (0 : ℝ) ≤ r := (NNReal.coe_nonneg t).trans h1.le
  refine ⟨r, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, coe_ratTime_of_nonneg hr]; exact h1
  · rw [← NNReal.coe_lt_coe, coe_ratTime_of_nonneg hr]; exact h2

/-- `{t : t < ζ₀}` is open in `ℝ≥0`. -/
theorem isOpen_setOf_coe_lt (ζ₀ : ℝ≥0∞) : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ₀} :=
  isOpen_lt ENNReal.continuous_coe continuous_const

/-! ### The path-level extension -/

/-- The lower extension of a path `v` (a nonincreasing force coordinate, bounded by `d`) through
the lifetime `ζ₀`: the infimum of `v r` over rational `r ≤ u` with `r < ζ₀`. -/
def lowerExtPath (ζ₀ : ℝ≥0∞) (v : ℝ≥0 → ℝ) (d : ℝ) (u : ℝ≥0) : ℝ :=
  ⨅ r : ℚ, if ratTime r ≤ u ∧ (ratTime r : ℝ≥0∞) < ζ₀ then v (ratTime r) else d

/-- The upper extension of a nondecreasing path `v ≥ d`. -/
def upperExtPath (ζ₀ : ℝ≥0∞) (v : ℝ≥0 → ℝ) (d : ℝ) (u : ℝ≥0) : ℝ :=
  -lowerExtPath ζ₀ (fun t => -v t) (-d) u

section Lower

variable {ζ₀ : ℝ≥0∞} {v : ℝ≥0 → ℝ} {d : ℝ}

/-- Before the lifetime the lower extension is the path itself. -/
theorem lowerExtPath_eq_of_lt (hanti : AntitoneOn v {t | (t : ℝ≥0∞) < ζ₀})
    (hcont : ContinuousOn v {t | (t : ℝ≥0∞) < ζ₀})
    (hd : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ → v t ≤ d) {u : ℝ≥0} (hu : (u : ℝ≥0∞) < ζ₀) :
    lowerExtPath ζ₀ v d u = v u := by
  set F : ℚ → ℝ := fun r => if ratTime r ≤ u ∧ (ratTime r : ℝ≥0∞) < ζ₀ then v (ratTime r) else d
    with hF
  have hlow : ∀ r : ℚ, v u ≤ F r := by
    intro r
    simp only [hF]
    split_ifs with h
    · exact hanti h.2 hu h.1
    · exact hd u hu
  have hbdd : BddBelow (range F) := ⟨v u, by rintro _ ⟨r, rfl⟩; exact hlow r⟩
  have hval : ∀ r : ℚ, ratTime r ≤ u → F r = v (ratTime r) := fun r hr => by
    simp only [hF]
    rw [ite_eq_left ⟨hr, lt_of_le_of_lt (by exact_mod_cast hr) hu⟩]
  refine le_antisymm ?_ (le_ciInf hlow)
  change iInf F ≤ v u
  rcases eq_or_ne u 0 with rfl | hu0
  · have := ciInf_le hbdd 0
    rw [hval 0 (by rw [ratTime_zero]), ratTime_zero] at this
    exact this
  · refine le_of_forall_pos_lt_add fun η hη => ?_
    have hca : ContinuousAt v u := hcont.continuousAt ((isOpen_setOf_coe_lt ζ₀).mem_nhds hu)
    obtain ⟨δ, hδ, hδv⟩ := Metric.continuousAt_iff.1 hca η hη
    have hlt : max 0 ((u : ℝ) - δ) < u :=
      max_lt (lt_of_le_of_ne (NNReal.coe_nonneg u) (by exact_mod_cast hu0.symm)) (by linarith)
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt
    have hr0 : (0 : ℝ) ≤ r := (le_max_left _ _).trans hr1.le
    have hru : ratTime r ≤ u := by
      rw [← NNReal.coe_le_coe, coe_ratTime_of_nonneg hr0]; exact hr2.le
    have hdist : dist (ratTime r) u < δ := by
      rw [NNReal.dist_eq, coe_ratTime_of_nonneg hr0, abs_sub_lt_iff]
      constructor <;> linarith [le_max_right 0 ((u : ℝ) - δ)]
    have h1 := hδv hdist
    rw [Real.dist_eq, abs_sub_lt_iff] at h1
    calc iInf F ≤ F r := ciInf_le hbdd r
      _ = v (ratTime r) := hval r hru
      _ < v u + η := by linarith [h1.1]

/-- After a finite positive lifetime `T` the lower extension is `inf_{t < T} v t`. -/
theorem lowerExtPath_eq_sInf {T : ℝ≥0} (hT : 0 < T) (hanti : AntitoneOn v (Iio T))
    (hd : ∀ t : ℝ≥0, t < T → v t ≤ d) (hbdd : BddBelow (v '' Iio T)) {u : ℝ≥0} (hu : T ≤ u) :
    lowerExtPath T v d u = sInf (v '' Iio T) := by
  set F : ℚ → ℝ := fun r => if ratTime r ≤ u ∧ (ratTime r : ℝ≥0∞) < (T : ℝ≥0∞) then v (ratTime r)
    else d with hF
  have hlow : ∀ r : ℚ, sInf (v '' Iio T) ≤ F r := by
    intro r
    simp only [hF]
    split_ifs with h
    · exact csInf_le hbdd ⟨ratTime r, ENNReal.coe_lt_coe.1 h.2, rfl⟩
    · exact (csInf_le hbdd ⟨0, hT, rfl⟩).trans (hd 0 hT)
  have hbddF : BddBelow (range F) := ⟨_, by rintro _ ⟨r, rfl⟩; exact hlow r⟩
  refine le_antisymm ?_ (le_ciInf hlow)
  refine le_csInf ⟨v 0, 0, hT, rfl⟩ ?_
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨r, hr1, hr2⟩ := exists_ratTime_btwn (show t < T from ht)
  have hFr : F r = v (ratTime r) := by
    simp only [hF]
    rw [ite_eq_left ⟨hr2.le.trans hu, ENNReal.coe_lt_coe.2 hr2⟩]
  calc iInf F ≤ F r := ciInf_le hbddF r
    _ = v (ratTime r) := hFr
    _ ≤ v t := hanti ht hr2 hr1.le

/-- The lower extension is continuous on `[0, T]` at a finite positive lifetime `T`, when `v` is
bounded below before `T`. -/
theorem continuousOn_lowerExtPath_Icc {T : ℝ≥0} (hT : 0 < T) (hanti : AntitoneOn v (Iio T))
    (hcont : ContinuousOn v (Iio T)) (hd : ∀ t : ℝ≥0, t < T → v t ≤ d)
    (hbdd : BddBelow (v '' Iio T)) : ContinuousOn (lowerExtPath T v d) (Icc 0 T) := by
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) < (T : ℝ≥0∞)} = Iio T := setOf_lt_coe_eq_Iio T
  have heq : ∀ t : ℝ≥0, t < T → lowerExtPath T v d t = v t := fun t ht =>
    lowerExtPath_eq_of_lt (by rwa [hset]) (by rwa [hset]) (fun s hs => hd s (by exact_mod_cast hs)) (by exact_mod_cast ht)
  intro x hx
  rcases lt_or_eq_of_le hx.2 with hxT | rfl
  · have hca : ContinuousAt v x := hcont.continuousAt (Iio_mem_nhds hxT)
    refine (hca.congr ?_).continuousWithinAt
    filter_upwards [Iio_mem_nhds hxT] with t ht using (heq t ht).symm
  · have hlim : Tendsto v (𝓝[<] x) (𝓝 (sInf (v '' Iio x))) := hanti.tendsto_nhdsLT hbdd
    rw [← lowerExtPath_eq_sInf hT hanti hd hbdd le_rfl] at hlim
    have hW : ContinuousWithinAt (lowerExtPath x v d) (Iio x) x :=
      hlim.congr' (eventually_nhdsWithin_of_forall fun t ht => (heq t ht).symm)
    exact (continuousWithinAt_Iio_iff_Iic.1 hW).mono fun t ht => ht.2

/-- Before the lifetime, the lower extension is continuous. -/
theorem continuousOn_lowerExtPath_lt (hanti : AntitoneOn v {t | (t : ℝ≥0∞) < ζ₀})
    (hcont : ContinuousOn v {t | (t : ℝ≥0∞) < ζ₀})
    (hd : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ → v t ≤ d) :
    ContinuousOn (lowerExtPath ζ₀ v d) {t | (t : ℝ≥0∞) < ζ₀} :=
  hcont.congr fun _ ht => lowerExtPath_eq_of_lt hanti hcont hd ht

end Lower

section Upper

variable {ζ₀ : ℝ≥0∞} {v : ℝ≥0 → ℝ} {d : ℝ}

theorem upperExtPath_eq_of_lt (hmono : MonotoneOn v {t | (t : ℝ≥0∞) < ζ₀})
    (hcont : ContinuousOn v {t | (t : ℝ≥0∞) < ζ₀})
    (hd : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ → d ≤ v t) {u : ℝ≥0} (hu : (u : ℝ≥0∞) < ζ₀) :
    upperExtPath ζ₀ v d u = v u := by
  unfold upperExtPath
  rw [lowerExtPath_eq_of_lt (v := fun t => -v t) (fun _ ha _ hb hab => neg_le_neg (hmono ha hb hab))
    hcont.neg (fun t ht => neg_le_neg (hd t ht)) hu, neg_neg]

theorem continuousOn_upperExtPath_Icc {T : ℝ≥0} (hT : 0 < T) (hmono : MonotoneOn v (Iio T))
    (hcont : ContinuousOn v (Iio T)) (hd : ∀ t : ℝ≥0, t < T → d ≤ v t)
    (hbdd : BddAbove (v '' Iio T)) : ContinuousOn (upperExtPath T v d) (Icc 0 T) := by
  have hbdd' : BddBelow ((fun t => -v t) '' Iio T) := by
    obtain ⟨M, hM⟩ := hbdd
    exact ⟨-M, by rintro _ ⟨t, ht, rfl⟩; exact neg_le_neg (hM ⟨t, ht, rfl⟩)⟩
  exact (continuousOn_lowerExtPath_Icc (v := fun t => -v t) hT
    (fun _ ha _ hb hab => neg_le_neg (hmono ha hb hab)) hcont.neg
    (fun t ht => neg_le_neg (hd t ht)) hbdd').neg

theorem continuousOn_upperExtPath_lt (hmono : MonotoneOn v {t | (t : ℝ≥0∞) < ζ₀})
    (hcont : ContinuousOn v {t | (t : ℝ≥0∞) < ζ₀})
    (hd : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ → d ≤ v t) :
    ContinuousOn (upperExtPath ζ₀ v d) {t | (t : ℝ≥0∞) < ζ₀} :=
  hcont.congr fun _ ht => upperExtPath_eq_of_lt hmono hcont hd ht

end Upper

/-! ### The process-level extension and its adaptedness -/

section Process

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞}
  {X : ℝ≥0 → Ω → ℝ}

/-- The lower extension of a process. -/
def lowerExt (ζ : Ω → ℝ≥0∞) (X : ℝ≥0 → Ω → ℝ) (d : ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  lowerExtPath (ζ ω) (fun t => X t ω) d u

/-- The upper extension of a process. -/
def upperExt (ζ : Ω → ℝ≥0∞) (X : ℝ≥0 → Ω → ℝ) (d : ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  upperExtPath (ζ ω) (fun t => X t ω) d u

/-- The process killed at `ζ` (value `d` from `ζ` on) is adapted. -/
theorem measurable_killed_of_adaptedBefore (hX : AdaptedBefore 𝓕 ζ X)
    (t : ℝ≥0) (d : ℝ) :
    Measurable[𝓕 t] fun ω => if (t : ℝ≥0∞) < ζ ω then X t ω else d := by
  intro A hA
  have h1 := hX t A hA
  have h2 : MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω} := by
    simpa using hX t univ MeasurableSet.univ
  by_cases hd : d ∈ A
  · convert h1.union h2.compl using 1
    ext ω
    by_cases h : (t : ℝ≥0∞) < ζ ω <;> simp [h, hd]
  · convert h1 using 1
    ext ω
    by_cases h : (t : ℝ≥0∞) < ζ ω <;> simp [h, hd]

theorem adaptedBefore_neg (hX : AdaptedBefore 𝓕 ζ X) :
    AdaptedBefore 𝓕 ζ (fun t ω => -X t ω) := by
  intro t A hA
  have := hX t (Neg.neg ⁻¹' A) (measurable_neg hA)
  simpa using this

/-- The lower extension is adapted (for every time, including times after `ζ`). -/
theorem measurable_lowerExt (hX : AdaptedBefore 𝓕 ζ X) (d : ℝ) (u : ℝ≥0) :
    Measurable[𝓕 u] (lowerExt ζ X d u) := by
  unfold lowerExt lowerExtPath
  refine Measurable.iInf fun r => ?_
  by_cases hr : ratTime r ≤ u
  · have hm := (measurable_killed_of_adaptedBefore hX (ratTime r) d).mono (𝓕.mono hr) le_rfl
    convert hm using 2 with ω
    simp only [hr, true_and]
  · simp only [hr, false_and, ite_false]
    exact measurable_const

theorem measurable_upperExt (hX : AdaptedBefore 𝓕 ζ X) (d : ℝ) (u : ℝ≥0) :
    Measurable[𝓕 u] (upperExt ζ X d u) :=
  (measurable_lowerExt (adaptedBefore_neg hX) (-d) u).neg

end Process

end Sec2

end InteractingSLE
