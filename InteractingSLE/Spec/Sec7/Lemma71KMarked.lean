/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71JSpace
import InteractingSLE.Spec.Sec7.Lemma71FBdry
import InteractingSLE.WangWu.ChamberChart

/-!
# Lemma 7.1's pocket: the marked prime ends, measurably

Packet PROVE-LEMMA71K. Specification §7.1 (`source/spec/p193-240.md` L576–L606, pp. 223–225): "the pocket `C` … its two
marked boundary points `x₀` (the opening point, first common point of the flanks traced by the right flank) and `y₀`
(the closing point, possibly `∞`)". In the compactified (Cayley) picture of `WangWu.IsOrderedArcs.traverse_disc` the
pocket is the Jordan domain bounded by `α̃[a, b] ∪ β̃[j a, j b]` (`α̃ = toDisc α` the right-wall crosscut), with marked
points `α̃ a` (opening) and `α̃ b` (closing; `= 1`, the image of `∞`, when the pocket closes at `∞`).

This file makes these points **functions of the outer curves**, defined for every `ω`:

* `ratHits R U`: the rational wall times `s ∈ [0, 1]` with `α̃ s ∈ U`; `openTime`, `closeTime`: its infimum and supremum
  (with `1`, resp. `0`, added, so that they are defined for every configuration); both are measurable when the
  membership events are (`measurable_openTime`, `measurable_closeTime`);
* `mem_closure_cayley_image_iff`: `w ∈ closure (cayley '' C)` through a dense sequence, hence measurable events
  (`measurableSet_mem_closure_cayley_image`);
* `measurable_wallPt`: the wall crosscut at a measurable time is measurable;
* `exists_measurable_approach_cayley`: a measurable approach sequence of points of `C ω` whose Cayley images tend to a
  given measurable point of `closure (cayley '' C ω)`;
* `pocket_marked` (deterministic): for a component `C` between two ordered proper arcs, the wall times in
  `closure (cayley '' C)` form exactly the interval `[a, b]` of a contact gap; the frontier of `cayley '' C` is a
  Jordan curve containing the distinct marked points `α̃ a`, `α̃ b`;
* `openTime_eq`, `closeTime_eq`: on such a configuration the measurable times are `a` and `b`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex Bornology
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71K

open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)

/-! ### The Cayley map -/

theorem measurable_cayley : Measurable cayley := by
  unfold QuantumZipper.CA.cayley
  fun_prop

theorem continuousAt_cayley_of_mem_H {z : ℂ} (hz : z ∈ H) : ContinuousAt cayley z :=
  (QuantumZipper.CA.differentiableAt_cayley (Lemma71F.add_I_ne_zero_of_mem_H hz)).continuousAt

/-- **Closure of the Cayley image through a dense sequence.** For `C ⊆ ℍ` open and `e` dense, `w` lies in the closure
of `cayley '' C` iff for every `j` some `e k ∈ C` has `cayley (e k)` within `1/(j+1)` of `w`. -/
theorem mem_closure_cayley_image_iff {C : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H) {e : ℕ → ℂ} (he : DenseRange e)
    {w : ℂ} : w ∈ closure (cayley '' C) ↔ ∀ j : ℕ, ∃ k, e k ∈ C ∧ dist (cayley (e k)) w < 1 / ((j : ℝ) + 1) := by
  constructor
  · intro hw j
    have hr : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    obtain ⟨y, ⟨z, hz, rfl⟩, hy⟩ := Metric.mem_closure_iff.1 hw (1 / ((j : ℝ) + 1) / 2) (by positivity)
    have hc := continuousAt_cayley_of_mem_H (hCH hz)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (hc.preimage_mem_nhds (ball_mem_nhds (cayley z)
      (show (0 : ℝ) < 1 / ((j : ℝ) + 1) / 2 by positivity)))
    obtain ⟨k, hk⟩ := he.exists_mem_open (hCo.inter isOpen_ball) ⟨z, hz, mem_ball_self hδ⟩
    refine ⟨k, hk.1, ?_⟩
    have h1 : dist (cayley (e k)) (cayley z) < 1 / ((j : ℝ) + 1) / 2 := hball hk.2
    calc dist (cayley (e k)) w ≤ dist (cayley (e k)) (cayley z) + dist (cayley z) w := dist_triangle _ _ _
      _ = dist (cayley (e k)) (cayley z) + dist w (cayley z) := by rw [dist_comm (cayley z) w]
      _ < 1 / ((j : ℝ) + 1) / 2 + 1 / ((j : ℝ) + 1) / 2 := add_lt_add h1 hy
      _ = 1 / ((j : ℝ) + 1) := by ring
  · intro hw
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
    obtain ⟨k, hk, hkd⟩ := hw j
    exact ⟨cayley (e k), mem_image_of_mem _ hk, by rw [dist_comm]; exact hkd.trans hj⟩

section Meas

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Membership in the closure of a random Cayley image is a measurable event.** -/
theorem measurableSet_mem_closure_cayley_image {C : Ω → Set ℂ} (hCo : ∀ ω, IsOpen (C ω)) (hCH : ∀ ω, C ω ⊆ H)
    (hCm : ∀ z, MeasurableSet {ω | z ∈ C ω}) {e : ℕ → ℂ} (he : DenseRange e) {w : Ω → ℂ} (hw : Measurable w) :
    MeasurableSet {ω | w ω ∈ closure (cayley '' C ω)} := by
  have e1 : {ω | w ω ∈ closure (cayley '' C ω)} =
      ⋂ j : ℕ, ⋃ k : ℕ, {ω | e k ∈ C ω} ∩ {ω | dist (cayley (e k)) (w ω) < 1 / ((j : ℝ) + 1)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, mem_inter_iff]
    exact mem_closure_cayley_image_iff (hCo ω) (hCH ω) he
  rw [e1]
  exact MeasurableSet.iInter fun j => MeasurableSet.iUnion fun k =>
    (hCm (e k)).inter (measurableSet_lt (measurable_const.dist hw) measurable_const)

end Meas

/-! ### The wall crosscut and its rational hitting times -/

/-- The right-wall crosscut `α̃ = toDisc α` of an `ℝ≥0`-indexed curve, at disc time `s`. -/
def wallPt (R : ℝ≥0 → ℂ) (s : ℝ) : ℂ := WangWu.toDisc (Lemma71I.realPath R) s

/-- The rational disc times `s ∈ [0, 1]` at which the wall crosscut lies in `U`. -/
def ratHits (R : ℝ≥0 → ℂ) (U : Set ℂ) : Set ℝ :=
  {s | ∃ q : ℚ, (q : ℝ) = s ∧ 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 1 ∧ wallPt R q ∈ U}

/-- The opening time: the infimum of the rational hitting times (`1` if there is none). -/
def openTime (R : ℝ≥0 → ℂ) (U : Set ℂ) : ℝ := sInf (insert 1 (ratHits R U))

/-- The closing time: the supremum of the rational hitting times (`0` if there is none). -/
def closeTime (R : ℝ≥0 → ℂ) (U : Set ℂ) : ℝ := sSup (insert 0 (ratHits R U))

theorem ratHits_subset_Icc (R : ℝ≥0 → ℂ) (U : Set ℂ) : ratHits R U ⊆ Icc 0 1 := by
  rintro s ⟨q, rfl, h0, h1, -⟩
  exact ⟨h0, h1⟩

theorem bddBelow_insert_ratHits (R : ℝ≥0 → ℂ) (U : Set ℂ) : BddBelow (insert 1 (ratHits R U)) :=
  ⟨0, by
    rintro s (rfl | hs)
    · exact zero_le_one
    · exact (ratHits_subset_Icc R U hs).1⟩

theorem bddAbove_insert_ratHits (R : ℝ≥0 → ℂ) (U : Set ℂ) : BddAbove (insert 0 (ratHits R U)) :=
  ⟨1, by
    rintro s (rfl | hs)
    · exact zero_le_one
    · exact (ratHits_subset_Icc R U hs).2⟩

theorem openTime_lt_iff (R : ℝ≥0 → ℂ) (U : Set ℂ) (x : ℝ) :
    openTime R U < x ↔ 1 < x ∨ ∃ q : ℚ, (q : ℝ) < x ∧ 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 1 ∧ wallPt R q ∈ U := by
  rw [openTime, csInf_lt_iff (bddBelow_insert_ratHits R U) (insert_nonempty _ _)]
  constructor
  · rintro ⟨s, rfl | ⟨q, rfl, h0, h1, hU⟩, hs⟩
    · exact Or.inl hs
    · exact Or.inr ⟨q, hs, h0, h1, hU⟩
  · rintro (h | ⟨q, hq, h0, h1, hU⟩)
    · exact ⟨1, mem_insert _ _, h⟩
    · exact ⟨q, mem_insert_of_mem _ ⟨q, rfl, h0, h1, hU⟩, hq⟩

theorem lt_closeTime_iff (R : ℝ≥0 → ℂ) (U : Set ℂ) (x : ℝ) :
    x < closeTime R U ↔ x < 0 ∨ ∃ q : ℚ, x < (q : ℝ) ∧ 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 1 ∧ wallPt R q ∈ U := by
  rw [closeTime, lt_csSup_iff (bddAbove_insert_ratHits R U) (insert_nonempty _ _)]
  constructor
  · rintro ⟨s, rfl | ⟨q, rfl, h0, h1, hU⟩, hs⟩
    · exact Or.inl hs
    · exact Or.inr ⟨q, hs, h0, h1, hU⟩
  · rintro (h | ⟨q, hq, h0, h1, hU⟩)
    · exact ⟨0, mem_insert _ _, h⟩
    · exact ⟨q, mem_insert_of_mem _ ⟨q, rfl, h0, h1, hU⟩, hq⟩

/-- **The measurable times on an interval configuration.** If the wall times in `[0, 1]` lying in `U` form exactly the
interval `[a, b]` with `0 ≤ a < b ≤ 1`, the opening time is `a` and the closing time is `b`. -/
theorem openTime_closeTime_eq {R : ℝ≥0 → ℂ} {U : Set ℂ} {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hI : {s ∈ Icc (0 : ℝ) 1 | wallPt R s ∈ U} = Icc a b) : openTime R U = a ∧ closeTime R U = b := by
  have hmem : ∀ q : ℚ, (q : ℝ) ∈ Icc a b → (q : ℝ) ∈ ratHits R U := fun q hq => by
    have : (q : ℝ) ∈ {s ∈ Icc (0 : ℝ) 1 | wallPt R s ∈ U} := hI ▸ hq
    exact ⟨q, rfl, this.1.1, this.1.2, this.2⟩
  have hsub : ratHits R U ⊆ Icc a b := by
    rintro s ⟨q, rfl, h0, h1, hU⟩
    have : (q : ℝ) ∈ {s ∈ Icc (0 : ℝ) 1 | wallPt R s ∈ U} := ⟨⟨h0, h1⟩, hU⟩
    rwa [hI] at this
  refine ⟨csInf_eq_of_forall_ge_of_forall_gt_exists_lt (insert_nonempty _ _) ?_ ?_,
    csSup_eq_of_forall_le_of_forall_lt_exists_gt (insert_nonempty _ _) ?_ ?_⟩
  · rintro s (rfl | hs)
    · exact hab.le.trans hb
    · exact (hsub hs).1
  · intro w hw
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min hw hab)
    exact ⟨q, mem_insert_of_mem _ (hmem q ⟨hq1.le, (hq2.trans_le (min_le_right _ _)).le⟩),
      hq2.trans_le (min_le_left _ _)⟩
  · rintro s (rfl | hs)
    · exact ha.trans hab.le
    · exact (hsub hs).2
  · intro w hw
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hw hab)
    exact ⟨q, mem_insert_of_mem _ (hmem q ⟨((le_max_right _ _).trans_lt hq1).le, hq2.le⟩),
      (le_max_left _ _).trans_lt hq1⟩

section Meas

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The wall crosscut at a fixed time is measurable when the wall's coordinates are. -/
theorem measurable_wallPt_const {R : Ω → ℝ≥0 → ℂ} (hRm : ∀ t, Measurable fun ω => R ω t) (s : ℝ) :
    Measurable fun ω => wallPt (R ω) s := by
  unfold wallPt WangWu.toDisc Lemma71I.realPath
  by_cases hs : s < 1
  · simp only [hs, ↓reduceIte]
    exact measurable_cayley.comp (hRm _)
  · simp only [hs, ↓reduceIte]
    exact measurable_const

/-- **The wall crosscut at a measurable time is measurable** (the wall is continuous for every `ω`). -/
theorem measurable_wallPt {R : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hRm : ∀ t, Measurable fun ω => R ω t)
    {s : Ω → ℝ} (hs : Measurable s) : Measurable fun ω => wallPt (R ω) (s ω) := by
  have hj : Measurable (Function.uncurry fun (t : ℝ≥0) (ω : Ω) => R ω t) :=
    measurable_uncurry_of_continuous_of_measurable (fun ω => hRc ω) hRm
  have harc : Measurable fun x : ℝ => WangWu.arcTime x := by
    unfold WangWu.arcTime
    fun_prop
  have hR' : Measurable fun ω => R ω (WangWu.arcTime (s ω)).toNNReal :=
    hj.comp ((measurable_real_toNNReal.comp (harc.comp hs)).prodMk measurable_id)
  unfold wallPt WangWu.toDisc Lemma71I.realPath
  exact Measurable.ite (measurableSet_lt hs measurable_const) (measurable_cayley.comp hR') measurable_const

/-- **The opening time is measurable** when the membership events of the wall points are. -/
theorem measurable_openTime {R : Ω → ℝ≥0 → ℂ} {U : Ω → Set ℂ}
    (hU : ∀ q : ℚ, MeasurableSet {ω | wallPt (R ω) q ∈ U ω}) : Measurable fun ω => openTime (R ω) (U ω) := by
  refine measurable_of_Iio fun x => ?_
  have e1 : (fun ω => openTime (R ω) (U ω)) ⁻¹' Iio x =
      {_ω | 1 < x} ∪ ⋃ q : ℚ, {_ω | (q : ℝ) < x ∧ 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 1} ∩ {ω | wallPt (R ω) q ∈ U ω} := by
    ext ω
    simp only [mem_preimage, mem_Iio, openTime_lt_iff, mem_union, mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · rintro (h | ⟨q, h1, h2, h3, h4⟩)
      · exact Or.inl h
      · exact Or.inr ⟨q, ⟨h1, h2, h3⟩, h4⟩
    · rintro (h | ⟨q, ⟨h1, h2, h3⟩, h4⟩)
      · exact Or.inl h
      · exact Or.inr ⟨q, h1, h2, h3, h4⟩
  rw [e1]
  exact (MeasurableSet.const _).union (MeasurableSet.iUnion fun q => (MeasurableSet.const _).inter (hU q))

/-- **The closing time is measurable** when the membership events of the wall points are. -/
theorem measurable_closeTime {R : Ω → ℝ≥0 → ℂ} {U : Ω → Set ℂ}
    (hU : ∀ q : ℚ, MeasurableSet {ω | wallPt (R ω) q ∈ U ω}) : Measurable fun ω => closeTime (R ω) (U ω) := by
  refine measurable_of_Ioi fun x => ?_
  have e1 : (fun ω => closeTime (R ω) (U ω)) ⁻¹' Ioi x =
      {_ω | x < 0} ∪ ⋃ q : ℚ, {_ω | x < (q : ℝ) ∧ 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 1} ∩ {ω | wallPt (R ω) q ∈ U ω} := by
    ext ω
    simp only [mem_preimage, mem_Ioi, lt_closeTime_iff, mem_union, mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · rintro (h | ⟨q, h1, h2, h3, h4⟩)
      · exact Or.inl h
      · exact Or.inr ⟨q, ⟨h1, h2, h3⟩, h4⟩
    · rintro (h | ⟨q, ⟨h1, h2, h3⟩, h4⟩)
      · exact Or.inl h
      · exact Or.inr ⟨q, h1, h2, h3, h4⟩
  rw [e1]
  exact (MeasurableSet.const _).union (MeasurableSet.iUnion fun q => (MeasurableSet.const _).inter (hU q))

end Meas

/-! ### Approach sequences in the compactified picture -/

section Approach

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A measurable approach sequence to a point of the closure of the Cayley image.** For a random open `C ω ⊆ ℍ`
with measurable membership events, a dense sequence `e`, a measurable fallback index `N₀` with `e (N₀ ω) ∈ C ω`, and a
measurable `w ω`: indices `N m ω` with `e (N m ω) ∈ C ω` for every `ω`, such that `cayley (e (N m ω)) → w ω` within
`cayley '' C ω` whenever `w ω ∈ closure (cayley '' C ω)`. -/
theorem exists_measurable_approach_cayley {C : Ω → Set ℂ} (hCo : ∀ ω, IsOpen (C ω)) (hCH : ∀ ω, C ω ⊆ H)
    (hCm : ∀ z, MeasurableSet {ω | z ∈ C ω}) {e : ℕ → ℂ} (he : DenseRange e) {N₀ : Ω → ℕ} (hN₀ : Measurable N₀)
    (hN₀C : ∀ ω, e (N₀ ω) ∈ C ω) {w : Ω → ℂ} (hw : Measurable w) :
    ∃ N : ℕ → Ω → ℕ, (∀ m, Measurable (N m)) ∧ (∀ m ω, e (N m ω) ∈ C ω) ∧
      ∀ ω, w ω ∈ closure (cayley '' C ω) →
        Tendsto (fun m => cayley (e (N m ω))) atTop (𝓝[cayley '' C ω] (w ω)) := by
  classical
  set p : ℕ → ℕ → Ω → Prop := fun m j ω => e j ∈ C ω ∧ dist (cayley (e j)) (w ω) < 1 / ((m : ℝ) + 1) with hpdef
  have hpm : ∀ m j, MeasurableSet {ω | p m j ω} := fun m j =>
    (hCm (e j)).inter (measurableSet_lt (measurable_const.dist hw) measurable_const)
  set E : ℕ → Set Ω := fun m => {ω | ∃ j, p m j ω} with hEdef
  have hEm : ∀ m, MeasurableSet (E m) := fun m => by
    have : E m = ⋃ j, {ω | p m j ω} := by ext ω; simp [hEdef]
    rw [this]
    exact MeasurableSet.iUnion fun j => hpm m j
  set q : ℕ → Ω → ℕ → Prop := fun m ω j => p m j ω ∨ (ω ∉ E m ∧ j = N₀ ω) with hqdef
  have hq : ∀ m ω, ∃ j, q m ω j := fun m ω => by
    by_cases hω : ω ∈ E m
    · obtain ⟨j, hj⟩ := hω
      exact ⟨j, Or.inl hj⟩
    · exact ⟨N₀ ω, Or.inr ⟨hω, rfl⟩⟩
  have hqm : ∀ m j, MeasurableSet {ω | q m ω j} := fun m j =>
    (hpm m j).union ((hEm m).compl.inter (measurableSet_eq_fun measurable_const hN₀))
  refine ⟨fun m ω => Nat.find (hq m ω), fun m => measurable_find (hq m) (hqm m), fun m ω => ?_, fun ω hω => ?_⟩
  · rcases Nat.find_spec (hq m ω) with h | ⟨-, h⟩
    · exact h.1
    · dsimp only
      rw [h]; exact hN₀C ω
  · have hE : ∀ m, ω ∈ E m := fun m => (mem_closure_cayley_image_iff (hCo ω) (hCH ω) he).1 hω m
    have hspec : ∀ m, p m (Nat.find (hq m ω)) ω := fun m => by
      rcases Nat.find_spec (hq m ω) with h | ⟨h, -⟩
      · exact h
      · exact absurd (hE m) h
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun m => mem_image_of_mem _ (hspec m).1⟩
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun m => dist_nonneg) (fun m => (hspec m).2.le)
      tendsto_one_div_add_atTop_nhds_zero_nat)

end Approach

/-! ### The marked points of a pocket (deterministic) -/

/-- **The wall times of a pocket form its contact gap.** For the pocket `U = jordanIn (α̃[a, b] ∪ β̃[j a, j b])` of a
contact gap `(a, b)` of two ordered crosscuts, the times `s ∈ [0, 1]` with `α̃ s ∈ closure U` are exactly `[a, b]`. -/
theorem wallTimes_eq_Icc_of_contactGap {α' β' : ℝ → ℂ} (hα : WangWu.IsDiscCrosscut α')
    (hβ : WangWu.IsDiscCrosscut β') (hord' : Disjoint (WangWu.crossRange β') (WangWu.crossSide α' (-1)))
    {a b : ℝ} (hg : WangWu.IsContactGap α' β' a b) :
    {s ∈ Icc (0 : ℝ) 1 | α' s ∈ closure (WangWu.jordanIn (WangWu.pocketCurve α' β' a b))} = Icc a b := by
  obtain ⟨-, -, hUαβ, hUfr, -⟩ := WangWu.pocket_props hα hβ hord' hg
  obtain ⟨ha, hb, hab, -⟩ := hg
  have ha01 : a ∈ Icc (0 : ℝ) 1 := ha.1
  have hb01 : b ∈ Icc (0 : ℝ) 1 := hb.1
  set U := WangWu.jordanIn (WangWu.pocketCurve α' β' a b)
  ext s
  constructor
  · rintro ⟨hs01, hsU⟩
    rw [closure_eq_self_union_frontier] at hsU
    rcases hsU with hsU | hsU
    · exact absurd (Or.inl ⟨s, hs01, rfl⟩) (Set.disjoint_left.1 hUαβ hsU)
    rw [hUfr] at hsU
    rcases hsU with ⟨s', hs', hss'⟩ | ⟨r, hr, hrs⟩
    · rwa [hα.inj hs01 ⟨ha01.1.trans hs'.1, hs'.2.trans hb01.2⟩ hss'.symm]
    · have hja := WangWu.contactMap_mem hβ ha
      have hjb := WangWu.contactMap_mem hβ hb
      have hr01 : r ∈ Icc (0 : ℝ) 1 := ⟨hja.1.1.trans hr.1, hr.2.trans hjb.1.2⟩
      have hsc : s ∈ pocketContactSet α' β' := ⟨hs01, r, hr01, hrs⟩
      have hjs : WangWu.contactMap α' β' s = r := WangWu.contactMap_eq hβ hr01 hrs.symm
      have hmono := WangWu.strictMonoOn_contactMap hα hβ hord'
      refine ⟨le_of_not_gt fun hsa => ?_, le_of_not_gt fun hbs => ?_⟩
      · have := hmono hsc ha hsa
        rw [hjs] at this
        exact absurd hr.1 (not_le.2 this)
      · have := hmono hb hsc hbs
        rw [hjs] at this
        exact absurd hr.2 (not_le.2 this)
  · intro hs
    refine ⟨⟨ha01.1.trans hs.1, hs.2.trans hb01.2⟩, frontier_subset_closure ?_⟩
    rw [hUfr]
    exact Or.inl ⟨s, hs, rfl⟩

/-- **The marked points of a pocket between two ordered proper arcs.** For a component `C` between the right wall `R`
and the left wall `L`, the times `s ∈ [0, 1]` at which the right-wall crosscut `α̃ = toDisc R` lies in
`closure (cayley '' C)` form exactly an interval `[a, b]` with `0 ≤ a < b ≤ 1` (the contact gap of the pocket); the
frontier of `cayley '' C` is a Jordan curve, and it contains the distinct marked points `α̃ a` (opening) and `α̃ b`
(closing). -/
theorem pocket_marked {R L : ℝ → ℂ} (hR : WangWu.IsProperArc R) (hL : WangWu.IsProperArc L)
    (hord : Disjoint (WangWu.arcRange L) (rightSideOf (WangWu.arcRange R))) {C : Set ℂ}
    (hC : C ∈ betweenComponents (WangWu.arcRange R) (WangWu.arcRange L)) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
      {s ∈ Icc (0 : ℝ) 1 | WangWu.toDisc R s ∈ closure (cayley '' C)} = Icc a b ∧
      LQGMetric.JordanMap.IsJordanCurve (frontier (cayley '' C)) ∧
      WangWu.toDisc R a ∈ frontier (cayley '' C) ∧ WangWu.toDisc R b ∈ frontier (cayley '' C) ∧
      WangWu.toDisc R a ≠ WangWu.toDisc R b := by
  obtain ⟨a, b, hg, hCU⟩ := WangWu.exists_contactGap_of_mem_betweenComponents hR hL hord hC
  have hα := hR.isDiscCrosscut_toDisc
  have hβ := hL.isDiscCrosscut_toDisc
  have hord' := (WangWu.disjoint_rightSideOf_iff hR hL).1 hord
  have hI := wallTimes_eq_Icc_of_contactGap hα hβ hord' hg
  obtain ⟨hJ, -, -, hUfr, -⟩ := WangWu.pocket_props hα hβ hord' hg
  obtain ⟨ha, hb, hab, -⟩ := hg
  rw [hCU]
  refine ⟨a, b, ha.1.1, hab, hb.1.2, hI, by rw [hUfr]; exact hJ, ?_, ?_, fun h => hab.ne (hα.inj ha.1 hb.1 h)⟩
  · rw [hUfr]; exact Or.inl ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩
  · rw [hUfr]; exact Or.inl ⟨b, ⟨hab.le, le_rfl⟩, rfl⟩

end InteractingSLE.Sec7.Lemma71K
