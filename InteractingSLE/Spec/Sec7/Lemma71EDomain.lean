/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71EDisc

/-!
# The pocket between two random curves, observed through closed balls

Packet PROVE-LEMMA71E, item (3) (PROVE-LEMMA71D's "What remains" C (i): "the pocket `C(ω)` as a random open set
with measurable events `{closedBall c r ⊆ C(ω)}` (from measurable outer curves; rational-point rule for the choice of
`C`)"). Specification §7.1, setup (p. 222): "Fix a connected component `C` of `ℍ \ (η_{θ₁} ∪ η_{θ₂})` … fix a positive
integer `k` and a countable, dense sequence `(r_n)` … let `C` be the component containing the `k`th element".

* `measurableSet_closedBall_inter_image_eq_empty`: for a random path `η ω`, continuous on `[0, ∞)` and measurable at
  each time, `{closedBall c r ∩ η_ω([0, ∞)) = ∅}` is measurable (rational times on each `[0, n]`);
* **`measurableSet_closedBall_subset_complement`**: hence `{closedBall c r ⊆ ℍ \ (η₁([0, ∞)) ∪ η₂([0, ∞)))}`;
* **`measurableSet_closedBall_subset_component`**: for a random open set `U ω` observed through closed balls and a
  base point `e (Np ω) ∈ U ω` with measurable index, the component `C ω = connectedComponentIn (U ω) (e (Np ω))` is
  again observed through closed balls (a closed ball lies in the component iff it lies in `U ω` and its centre is
  joined to the base point inside the union of the first rational discs of `U ω`, a finite measurable test,
  `Kernel.exists_mem_connectedComponentIn_ratDiscUnion`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Function MeasureTheory
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec7.Lemma71E

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A continuous path meets a closed set on `[0, n]` iff it comes within every `1/(j+1)` of it at a rational time
of `[0, n]`. -/
theorem image_Icc_inter_nonempty_iff {g : ℝ → ℂ} (hg : ContinuousOn g (Ici 0)) {B : Set ℂ} (hB : IsClosed B)
    (hBne : B.Nonempty) (n : ℕ) :
    (B ∩ g '' Icc 0 n).Nonempty ↔
      ∀ j : ℕ, ∃ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) n ∧ infDist (g q) B < 1 / ((j : ℝ) + 1) := by
  constructor
  · rintro ⟨z, hzB, t, ht, rfl⟩ j
    have hj : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    have hgc : ContinuousWithinAt g (Icc 0 n) t := (hg t ht.1).mono Icc_subset_Ici_self
    obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.1 (hgc.eventually (ball_mem_nhds _ hj))
    -- a rational time of `[0, n]` near `t`
    obtain ⟨q, hq, hqt⟩ : ∃ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) n ∧ |(q : ℝ) - t| < δ := by
      rcases (Nat.cast_nonneg n : (0 : ℝ) ≤ n).lt_or_eq with hn | hn
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max 0 (t - δ) < min (n : ℝ) (t + δ) from
          max_lt (lt_min hn (by linarith [ht.1])) (lt_min (by linarith [ht.2]) (by linarith)))
        refine ⟨q, ⟨(le_max_left _ _).trans hq1.le, hq2.le.trans (min_le_left _ _)⟩, abs_lt.2 ⟨?_, ?_⟩⟩
        · linarith [le_max_right 0 (t - δ)]
        · linarith [min_le_right (n : ℝ) (t + δ)]
      · have ht0 : t = 0 := le_antisymm (hn ▸ ht.2) ht.1
        exact ⟨0, by simp [← hn], by simp [ht0, hδ]⟩
    refine ⟨q, hq, lt_of_le_of_lt (infDist_le_dist_of_mem hzB) ?_⟩
    exact hδs ⟨mem_ball.2 (by rw [Real.dist_eq]; exact hqt), hq⟩
  · intro h
    choose q hq hqd using h
    obtain ⟨t, ht, φ, hφ, hlim⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := n)).tendsto_subseq
      (x := fun i => ((q i : ℚ) : ℝ)) hq
    have hlim' : Tendsto (fun i => ((q (φ i) : ℚ) : ℝ)) atTop (𝓝[Ici 0] t) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun i => (hq _).1⟩
    have hεlim : Tendsto (fun i => 1 / (((φ i : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have hd := ((continuous_infDist_pt B).tendsto (g t)).comp ((hg t ht.1).tendsto.comp hlim')
    have h0 : infDist (g t) B = 0 :=
      le_antisymm (le_of_tendsto_of_tendsto' hd hεlim fun i => (hqd _).le) infDist_nonneg
    exact ⟨g t, (hB.mem_iff_infDist_zero hBne).2 h0, t, ht, rfl⟩

/-- **A random path misses a closed ball: a measurable event.** -/
theorem measurableSet_closedBall_inter_image_eq_empty {η : Ω → ℝ → ℂ} (hη : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hm : ∀ t, 0 ≤ t → Measurable fun ω => η ω t) (c : ℂ) (r : ℝ) :
    MeasurableSet {ω | closedBall c r ∩ η ω '' Ici 0 = ∅} := by
  rcases lt_or_ge r 0 with hr | hr
  · have : {ω | closedBall c r ∩ η ω '' Ici 0 = ∅} = univ := by
      ext ω
      simp [closedBall_eq_empty.2 hr]
    rw [this]
    exact MeasurableSet.univ
  have hBne : (closedBall c r).Nonempty := nonempty_closedBall.2 hr
  have heq : {ω | closedBall c r ∩ η ω '' Ici 0 = ∅} =
      ⋂ n : ℕ, {ω | ¬ (closedBall c r ∩ η ω '' Icc 0 n).Nonempty} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, not_nonempty_iff_eq_empty]
    constructor
    · intro h n
      exact subset_empty_iff.1 (h ▸ inter_subset_inter_right _ (image_mono Icc_subset_Ici_self))
    · intro h
      refine subset_empty_iff.1 fun z ⟨hzB, t, ht, htz⟩ => ?_
      obtain ⟨n, hn⟩ := exists_nat_ge t
      have : z ∈ closedBall c r ∩ η ω '' Icc 0 n := ⟨hzB, t, ⟨ht, hn⟩, htz⟩
      rw [h n] at this
      exact this
  rw [heq]
  refine MeasurableSet.iInter fun n => ?_
  have hc : {ω | ¬ (closedBall c r ∩ η ω '' Icc 0 n).Nonempty} =
      {ω | (closedBall c r ∩ η ω '' Icc 0 n).Nonempty}ᶜ := rfl
  rw [hc]
  refine MeasurableSet.compl ?_
  have heq' : {ω | (closedBall c r ∩ η ω '' Icc 0 n).Nonempty} =
      ⋂ j : ℕ, ⋃ q : ℚ, {ω | (q : ℝ) ∈ Icc (0 : ℝ) n ∧ infDist (η ω q) (closedBall c r) < 1 / ((j : ℝ) + 1)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion]
    exact image_Icc_inter_nonempty_iff (hη ω) isClosed_closedBall hBne n
  rw [heq']
  refine MeasurableSet.iInter fun j => MeasurableSet.iUnion fun q => ?_
  by_cases hq : (q : ℝ) ∈ Icc (0 : ℝ) n
  · simp only [hq, true_and]
    exact measurableSet_lt ((continuous_infDist_pt _).measurable.comp (hm q hq.1)) measurable_const
  · simp [hq]

/-- **The closed balls inside the complement of two random paths in `ℍ`: measurable events.** -/
theorem measurableSet_closedBall_subset_complement {η₁ η₂ : Ω → ℝ → ℂ}
    (hη₁ : ∀ ω, ContinuousOn (η₁ ω) (Ici 0)) (hη₂ : ∀ ω, ContinuousOn (η₂ ω) (Ici 0))
    (hm₁ : ∀ t, 0 ≤ t → Measurable fun ω => η₁ ω t) (hm₂ : ∀ t, 0 ≤ t → Measurable fun ω => η₂ ω t)
    (c : ℂ) (r : ℝ) :
    MeasurableSet {ω | closedBall c r ⊆ H \ (η₁ ω '' Ici 0 ∪ η₂ ω '' Ici 0)} := by
  have heq : {ω | closedBall c r ⊆ H \ (η₁ ω '' Ici 0 ∪ η₂ ω '' Ici 0)} =
      {_ω | closedBall c r ⊆ H} ∩ ({ω | closedBall c r ∩ η₁ ω '' Ici 0 = ∅} ∩
        {ω | closedBall c r ∩ η₂ ω '' Ici 0 = ∅}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, subset_sdiff, disjoint_union_right,
      ← disjoint_iff_inter_eq_empty]
  rw [heq]
  exact (MeasurableSet.const _).inter ((measurableSet_closedBall_inter_image_eq_empty hη₁ hm₁ c r).inter
    (measurableSet_closedBall_inter_image_eq_empty hη₂ hm₂ c r))

/-- **The component of a random open set through a random rational base point is observed through closed balls.** -/
theorem measurableSet_closedBall_subset_component {U : Ω → Set ℂ} (hUo : ∀ ω, IsOpen (U ω))
    (hUm : ∀ (c : ℂ) (r : ℝ), MeasurableSet {ω | closedBall c r ⊆ U ω}) {e : ℕ → ℂ} {Np : Ω → ℕ}
    (hNp : Measurable Np) (hpU : ∀ ω, e (Np ω) ∈ U ω) (c : ℂ) (r : ℝ) :
    MeasurableSet {ω | closedBall c r ⊆ connectedComponentIn (U ω) (e (Np ω))} := by
  rcases lt_or_ge r 0 with hr | hr
  · have : {ω | closedBall c r ⊆ connectedComponentIn (U ω) (e (Np ω))} = univ := by
      ext ω
      simp [closedBall_eq_empty.2 hr]
    rw [this]
    exact MeasurableSet.univ
  -- membership of the centre in the component, through the first rational discs
  have hcomp : ∀ ω, c ∈ connectedComponentIn (U ω) (e (Np ω)) ↔
      ∃ N : ℕ, c ∈ connectedComponentIn (ratDiscUnion (ratDiscIndices (U ω) N)) (e (Np ω)) := by
    intro ω
    constructor
    · intro hc
      have hCo : IsOpen (connectedComponentIn (U ω) (e (Np ω))) := (hUo ω).connectedComponentIn
      have hCc : IsConnected (connectedComponentIn (U ω) (e (Np ω))) :=
        isConnected_connectedComponentIn_iff.2 (hpU ω)
      obtain ⟨N, hN⟩ := exists_mem_connectedComponentIn_ratDiscUnion hCo hCc
        (mem_connectedComponentIn (hpU ω)) hc
      refine ⟨N, connectedComponentIn_mono _ (ratDiscUnion_mono fun k hk => ?_) hN⟩
      rw [mem_ratDiscIndices] at hk ⊢
      exact ⟨hk.1, hk.2.trans (connectedComponentIn_subset _ _)⟩
    · rintro ⟨N, hN⟩
      exact connectedComponentIn_mono _ (ratDiscUnion_ratDiscIndices_subset _ N) hN
  have heq : {ω | closedBall c r ⊆ connectedComponentIn (U ω) (e (Np ω))} =
      {ω | closedBall c r ⊆ U ω} ∩ ⋃ N : ℕ, ⋃ j : ℕ, ({ω | Np ω = j} ∩
        {ω | c ∈ connectedComponentIn (ratDiscUnion (ratDiscIndices (U ω) N)) (e j)}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iUnion]
    constructor
    · intro h
      refine ⟨h.trans (connectedComponentIn_subset _ _), ?_⟩
      obtain ⟨N, hN⟩ := (hcomp ω).1 (h (mem_closedBall_self hr))
      exact ⟨N, Np ω, rfl, hN⟩
    · rintro ⟨hU, N, j, hj, hN⟩
      have hc : c ∈ connectedComponentIn (U ω) (e (Np ω)) := (hcomp ω).2 ⟨N, hj ▸ hN⟩
      rw [connectedComponentIn_eq hc]
      exact (convex_closedBall c r).isPreconnected.subset_connectedComponentIn (mem_closedBall_self hr) hU
  rw [heq]
  refine (hUm c r).inter (MeasurableSet.iUnion fun N => MeasurableSet.iUnion fun j =>
    (measurableSet_eq_fun hNp measurable_const).inter ?_)
  exact measurableSet_setOfPred.2 (measurable_comp_ratDiscIndices hUm
    (fun S => c ∈ connectedComponentIn (ratDiscUnion S) (e j)) N)

end InteractingSLE.Sec7.Lemma71E
