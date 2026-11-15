/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ChartMeasHull

/-!
# Measurability of the mapping-out function of a random compact set

Packet PROVE-RESTART-CPL4. Let `K : Ω → Set ℂ` be a random compact set with `K ω ∪ {Im ≤ 0}` preconnected, observed
through its **dyadic hits**: every event `{Q ∩ K ω ≠ ∅}`, `Q` a closed dyadic square, is measurable
(`IsDyadicHitMeasurable`). Then the domain events `{z ∈ ℍ \ fill(K ω)}` are measurable, and the mapping-out function
`g_ω = mapOut (fill(K ω))` and its derivative are measurable in `ω` at every point of the domain (indicator form, the
form PROVE-PUSHFWD's `Chart.measurable_chartTransport_random'` asks for). The level-`n` cover takes countably many
values, measurably (`measurable_comp_dyadicIdx`), and the cover maps converge (`ChartMeasHull.lean`).

A general tool: **forward limits are measurable** (`measurable_of_tendsto_nhdsWithin`). If `f ω` has the limit `w ω`
at `q ω` along a random open set `D ω`, with measurable data, then `w` is measurable: a measurable choice of points of
`D ω` from a countable dense set (`Measurable.find`) converging to `q ω`.

## Main results

* `measurable_comp_of_countable_range`, `measurable_comp_dyadicIdx`, `measurableSet_comp_dyadicIdx`;
* `measurableSet_mem_H_diff_fillH`, `measurable_indicator_mapOut`, `measurable_indicator_deriv_mapOut`;
* `measurable_of_tendsto_nhdsWithin`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Restart

/-! ### Functions of a variable with countable range and measurable fibres -/

section Countable

variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]

/-- A function of a variable with countable range and measurable fibres is measurable. -/
theorem measurable_comp_of_countable_range {f : Ω → α} (hc : (range f).Countable)
    (hf : ∀ a, MeasurableSet (f ⁻¹' {a})) (G : α → β) : Measurable (G ∘ f) := by
  intro B _
  have heq : (G ∘ f) ⁻¹' B = ⋃ a ∈ range f ∩ G ⁻¹' B, f ⁻¹' {a} := by
    ext ω
    simp only [mem_preimage, Function.comp_apply, mem_iUnion, mem_inter_iff, mem_range, mem_singleton_iff,
      exists_prop]
    exact ⟨fun h => ⟨f ω, ⟨⟨ω, rfl⟩, h⟩, rfl⟩, fun ⟨a, ⟨_, ha⟩, hfa⟩ => hfa ▸ ha⟩
  rw [heq]
  exact MeasurableSet.biUnion (hc.mono inter_subset_left) fun a _ => hf a

theorem measurableSet_comp_of_countable_range {f : Ω → α} (hc : (range f).Countable)
    (hf : ∀ a, MeasurableSet (f ⁻¹' {a})) (p : α → Prop) : MeasurableSet {ω | p (f ω)} := by
  classical
  have h := measurable_comp_of_countable_range (β := Prop) hc hf p
  exact h (measurableSet_singleton True) |>.congr (by ext ω; simp)

end Countable

/-! ### Random compact sets observed through dyadic hits -/

/-- `K` is **dyadic-hit measurable**: whether a closed dyadic square meets `K ω` is a measurable event. -/
def IsDyadicHitMeasurable {Ω : Type*} [MeasurableSpace Ω] (K : Ω → Set ℂ) : Prop :=
  ∀ (n : ℕ) (k : ℤ × ℤ), MeasurableSet {ω | (dyadicSquare n k ∩ K ω).Nonempty}

/-- The union of the level-`n` squares with indices in `S`. -/
def coverOf (n : ℕ) (S : Set (ℤ × ℤ)) : Set ℂ := ⋃ k ∈ S, dyadicSquare n k

theorem dyadicCover_eq_coverOf (n : ℕ) (K : Set ℂ) : dyadicCover n K = coverOf n (dyadicIdx n K) := rfl

variable {Ω : Type*} [MeasurableSpace Ω] {K : Ω → Set ℂ}

theorem measurableSet_dyadicIdx_eq (hK : IsDyadicHitMeasurable K) (n : ℕ) (S : Set (ℤ × ℤ)) :
    MeasurableSet ((fun ω => dyadicIdx n (K ω)) ⁻¹' {S}) := by
  classical
  have heq : (fun ω => dyadicIdx n (K ω)) ⁻¹' {S} =
      ⋂ k : ℤ × ℤ, if k ∈ S then {ω | (dyadicSquare n k ∩ K ω).Nonempty}
        else {ω | (dyadicSquare n k ∩ K ω).Nonempty}ᶜ := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, mem_iInter]
    constructor
    · rintro h k
      split_ifs with hk
      · rw [← h] at hk; exact hk
      · exact fun h' => hk (h ▸ h')
    · intro h
      ext k
      have := h k
      split_ifs at this with hk
      · exact ⟨fun _ => hk, fun _ => this⟩
      · exact ⟨fun h' => (this h').elim, fun h' => (hk h').elim⟩
  rw [heq]
  refine MeasurableSet.iInter fun k => ?_
  split_ifs
  · exact hK n k
  · exact (hK n k).compl

omit [MeasurableSpace Ω] in
theorem countable_range_dyadicIdx (hKb : ∀ ω, Bornology.IsBounded (K ω)) (n : ℕ) :
    (range fun ω => dyadicIdx n (K ω)).Countable :=
  (Set.countable_ofPred_finite_subset (Set.countable_univ (α := ℤ × ℤ))).mono (by
    rintro _ ⟨ω, rfl⟩
    exact ⟨dyadicIdx_finite (hKb ω) n, subset_univ _⟩)

theorem measurable_comp_dyadicIdx {β : Type*} [MeasurableSpace β] (hK : IsDyadicHitMeasurable K)
    (hKb : ∀ ω, Bornology.IsBounded (K ω)) (n : ℕ) (G : Set (ℤ × ℤ) → β) :
    Measurable fun ω => G (dyadicIdx n (K ω)) :=
  measurable_comp_of_countable_range (countable_range_dyadicIdx hKb n) (measurableSet_dyadicIdx_eq hK n) G

theorem measurableSet_comp_dyadicIdx (hK : IsDyadicHitMeasurable K)
    (hKb : ∀ ω, Bornology.IsBounded (K ω)) (n : ℕ) (p : Set (ℤ × ℤ) → Prop) :
    MeasurableSet {ω | p (dyadicIdx n (K ω))} :=
  measurableSet_comp_of_countable_range (countable_range_dyadicIdx hKb n) (measurableSet_dyadicIdx_eq hK n) p

/-! ### The domain and the mapping-out function -/

section Domain

variable (hK : IsDyadicHitMeasurable K) (hKc : ∀ ω, IsCompact (K ω))
  (hKp : ∀ ω, IsPreconnected (K ω ∪ lowerHalf))
include hK hKc

/-- The domain events `{z ∈ ℍ \ fill(K ω)}` are measurable. -/
theorem measurableSet_mem_H_diff_fillH (z : ℂ) : MeasurableSet {ω | z ∈ H \ fillH (K ω)} := by
  have heq : {ω | z ∈ H \ fillH (K ω)} = ⋃ n : ℕ, {ω | z ∈ H \ fillH (coverOf n (dyadicIdx n (K ω)))} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, ← dyadicCover_eq_coverOf]
    constructor
    · intro hz
      have h := mem_iInter.not.1 (show z ∉ ⋂ n, fillH (dyadicCover n (K ω)) by
        rw [iInter_fillH_dyadicCover (hKc ω)]; exact hz.2)
      obtain ⟨n, hn⟩ := not_forall.1 h
      exact ⟨n, hz.1, hn⟩
    · rintro ⟨n, hz, hn⟩
      exact ⟨hz, fun h => hn (fillH_subset_fillH_dyadicCover n h)⟩
  rw [heq]
  exact MeasurableSet.iUnion fun n =>
    measurableSet_comp_dyadicIdx hK (fun ω => (hKc ω).isBounded) n fun S => z ∈ H \ fillH (coverOf n S)

include hKp in
/-- **The mapping-out function of a random compact set is measurable** at every point of its domain. -/
theorem measurable_indicator_mapOut (z : ℂ) :
    Measurable ({ω | z ∈ H \ fillH (K ω)}.indicator fun ω => ConformalImage.mapOut (fillH (K ω)) z) := by
  set E := {ω | z ∈ H \ fillH (K ω)}
  have hE : MeasurableSet E := measurableSet_mem_H_diff_fillH hK hKc z
  refine measurable_of_tendsto_metrizable (f := fun n => E.indicator fun ω =>
    ConformalImage.mapOut (fillH (coverOf n (dyadicIdx n (K ω)))) z) (fun n => ?_) ?_
  · exact (measurable_comp_dyadicIdx hK (fun ω => (hKc ω).isBounded) n
      fun S => ConformalImage.mapOut (fillH (coverOf n S)) z).indicator hE
  · rw [tendsto_pi_nhds]
    intro ω
    by_cases hω : ω ∈ E
    · simp only [indicator_of_mem hω, ← dyadicCover_eq_coverOf]
      exact (tendstoLocallyUniformlyOn_mapOut_dyadicCover (hKc ω) (hKp ω)).tendsto_at hω
    · simp only [indicator_of_notMem hω]
      exact tendsto_const_nhds

include hKp in
/-- The derivative of the mapping-out function is measurable at every point of the domain. -/
theorem measurable_indicator_deriv_mapOut (z : ℂ) :
    Measurable ({ω | z ∈ H \ fillH (K ω)}.indicator fun ω => deriv (ConformalImage.mapOut (fillH (K ω))) z) := by
  set E := {ω | z ∈ H \ fillH (K ω)}
  have hE : MeasurableSet E := measurableSet_mem_H_diff_fillH hK hKc z
  refine measurable_of_tendsto_metrizable (f := fun n => E.indicator fun ω =>
    deriv (ConformalImage.mapOut (fillH (coverOf n (dyadicIdx n (K ω))))) z) (fun n => ?_) ?_
  · exact (measurable_comp_dyadicIdx hK (fun ω => (hKc ω).isBounded) n
      fun S => deriv (ConformalImage.mapOut (fillH (coverOf n S))) z).indicator hE
  · rw [tendsto_pi_nhds]
    intro ω
    by_cases hω : ω ∈ E
    · simp only [indicator_of_mem hω, ← dyadicCover_eq_coverOf]
      exact (tendstoLocallyUniformlyOn_deriv_mapOut_dyadicCover (hKc ω) (hKp ω)).tendsto_at hω
    · simp only [indicator_of_notMem hω]
      exact tendsto_const_nhds

end Domain

/-! ### Forward limits along random open sets -/

section ForwardLimit

variable {Ω : Type*} [MeasurableSpace Ω] {D : Ω → Set ℂ} {f : Ω → ℂ → ℂ} {q w : Ω → ℂ}

/-- A measurable choice of points of a random open set converging to a point of its closure: the first point of a
dense sequence in `D ω` within `1/(m+1)` of `q ω`. -/
theorem exists_measurable_seq_tendsto (hDo : ∀ ω, IsOpen (D ω)) (hDm : ∀ z, MeasurableSet {ω | z ∈ D ω})
    (hq : Measurable q) (hqD : ∀ ω, q ω ∈ closure (D ω)) :
    ∃ (e : ℕ → ℂ) (N : ℕ → Ω → ℕ), (∀ m, Measurable (N m)) ∧ (∀ m ω, e (N m ω) ∈ D ω) ∧
      ∀ ω, Tendsto (fun m => e (N m ω)) atTop (𝓝[D ω] (q ω)) := by
  classical
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  have hex : ∀ (m : ℕ) (ω : Ω), ∃ j, e j ∈ D ω ∧ dist (e j) (q ω) < 1 / ((m : ℝ) + 1) := by
    intro m ω
    have hr : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    obtain ⟨y, hyD, hyq⟩ := Metric.mem_closure_iff.1 (hqD ω) _ hr
    obtain ⟨j, hj⟩ := he.exists_mem_open ((hDo ω).inter isOpen_ball)
      ⟨y, hyD, mem_ball.2 (by rw [dist_comm]; exact hyq)⟩
    exact ⟨j, hj.1, mem_ball.1 hj.2⟩
  refine ⟨e, fun m ω => Nat.find (hex m ω), fun m => ?_, fun m ω => (Nat.find_spec (hex m ω)).1, fun ω => ?_⟩
  · refine measurable_find (hex m) fun j => ?_
    exact (hDm (e j)).inter (measurableSet_lt (measurable_const.dist hq) measurable_const)
  · refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun m => (Nat.find_spec (hex m ω)).1⟩
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun m => dist_nonneg) (fun m => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat)
    exact (Nat.find_spec (hex m ω)).2.le

/-- **Forward limits are measurable.** If `f ω` tends to `w ω` at `q ω` along the random open set `D ω`, where the
domain events, `f` on the domain (indicator form) and `q` are measurable and `q ω ∈ closure (D ω)`, then `w` is
measurable. -/
theorem measurable_of_tendsto_nhdsWithin (hDo : ∀ ω, IsOpen (D ω)) (hDm : ∀ z, MeasurableSet {ω | z ∈ D ω})
    (hfm : ∀ z, Measurable ({ω | z ∈ D ω}.indicator fun ω => f ω z)) (hq : Measurable q)
    (hqD : ∀ ω, q ω ∈ closure (D ω)) (hlim : ∀ ω, Tendsto (f ω) (𝓝[D ω] (q ω)) (𝓝 (w ω))) :
    Measurable w := by
  obtain ⟨e, N, hNm, hND, hNt⟩ := exists_measurable_seq_tendsto hDo hDm hq hqD
  have hG : Measurable fun p : Ω × ℕ => {ω | e p.2 ∈ D ω}.indicator (fun ω => f ω (e p.2)) p.1 :=
    measurable_from_prod_countable_left fun j => hfm (e j)
  refine measurable_of_tendsto_metrizable (f := fun m ω => f ω (e (N m ω))) (fun m => ?_) ?_
  · have h := hG.comp (measurable_id.prodMk (hNm m))
    have heq : ((fun p : Ω × ℕ => {ω | e p.2 ∈ D ω}.indicator (fun ω => f ω (e p.2)) p.1) ∘
        fun a => (id a, N m a)) = fun ω => f ω (e (N m ω)) := by
      funext ω
      simp only [Function.comp_apply, id_eq]
      exact indicator_of_mem (show ω ∈ {ω | e (N m ω) ∈ D ω} from hND m ω) (fun ω => f ω (e (N m ω)))
    rwa [heq] at h
  · rw [tendsto_pi_nhds]
    exact fun ω => (hlim ω).comp (hNt ω)

end ForwardLimit

end Restart

end InteractingSLE
