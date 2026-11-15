/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Switching grids and rounded stopping times (proof of Proposition 5.9)

Packet PROVE-SEC5-A (specification §5.2, proof of Proposition 5.9, `source/spec/p145-192.md` L12–L25, pp. 145–146).

"We must switch at a time in `Q`, measured in the original clock. For each integer `m ≥ 1`, fix a locally finite
increasing grid `Q_m ⊆ Q` which is unbounded and has successive gaps at most `2^{1−m}`, and whose first point is at
most `2^{1−m}`. Such grids exist by density; for example, choose one point of `Q` in each consecutive interval of
length `2^{−m}`. Write `q_m(t) = min{q ∈ Q_m : q ≥ t}`. For a finite stopping time `T`, `q_m(T)` is again a stopping
time and `0 ≤ q_m(T) − T ≤ 2^{1−m}`. … We set `q_m(∞) = ∞`."

* `IsSwitchGrid Q δ g`: `g` is a strictly increasing unbounded sequence of points of `Q` with first point and gaps at
  most `δ` (a locally finite unbounded increasing grid, listed in order);
* `exists_isSwitchGrid`: such grids exist for every dense `Q ⊆ ℝ≥0` and every mesh `δ > 0` (one point of `Q` in each
  interval `(nδ/2, (n+1)δ/2)`);
* `gridCeil g t = q(t)` (`q(∞) = ∞`), with `le_gridCeil`, `gridCeil_le_add` (`q(t) − t ≤ δ`), `exists_gridCeil_eq`
  (`q(t)` is a grid point for finite `t`) and `gridCeil_le_iff`;
* `measurableSet_gridCeil_le`: `q(T)` is a stopping time when `T` is ("`{q_m(T) ≤ u} = {T ≤ p_m(u)} ∈ 𝓕_u`"; here
  as the countable union `⋃_{g n ≤ u} {T ≤ g n}`, which is the same event);
* `tendsto_gridCeil`, `eventually_gridCeil_lt_and_mem`: as the mesh tends to zero, `q_m(S) → S`, and on `{S < L}`,
  "continuity of the individual driving trajectory … gives, for all sufficiently large `m`, `q_m(S) < L`,
  `W(q_m(S)) ∈ I`" (right-continuity of the trajectory at `S` suffices);
* `exists_measure_le_add_of_subset_liminf`: "consequently one can choose `m` … so that the event in this display has
  probability at least `1 − ε`" (continuity from below).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec5

/-- A **switching grid** of mesh `δ` in `Q` (proof of Proposition 5.9): a strictly increasing unbounded sequence of
points of `Q` whose first point and successive gaps are at most `δ`. -/
structure IsSwitchGrid (Q : Set ℝ≥0) (δ : ℝ≥0) (g : ℕ → ℝ≥0) : Prop where
  mem : ∀ n, g n ∈ Q
  strictMono : StrictMono g
  zero_le : g 0 ≤ δ
  succ_le : ∀ n, g (n + 1) ≤ g n + δ
  tendsto : Tendsto g atTop atTop

/-- Switching grids exist: "choose one point of `Q` in each consecutive interval of length" `δ/2`. -/
theorem exists_isSwitchGrid {Q : Set ℝ≥0} (hQ : Dense Q) {δ : ℝ≥0} (hδ : 0 < δ) :
    ∃ g : ℕ → ℝ≥0, IsSwitchGrid Q δ g := by
  set ε : ℝ≥0 := δ / 2 with hε
  have hεpos : 0 < ε := by positivity
  have hex : ∀ n : ℕ, ∃ q ∈ Q, q ∈ Ioo (n * ε) ((n + 1) * ε) := fun n =>
    hQ.exists_between (mul_lt_mul_of_pos_right (by norm_cast; omega) hεpos)
  choose g hgQ hg using hex
  have hδε : δ = ε + ε := by rw [hε, add_halves]
  refine ⟨g, ⟨hgQ, ?_, ?_, fun n => ?_, ?_⟩⟩
  · refine strictMono_nat_of_lt_succ fun n => (hg n).2.trans ?_
    simpa using (hg (n + 1)).1
  · have := (hg 0).2
    simp only [CharP.cast_eq_zero, zero_add, one_mul] at this
    rw [hδε]; exact this.le.trans le_self_add
  · have h1 := (hg (n + 1)).2
    have h0 := (hg n).1
    push_cast at h1
    calc g (n + 1) ≤ (n + 1 + 1) * ε := h1.le
      _ = n * ε + (ε + ε) := by ring
      _ ≤ g n + δ := by rw [hδε]; exact add_le_add_left h0.le _
  · refine tendsto_atTop_atTop.2 fun b => ?_
    obtain ⟨N, hN⟩ := exists_nat_ge (b / ε)
    refine ⟨N, fun n hn => ?_⟩
    calc b = b / ε * ε := (div_mul_cancel₀ b hεpos.ne').symm
      _ ≤ n * ε := mul_le_mul_of_nonneg_right (hN.trans (by exact_mod_cast hn)) zero_le
      _ ≤ g n := (hg n).1.le

open Classical in
/-- **Rounding up to the grid**: `q(t) = min {g n : g n ≥ t}`, and `q(t) = ∞` if no grid point is `≥ t`
(in particular `q(∞) = ∞`). -/
def gridCeil (g : ℕ → ℝ≥0) (t : ℝ≥0∞) : ℝ≥0∞ :=
  if h : ∃ n, t ≤ g n then (g (Nat.find h) : ℝ≥0∞) else ⊤

theorem le_gridCeil (g : ℕ → ℝ≥0) (t : ℝ≥0∞) : t ≤ gridCeil g t := by
  classical
  unfold gridCeil
  split_ifs with h
  · exact Nat.find_spec h
  · exact le_top

@[simp] theorem gridCeil_top (g : ℕ → ℝ≥0) : gridCeil g ⊤ = ⊤ :=
  top_le_iff.1 (le_gridCeil g ⊤)

theorem exists_le_of_isSwitchGrid {Q : Set ℝ≥0} {δ : ℝ≥0} {g : ℕ → ℝ≥0} (hg : IsSwitchGrid Q δ g)
    {t : ℝ≥0∞} (ht : t ≠ ⊤) : ∃ n, t ≤ g n := by
  obtain ⟨n, hn⟩ := (hg.tendsto.eventually (eventually_ge_atTop t.toNNReal)).exists
  exact ⟨n, (ENNReal.coe_toNNReal ht).symm.le.trans (ENNReal.coe_le_coe.2 hn)⟩

/-- For finite `t`, `q(t)` is a grid point (hence a point of `Q`). -/
theorem exists_gridCeil_eq {Q : Set ℝ≥0} {δ : ℝ≥0} {g : ℕ → ℝ≥0} (hg : IsSwitchGrid Q δ g)
    {t : ℝ≥0∞} (ht : t ≠ ⊤) : ∃ n, gridCeil g t = g n := by
  classical
  have h := exists_le_of_isSwitchGrid hg ht
  exact ⟨Nat.find h, by simp only [gridCeil, h, ↓reduceDIte]⟩

/-- `0 ≤ q(t) − t ≤ δ`. -/
theorem gridCeil_le_add {Q : Set ℝ≥0} {δ : ℝ≥0} {g : ℕ → ℝ≥0} (hg : IsSwitchGrid Q δ g)
    (t : ℝ≥0∞) : gridCeil g t ≤ t + δ := by
  classical
  by_cases ht : t = ⊤
  · simp [ht]
  have h := exists_le_of_isSwitchGrid hg ht
  simp only [gridCeil, h, ↓reduceDIte]
  rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | hpos
  · rw [h0]
    exact (ENNReal.coe_le_coe.2 hg.zero_le).trans le_add_self
  · obtain ⟨k, hk⟩ : ∃ k, Nat.find h = k + 1 := ⟨Nat.find h - 1, by omega⟩
    have hlt : ¬ t ≤ g k := Nat.find_min h (by omega)
    rw [not_le] at hlt
    rw [hk]
    calc ((g (k + 1) : ℝ≥0) : ℝ≥0∞) ≤ ((g k + δ : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.2 (hg.succ_le k)
      _ = (g k : ℝ≥0∞) + δ := ENNReal.coe_add _ _
      _ ≤ t + δ := add_le_add hlt.le le_rfl

/-- `q(t) ≤ u` iff some grid point `g n` satisfies `t ≤ g n ≤ u`. -/
theorem gridCeil_le_iff {g : ℕ → ℝ≥0} (hg : Monotone g) (t : ℝ≥0∞) (u : ℝ≥0) :
    gridCeil g t ≤ u ↔ ∃ n, t ≤ g n ∧ g n ≤ u := by
  classical
  constructor
  · intro hq
    by_cases h : ∃ n, t ≤ g n
    · simp only [gridCeil, h, ↓reduceDIte, ENNReal.coe_le_coe] at hq
      exact ⟨Nat.find h, Nat.find_spec h, hq⟩
    · simp only [gridCeil, h, ↓reduceDIte, top_le_iff, ENNReal.coe_ne_top] at hq
  · rintro ⟨n, htn, hnu⟩
    have h : ∃ n, t ≤ g n := ⟨n, htn⟩
    simp only [gridCeil, h, ↓reduceDIte, ENNReal.coe_le_coe]
    exact (hg (Nat.find_min' h htn)).trans hnu

/-- **`q_m(T)` is a stopping time** when `T` is: `{q(T) ≤ u} = ⋃_{g n ≤ u} {T ≤ g n} ∈ 𝓕_u`. -/
theorem measurableSet_gridCeil_le {Ω : Type*} {m : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 m}
    {T : Ω → ℝ≥0∞} (hT : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | T ω ≤ s}) {g : ℕ → ℝ≥0}
    (hg : Monotone g) (u : ℝ≥0) : MeasurableSet[𝓕 u] {ω | gridCeil g (T ω) ≤ u} := by
  have : {ω | gridCeil g (T ω) ≤ u} = ⋃ n ∈ {n | g n ≤ u}, {ω | T ω ≤ g n} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, exists_prop, gridCeil_le_iff hg]
    exact ⟨fun ⟨n, h1, h2⟩ => ⟨n, h2, h1⟩, fun ⟨n, h1, h2⟩ => ⟨n, h2, h1⟩⟩
  rw [this]
  exact MeasurableSet.biUnion (to_countable _) fun n hn => 𝓕.mono hn _ (hT (g n))

/-- As the mesh tends to zero, `q_m(t) → t`. -/
theorem tendsto_gridCeil {Q : Set ℝ≥0} {δ : ℕ → ℝ≥0} {g : ℕ → ℕ → ℝ≥0}
    (hg : ∀ m, IsSwitchGrid Q (δ m) (g m)) (hδ : Tendsto δ atTop (𝓝 0)) (t : ℝ≥0∞) :
    Tendsto (fun m => gridCeil (g m) t) atTop (𝓝 t) := by
  have hup : Tendsto (fun m => t + (δ m : ℝ≥0∞)) atTop (𝓝 t) := by
    have h := (tendsto_const_nhds (x := t)).add ((ENNReal.continuous_coe.tendsto 0).comp hδ)
    simpa using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun m => le_gridCeil _ t) (fun m => gridCeil_le_add (hg m) t)

/-- On `{S < L}`, for all sufficiently large `m`: `q_m(S) < L`, and a trajectory `f` that is right-continuous at
`S` takes a value in a given open neighbourhood `U` of `f(S)` at `q_m(S)`. -/
theorem eventually_gridCeil_lt_and_mem {Q : Set ℝ≥0} {δ : ℕ → ℝ≥0} {g : ℕ → ℕ → ℝ≥0}
    (hg : ∀ m, IsSwitchGrid Q (δ m) (g m)) (hδ : Tendsto δ atTop (𝓝 0)) {S L : ℝ≥0∞} (hSL : S < L)
    {X : Type*} [TopologicalSpace X] {f : ℝ≥0 → X} (hf : ContinuousWithinAt f (Ici S.toNNReal) S.toNNReal)
    {U : Set X} (hU : IsOpen U) (hfU : f S.toNNReal ∈ U) :
    ∀ᶠ m in atTop, gridCeil (g m) S < L ∧ f (gridCeil (g m) S).toNNReal ∈ U := by
  have hS : S ≠ ⊤ := hSL.ne_top
  have ht := tendsto_gridCeil hg hδ S
  have h1 : ∀ᶠ m in atTop, gridCeil (g m) S < L := ht.eventually (gt_mem_nhds hSL)
  have hnn : Tendsto (fun m => (gridCeil (g m) S).toNNReal) atTop (𝓝[≥] S.toNNReal) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(ENNReal.tendsto_toNNReal hS).comp ht, Eventually.of_forall
      fun m => ?_⟩
    obtain ⟨n, hn⟩ := exists_gridCeil_eq (hg m) hS
    have hle := le_gridCeil (g m) S
    rw [hn] at hle ⊢
    simp only [mem_Ici, ENNReal.toNNReal_coe]
    exact ENNReal.toNNReal_mono ENNReal.coe_ne_top hle
  have h2 : ∀ᶠ m in atTop, f (gridCeil (g m) S).toNNReal ∈ U :=
    (hf.tendsto.comp hnn) (hU.mem_nhds hfU)
  exact h1.and h2

/-- "Consequently one can choose `m` … so that the event in this display has probability at least `1 − ε`": if
every point of `B` lies eventually in `A m`, then for every `ε > 0` some `A m` has `μ(B) ≤ μ(A m) + ε`. -/
theorem exists_measure_le_add_of_subset_liminf {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω)
    [IsFiniteMeasure μ] {A : ℕ → Set Ω} {B : Set Ω}
    (hB : B ⊆ {ω | ∀ᶠ n in atTop, ω ∈ A n}) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ n, μ B ≤ μ (A n) + ε := by
  set C : ℕ → Set Ω := fun n => ⋂ k ≥ n, A k with hC
  have hCm : Monotone C := fun a b hab => biInter_subset_biInter_left fun k hk => le_trans hab hk
  have hBC : B ⊆ ⋃ n, C n := by
    intro ω hω
    obtain ⟨n, hn⟩ := eventually_atTop.1 (hB hω)
    exact mem_iUnion.2 ⟨n, mem_iInter₂.2 hn⟩
  have hlim : Tendsto (fun n => μ (C n)) atTop (𝓝 (μ (⋃ n, C n))) :=
    tendsto_measure_iUnion_atTop hCm
  by_cases hεt : ε = ⊤
  · exact ⟨0, by rw [hεt, add_top]; exact le_top⟩
  have hlt : μ (⋃ n, C n) < μ (⋃ n, C n) + ε :=
    ENNReal.lt_add_right (measure_ne_top _ _) hε.ne'
  have hlim' : Tendsto (fun n => μ (C n) + ε) atTop (𝓝 (μ (⋃ n, C n) + ε)) :=
    hlim.add tendsto_const_nhds
  obtain ⟨n, hn⟩ := (hlim'.eventually (lt_mem_nhds hlt)).exists
  refine ⟨n, ((measure_mono hBC).trans hn.le).trans (add_le_add (measure_mono ?_) le_rfl)⟩
  exact biInter_subset_of_mem (le_refl n)

end Sec5

end InteractingSLE
