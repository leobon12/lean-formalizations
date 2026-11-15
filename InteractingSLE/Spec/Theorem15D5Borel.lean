/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.closedLeftSide
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Complex.Convex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Countable descriptions of components of open sets in `ℂ` and of the closed left side

Packet PROVE-T15-D5, infrastructure for the crossing step of D.5 (W5 applied to the conditional continuations under
the restart kernel needs W0's event — `HasOrderedProperCompletions`, the closed left side of a completion — to be
universally measurable; the specification remarks it is analytic, supplement §9, p. 528). Deterministic topology:

* **Polygonal reachability** (`Reach`): a point `z` of an open set `U ⊆ ℂ` is in the component of `w` iff it is
  reached from `w` by finitely many segments in `U` whose intermediate vertices are rational
  (`mem_connectedComponentIn_iff_exists_reach`). The proof: the reachable set is open and so is its complement in
  `U` (`reach_succ_of_mem_ball`, a segment perturbation by compactness), so it contains the component.
* **Segments off a separable closed set** (`disjoint_segment_closure_range_iff`): `[p, p']` misses
  `closure (range f)` iff the distances of the points `f i` to the rational points of the segment are bounded below
  by one `1/(m + 1)`.
* **The closed left side is closed** when the seed-ray closure is (`isClosed_closedLeftSide`), and its points are
  the seed-ray closure and the points reached from the base point (`mem_closedLeftSide_iff`).
* Measurability of these conditions in parameters (`measurableSet_reach`, `measurableSet_mem_closure_range`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Topology Filter MeasureTheory

namespace InteractingSLE

namespace Theorem15D5

/-! ### Rational points -/

/-- The rational point `q.1 + q.2 i` of `ℂ`. -/
def ratPt (q : ℚ × ℚ) : ℂ := ⟨q.1, q.2⟩

theorem exists_ratPt_dist_lt (x : ℂ) {ε : ℝ} (hε : 0 < ε) : ∃ q : ℚ × ℚ, dist (ratPt q) x < ε := by
  obtain ⟨a, ha₁, ha₂⟩ := exists_rat_btwn (show x.re - ε / 2 < x.re + ε / 2 by linarith)
  obtain ⟨b, hb₁, hb₂⟩ := exists_rat_btwn (show x.im - ε / 4 < x.im + ε / 4 by linarith)
  refine ⟨(a, b), ?_⟩
  rw [Complex.dist_eq]
  calc ‖ratPt (a, b) - x‖ ≤ |(ratPt (a, b) - x).re| + |(ratPt (a, b) - x).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ < ε / 2 + ε / 2 := by
        apply add_lt_add
        · simp only [ratPt, Complex.sub_re]
          rw [abs_lt]; constructor <;> linarith
        · simp only [ratPt, Complex.sub_im]
          rw [abs_lt]; constructor <;> linarith
    _ = ε := by ring

/-- Segments are compact. -/
theorem isCompact_segment_complex (p z : ℂ) : IsCompact (segment ℝ p z) := by
  rw [segment_eq_image']
  exact isCompact_Icc.image (by fun_prop)

/-! ### Polygonal reachability -/

/-- `Reach U w k z`: `z` is reached from `w` by `k + 1` segments contained in `U`, all of whose intermediate
vertices are rational points. -/
def Reach (U : Set ℂ) (w : ℂ) : ℕ → ℂ → Prop
  | 0, z => segment ℝ w z ⊆ U
  | k + 1, z => ∃ q : ℚ × ℚ, Reach U w k (ratPt q) ∧ segment ℝ (ratPt q) z ⊆ U

theorem reach_zero {U : Set ℂ} {w z : ℂ} : Reach U w 0 z ↔ segment ℝ w z ⊆ U := Iff.rfl

theorem reach_succ {U : Set ℂ} {w z : ℂ} {k : ℕ} :
    Reach U w (k + 1) z ↔ ∃ q : ℚ × ℚ, Reach U w k (ratPt q) ∧ segment ℝ (ratPt q) z ⊆ U := Iff.rfl

/-- A reachable point lies in `U`. -/
theorem Reach.mem {U : Set ℂ} {w z : ℂ} {k : ℕ} (h : Reach U w k z) : z ∈ U := by
  cases k with
  | zero => exact h (right_mem_segment ℝ w z)
  | succ k =>
    obtain ⟨q, -, hq⟩ := h
    exact hq (right_mem_segment ℝ _ z)

/-- **Segment perturbation**: if `[p, z] ⊆ U` with `U` open, then `[p, y] ⊆ U` for all `y` near `z`. -/
theorem exists_segment_subset_of_near {U : Set ℂ} (hU : IsOpen U) {p z : ℂ} (h : segment ℝ p z ⊆ U) :
    ∃ δ > 0, ∀ y : ℂ, dist y z < δ → segment ℝ p y ⊆ U := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_segment_complex p z).exists_thickening_subset_open hU h
  refine ⟨δ, hδ, fun y hy x hx => hsub ?_⟩
  rw [segment_eq_image'] at hx
  obtain ⟨θ, hθ, rfl⟩ := hx
  rw [mem_thickening_iff]
  refine ⟨p + θ • (z - p), by rw [segment_eq_image']; exact ⟨θ, hθ, rfl⟩, ?_⟩
  rw [dist_eq_norm]
  have : p + θ • (y - p) - (p + θ • (z - p)) = θ • (y - z) := by
    simp only [smul_sub]; abel
  rw [this, norm_smul, Real.norm_of_nonneg hθ.1, ← dist_eq_norm]
  calc θ * dist y z ≤ 1 * dist y z := by gcongr; exact hθ.2
    _ < δ := by rw [one_mul]; exact hy

/-- The endpoint of a reachable point can be perturbed. -/
theorem Reach.exists_near {U : Set ℂ} (hU : IsOpen U) {w z : ℂ} {k : ℕ} (h : Reach U w k z) :
    ∃ δ > 0, ∀ y : ℂ, dist y z < δ → Reach U w k y := by
  cases k with
  | zero => exact exists_segment_subset_of_near hU h
  | succ k =>
    obtain ⟨q, hq, hseg⟩ := h
    obtain ⟨δ, hδ, hnear⟩ := exists_segment_subset_of_near hU hseg
    exact ⟨δ, hδ, fun y hy => ⟨q, hq, hnear y hy⟩⟩

/-- **The key step**: if `z''` is reachable in `k` steps and lies in a ball `B(z, ε) ⊆ U`, then `z` is reachable in
`k + 1` steps (through a rational point near `z''`). -/
theorem reach_succ_of_mem_ball {U : Set ℂ} (hU : IsOpen U) {w z z'' : ℂ} {ε : ℝ} {k : ℕ}
    (h : Reach U w k z'') (hz'' : z'' ∈ ball z ε) (hball : ball z ε ⊆ U) : Reach U w (k + 1) z := by
  obtain ⟨δ, hδ, hnear⟩ := h.exists_near hU
  obtain ⟨ε', hε', hε'sub⟩ := Metric.isOpen_ball.mem_nhds hz'' |> Metric.mem_nhds_iff.mp
  obtain ⟨q, hq⟩ := exists_ratPt_dist_lt z'' (lt_min hδ hε')
  have hqb : ratPt q ∈ ball z ε := hε'sub (mem_ball.mpr (hq.trans_le (min_le_right _ _)))
  refine ⟨q, hnear _ (hq.trans_le (min_le_left _ _)), ?_⟩
  exact ((convex_ball z ε).segment_subset hqb (mem_ball_self (pos_of_mem_ball hqb))).trans hball

/-- A reachable point is in the component of the start. -/
theorem Reach.mem_connectedComponentIn {U : Set ℂ} {w z : ℂ} {k : ℕ} (h : Reach U w k z) :
    z ∈ connectedComponentIn U w := by
  induction k generalizing z with
  | zero =>
    exact (convex_segment w z).isPreconnected.subset_connectedComponentIn (left_mem_segment ℝ w z) h
      (right_mem_segment ℝ w z)
  | succ k ih =>
    obtain ⟨q, hq, hseg⟩ := h
    have hqC := ih hq
    rw [connectedComponentIn_eq hqC]
    exact (convex_segment _ z).isPreconnected.subset_connectedComponentIn (left_mem_segment ℝ _ z) hseg
      (right_mem_segment ℝ _ z)

/-- **Components of open sets by rational polygonal paths.** -/
theorem mem_connectedComponentIn_iff_exists_reach {U : Set ℂ} (hU : IsOpen U) {w z : ℂ} :
    z ∈ connectedComponentIn U w ↔ ∃ k, Reach U w k z := by
  refine ⟨fun hz => ?_, fun ⟨k, hk⟩ => hk.mem_connectedComponentIn⟩
  have hw : w ∈ U := connectedComponentIn_nonempty_iff.mp ⟨z, hz⟩
  set V : Set ℂ := {y | ∃ k, Reach U w k y} with hV
  have hVo : IsOpen V := by
    rw [Metric.isOpen_iff]
    rintro y ⟨k, hk⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU y hk.mem
    refine ⟨ε / 2, half_pos hε, fun y' hy' => ⟨k + 1, reach_succ_of_mem_ball (ε := ε / 2) hU hk ?_ ?_⟩⟩
    · rw [mem_ball, dist_comm]; exact mem_ball.mp hy'
    · intro x hx
      apply hball
      rw [mem_ball] at hx hy' ⊢
      calc dist x y ≤ dist x y' + dist y' y := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add hx hy'
        _ = ε := add_halves ε
  have hWo : IsOpen (U \ V) := by
    rw [Metric.isOpen_iff]
    rintro y ⟨hyU, hyV⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU y hyU
    refine ⟨ε / 2, half_pos hε, fun y' hy' => ⟨hball (ball_subset_ball (half_le_self hε.le) hy'), ?_⟩⟩
    rintro ⟨k, hk⟩
    exact hyV ⟨k + 1, reach_succ_of_mem_ball hU hk (ball_subset_ball (half_le_self hε.le) hy') hball⟩
  have hsub : connectedComponentIn U w ⊆ V := by
    refine isPreconnected_connectedComponentIn.subset_left_of_subset_union hVo hWo disjoint_sdiff_right
      ?_ ⟨w, mem_connectedComponentIn hw, 0, ?_⟩
    · intro y hy
      by_cases hyV : y ∈ V
      · exact Or.inl hyV
      · exact Or.inr ⟨connectedComponentIn_subset U w hy, hyV⟩
    · show segment ℝ w w ⊆ U
      rw [segment_same]
      exact singleton_subset_iff.mpr hw
  exact hsub hz

/-! ### Segments off a separable closed set -/

/-- The clamp of a real number to `[0, 1]`. -/
def clamp01 (x : ℝ) : ℝ := max 0 (min 1 x)

theorem clamp01_mem (x : ℝ) : clamp01 x ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem abs_clamp01_sub_clamp01_le (x y : ℝ) : |clamp01 x - clamp01 y| ≤ |x - y| := by
  unfold clamp01
  calc |max 0 (min 1 x) - max 0 (min 1 y)| ≤ max |0 - 0| |min 1 x - min 1 y| :=
        abs_max_sub_max_le_max _ _ _ _
    _ ≤ max |0 - 0| (max |1 - 1| |x - y|) := max_le_max le_rfl (abs_min_sub_min_le_max _ _ _ _)
    _ = |x - y| := by simp

theorem abs_clamp01_sub_le {x θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) : |clamp01 x - θ| ≤ |x - θ| := by
  have h1 : clamp01 θ = θ := by
    unfold clamp01; rw [min_eq_right hθ.2, max_eq_right hθ.1]
  have := abs_clamp01_sub_clamp01_le x θ
  rwa [h1] at this

/-- The point of the segment `[p, p']` with clamped parameter `λ`. -/
def segPt (p p' : ℂ) (r : ℚ) : ℂ := p + (clamp01 r : ℝ) • (p' - p)

theorem segPt_mem (p p' : ℂ) (r : ℚ) : segPt p p' r ∈ segment ℝ p p' := by
  rw [segment_eq_image']
  exact ⟨_, clamp01_mem r, rfl⟩

/-- **A segment misses `closure (range f)`** iff the points `f i` stay at distance at least one `1/(m + 1)` from
the rational points of the segment. -/
theorem disjoint_segment_closure_range_iff {ι : Type*} (f : ι → ℂ) (p p' : ℂ) :
    Disjoint (segment ℝ p p') (closure (range f)) ↔
      ∃ m : ℕ, ∀ i (r : ℚ), 1 / ((m : ℝ) + 1) ≤ dist (f i) (segPt p p' r) := by
  constructor
  · intro hdis
    obtain ⟨δ, hδ, hsub⟩ := (isCompact_segment_complex p p').exists_thickening_subset_open
      isClosed_closure.isOpen_compl (subset_compl_iff_disjoint_right.mpr hdis)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    refine ⟨m, fun i r => ?_⟩
    by_contra hlt
    push Not at hlt
    have hmem : f i ∈ thickening δ (segment ℝ p p') :=
      mem_thickening_iff.mpr ⟨_, segPt_mem p p' r, hlt.trans hm⟩
    exact hsub hmem (subset_closure (mem_range_self i))
  · rintro ⟨m, hm⟩
    rw [Set.disjoint_left]
    intro x hx hxc
    rw [segment_eq_image'] at hx
    obtain ⟨θ, hθ, rfl⟩ := hx
    set ε : ℝ := 1 / ((m : ℝ) + 1) with hε
    have hεpos : 0 < ε := by positivity
    obtain ⟨i, hi⟩ := mem_closure_range_iff.mp hxc (ε / 2) (half_pos hεpos)
    set η : ℝ := ε / (2 * (‖p' - p‖ + 1)) with hη
    have hηpos : 0 < η := by positivity
    obtain ⟨r, hr₁, hr₂⟩ := exists_rat_btwn (show θ - η < θ + η by linarith)
    have hrθ : |(r : ℝ) - θ| < η := by rw [abs_lt]; constructor <;> linarith
    have hcl : |clamp01 r - θ| < η := (abs_clamp01_sub_le hθ).trans_lt hrθ
    have hd : dist (p + θ • (p' - p)) (segPt p p' r) ≤ η * ‖p' - p‖ := by
      rw [segPt, dist_eq_norm]
      have : p + θ • (p' - p) - (p + clamp01 r • (p' - p)) = (θ - clamp01 r) • (p' - p) := by
        rw [sub_smul]; abel
      rw [this, norm_smul, Real.norm_eq_abs, abs_sub_comm]
      exact mul_le_mul_of_nonneg_right hcl.le (norm_nonneg _)
    have hηn : η * ‖p' - p‖ < ε / 2 := by
      rw [hη, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg (p' - p)]
    have := hm i r
    have htri := dist_triangle (f i) (p + θ • (p' - p)) (segPt p p' r)
    rw [dist_comm] at hi
    linarith

/-! ### The closed left side -/

/-- **The closed left side is closed** when the seed-ray closure is: the closure of the component `C` of the
complement adds only points of the seed-ray closure (components of open sets are open). -/
theorem isClosed_closedLeftSide {γ : NNReal → ℂ} (hF : IsClosed (seedRayClosure γ)) :
    IsClosed (closedLeftSide γ) := by
  unfold closedLeftSide
  rw [← closure_subset_iff_isClosed, closure_union, hF.closure_eq]
  rintro x (hx | hx)
  · by_cases hxF : x ∈ seedRayClosure γ
    · exact Or.inr hxF
    · left
      obtain ⟨y, hyx, hyC⟩ := mem_closure_iff.mp hx _ (hF.isOpen_compl.connectedComponentIn)
        (mem_connectedComponentIn hxF)
      rw [connectedComponentIn_eq hyC, ← connectedComponentIn_eq hyx]
      exact mem_connectedComponentIn hxF
  · exact Or.inr hx

/-- Points of the closed left side: the seed-ray closure, and the points reached from the base point
`γ 0 − 1 − i` by rational polygonal paths off it. -/
theorem mem_closedLeftSide_iff {γ : NNReal → ℂ} (hF : IsClosed (seedRayClosure γ)) {z : ℂ} :
    z ∈ closedLeftSide γ ↔
      z ∈ seedRayClosure γ ∨ ∃ k, Reach (seedRayClosure γ)ᶜ (γ 0 - 1 - Complex.I) k z := by
  unfold closedLeftSide
  rw [mem_union, mem_connectedComponentIn_iff_exists_reach hF.isOpen_compl, or_comm]

/-! ### Measurability in parameters -/

section Measurable

variable {X : Type*} [MeasurableSpace X] {ι : Type*} [Countable ι]

/-- "`[p, p']` misses `closure (range f)`" is measurable in measurable parameters. -/
theorem measurableSet_disjoint_segment {f : X → ι → ℂ} (hf : ∀ i, Measurable fun x => f x i) {p p' : X → ℂ}
    (hp : Measurable p) (hp' : Measurable p') :
    MeasurableSet {x | Disjoint (segment ℝ (p x) (p' x)) (closure (range (f x)))} := by
  have hset : {x | Disjoint (segment ℝ (p x) (p' x)) (closure (range (f x)))} =
      ⋃ m : ℕ, ⋂ i, ⋂ r : ℚ, {x | 1 / ((m : ℝ) + 1) ≤ dist (f x i) (segPt (p x) (p' x) r)} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter]
    exact disjoint_segment_closure_range_iff (f x) (p x) (p' x)
  rw [hset]
  refine MeasurableSet.iUnion fun m => MeasurableSet.iInter fun i => MeasurableSet.iInter fun r => ?_
  have hseg : Measurable fun x => segPt (p x) (p' x) r := by
    unfold segPt
    fun_prop
  exact measurableSet_le measurable_const ((hf i).dist hseg)

/-- Membership in `closure (range f)` is measurable in measurable parameters. -/
theorem measurableSet_mem_closure_range {f : X → ι → ℂ} (hf : ∀ i, Measurable fun x => f x i) {z : X → ℂ}
    (hz : Measurable z) : MeasurableSet {x | z x ∈ closure (range (f x))} := by
  have hset : {x | z x ∈ closure (range (f x))} =
      ⋂ m : ℕ, ⋃ i, {x | dist (z x) (f x i) < 1 / ((m : ℝ) + 1)} := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, mem_closure_range_iff]
    constructor
    · intro h m
      exact h _ (by positivity)
    · intro h ε hε
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
      obtain ⟨i, hi⟩ := h m
      exact ⟨i, hi.trans hm⟩
  rw [hset]
  exact MeasurableSet.iInter fun m => MeasurableSet.iUnion fun i =>
    measurableSet_lt (hz.dist (hf i)) measurable_const

/-- **Polygonal reachability off `closure (range f)` is measurable** in measurable parameters. -/
theorem measurableSet_reach {f : X → ι → ℂ} (hf : ∀ i, Measurable fun x => f x i) {w : X → ℂ}
    (hw : Measurable w) (k : ℕ) {z : X → ℂ} (hz : Measurable z) :
    MeasurableSet {x | Reach (closure (range (f x)))ᶜ (w x) k (z x)} := by
  induction k generalizing z with
  | zero =>
    simp only [reach_zero, subset_compl_iff_disjoint_right]
    exact measurableSet_disjoint_segment hf hw hz
  | succ k ih =>
    simp only [reach_succ, subset_compl_iff_disjoint_right, ofPred_exists]
    exact MeasurableSet.iUnion fun q =>
      (ih measurable_const).inter (measurableSet_disjoint_segment hf measurable_const hz)

end Measurable

end Theorem15D5

end InteractingSLE
