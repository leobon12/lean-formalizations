import HigherDimLQGMetric.DGZ.Functionals

/-!
# Continuity of internal LFPP distances (packet L3b1)

Source: MA7 (`planning/audits/MA7-ref2-sections-4-6.md`) §5 row L3b1 and Details (a) D-6.1–D-6.3
("continuity of `(x, y) ↦ D_n(x, y; U)` on `U × U`: L3b1"), D-6.9 and the junk-value note of
`normMetricC` (Details (c) §F: "continuity of the LFPP metric of a continuous field is a lemma of
packet L3b").

* `pcwJoined_of_isPreconnected`: two points of an open preconnected set `V ⊆ ℝ^d` are joined inside
  `V` by a piecewise `C¹` path (locally by segments in balls; `IsPreconnected.induction₂`).
* `exists_lfppDistOn_le_mul_dist`: the local Lipschitz bound `D_V(x, x') ≤ M |x' - x|` for `x'`
  in a ball around `x ∈ V` (segment in a ball inside `V`, `M = max e^{ξ φ}` on its closure).
* **`continuousOn_lfppDistOn`** (target): for open preconnected `V` and continuous `φ`,
  `(x, y) ↦ D_V(x, y)` is continuous on `V × V`; with the triangle inequality
  `|D(x, y) - D(x₀, y₀)| ≤ D(x₀, x) + D(y₀, y) ≤ M_x |x - x₀| + M_y |y - y₀|`.
* `continuous_lfppMetric`: the whole-space metric of a continuous field is continuous on
  `ℝ^d × ℝ^d`; `continuousOn_lfppDistOn_left/right` (one variable fixed).
* `abs_lfppDistOn_sub_le`: the two-point Lipschitz-type comparison used above;
  `lfppDistOn_triangle_of_isPreconnected`, `lfppDistOn_mono_of_isPreconnected` (no joinability
  hypotheses in open preconnected sets).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP

variable {d : ℕ} {ξ : ℝ} {φ : Rd d → ℝ} {V : Set (Rd d)}

/-- Two points of an open preconnected set are joined inside it by a piecewise `C¹` path. -/
theorem pcwJoined_of_isPreconnected (hV : IsOpen V) (hVc : IsPreconnected V) {x y : Rd d}
    (hx : x ∈ V) (hy : y ∈ V) : PcwJoined V x y := by
  refine hVc.induction₂ (PcwJoined V) (fun x hx => ?_) (fun x y z _ _ _ h₁ h₂ => h₁.trans h₂)
    (fun x y _ _ h => h.symm) hx hy
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV x hx
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds x hε)] with y hy
  exact (PcwJoined.of_convex (convex_ball x ε) (Metric.mem_ball_self hε) hy).mono hball

/-- **Triangle inequality in an open preconnected set** (no joinability hypotheses). -/
theorem lfppDistOn_triangle_of_isPreconnected (hV : IsOpen V) (hVc : IsPreconnected V)
    (hφ : Continuous φ) {x y z : Rd d} (hx : x ∈ V) (hy : y ∈ V) (hz : z ∈ V) :
    lfppDistOn ξ φ V x z ≤ lfppDistOn ξ φ V x y + lfppDistOn ξ φ V y z :=
  lfppDistOn_triangle hφ (pcwJoined_of_isPreconnected hV hVc hx hy)
    (pcwJoined_of_isPreconnected hV hVc hy hz)

/-- **Monotonicity in the domain from an open preconnected set**: `D_W ≤ D_V` on `V ⊆ W`. -/
theorem lfppDistOn_mono_of_isPreconnected (hV : IsOpen V) (hVc : IsPreconnected V)
    {W : Set (Rd d)} (hVW : V ⊆ W) {x y : Rd d} (hx : x ∈ V) (hy : y ∈ V) :
    lfppDistOn ξ φ W x y ≤ lfppDistOn ξ φ V x y :=
  lfppDistOn_mono hVW (pcwJoined_of_isPreconnected hV hVc hx hy)

/-- **Local Lipschitz bound**: around every point `x` of an open set `V` there is a ball on which
`D_V(x, x') ≤ M |x' - x|`. -/
theorem exists_lfppDistOn_le_mul_dist (hV : IsOpen V) (hφ : Continuous φ) (ξ : ℝ) {x : Rd d}
    (hx : x ∈ V) : ∃ ε > 0, ∃ M, 0 ≤ M ∧
      ∀ x' ∈ Metric.ball x ε, lfppDistOn ξ φ V x x' ≤ M * dist x' x := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV x hx
  obtain ⟨m, hm⟩ := (isCompact_closedBall x ε).bddAbove_image
    (continuous_const.mul hφ).continuousOn
  have hconv : Convex ℝ (Metric.ball x ε) := convex_ball x ε
  have hxb : x ∈ Metric.ball x ε := Metric.mem_ball_self hε
  refine ⟨ε, hε, Real.exp m, (Real.exp_pos m).le, fun x' hx' => ?_⟩
  calc lfppDistOn ξ φ V x x' ≤ lfppDistOn ξ φ (Metric.ball x ε) x x' :=
        lfppDistOn_mono hball (PcwJoined.of_convex hconv hxb hx')
    _ ≤ Real.exp m * ‖x' - x‖ :=
        lfppDistOn_le_exp_mul_norm_of_convex hφ hconv hxb hx' fun z hz =>
          hm ⟨z, Metric.ball_subset_closedBall hz, rfl⟩
    _ = Real.exp m * dist x' x := by rw [dist_eq_norm]

/-- **Two-point comparison**: for points joined in `V`,
`|D_V(x, y) - D_V(x₀, y₀)| ≤ D_V(x₀, x) + D_V(y₀, y)`. -/
theorem abs_lfppDistOn_sub_le (hφ : Continuous φ) {x y x₀ y₀ : Rd d}
    (hj : ∀ p ∈ ({x, y, x₀, y₀} : Set (Rd d)), ∀ q ∈ ({x, y, x₀, y₀} : Set (Rd d)),
      PcwJoined V p q) :
    |lfppDistOn ξ φ V x y - lfppDistOn ξ φ V x₀ y₀| ≤
      lfppDistOn ξ φ V x₀ x + lfppDistOn ξ φ V y₀ y := by
  have mx : x ∈ ({x, y, x₀, y₀} : Set (Rd d)) := by simp
  have my : y ∈ ({x, y, x₀, y₀} : Set (Rd d)) := by simp
  have mx₀ : x₀ ∈ ({x, y, x₀, y₀} : Set (Rd d)) := by simp
  have my₀ : y₀ ∈ ({x, y, x₀, y₀} : Set (Rd d)) := by simp
  have h1 : lfppDistOn ξ φ V x y ≤
      lfppDistOn ξ φ V x x₀ + lfppDistOn ξ φ V x₀ y₀ + lfppDistOn ξ φ V y₀ y := by
    calc lfppDistOn ξ φ V x y ≤ lfppDistOn ξ φ V x y₀ + lfppDistOn ξ φ V y₀ y :=
          lfppDistOn_triangle hφ (hj x mx y₀ my₀) (hj y₀ my₀ y my)
      _ ≤ (lfppDistOn ξ φ V x x₀ + lfppDistOn ξ φ V x₀ y₀) + lfppDistOn ξ φ V y₀ y := by
          gcongr
          exact lfppDistOn_triangle hφ (hj x mx x₀ mx₀) (hj x₀ mx₀ y₀ my₀)
  have h2 : lfppDistOn ξ φ V x₀ y₀ ≤
      lfppDistOn ξ φ V x₀ x + lfppDistOn ξ φ V x y + lfppDistOn ξ φ V y y₀ := by
    calc lfppDistOn ξ φ V x₀ y₀ ≤ lfppDistOn ξ φ V x₀ y + lfppDistOn ξ φ V y y₀ :=
          lfppDistOn_triangle hφ (hj x₀ mx₀ y my) (hj y my y₀ my₀)
      _ ≤ (lfppDistOn ξ φ V x₀ x + lfppDistOn ξ φ V x y) + lfppDistOn ξ φ V y y₀ := by
          gcongr
          exact lfppDistOn_triangle hφ (hj x₀ mx₀ x mx) (hj x mx y my)
  rw [lfppDistOn_comm ξ φ V x x₀] at h1
  rw [lfppDistOn_comm ξ φ V y y₀] at h2
  rw [abs_le]
  constructor <;> linarith

/-- **Continuity of internal distances** (MA7 §5 row L3b1; D-6.3): for an open preconnected
`V ⊆ ℝ^d` and a continuous field `φ`, `(x, y) ↦ D_V(x, y)(φ)` is continuous on `V × V`. -/
theorem continuousOn_lfppDistOn (hV : IsOpen V) (hVc : IsPreconnected V) (hφ : Continuous φ)
    (ξ : ℝ) : ContinuousOn (fun p : Rd d × Rd d => lfppDistOn ξ φ V p.1 p.2) (V ×ˢ V) := by
  rintro ⟨x₀, y₀⟩ hp
  obtain ⟨hx₀, hy₀⟩ : x₀ ∈ V ∧ y₀ ∈ V := hp
  obtain ⟨εx, hεx, Mx, hMx, hx⟩ := exists_lfppDistOn_le_mul_dist hV hφ ξ hx₀
  obtain ⟨εy, hεy, My, hMy, hy⟩ := exists_lfppDistOn_le_mul_dist hV hφ ξ hy₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set δ := min (min εx εy) (ε / (Mx + My + 1)) with hδ
  have hδpos : 0 < δ := lt_min (lt_min hεx hεy) (div_pos hε (by linarith))
  refine ⟨δ, hδpos, ?_⟩
  rintro ⟨x, y⟩ hp' hdist
  obtain ⟨hx', hy'⟩ : x ∈ V ∧ y ∈ V := hp'
  have hdx : dist x x₀ < δ :=
    lt_of_le_of_lt (le_max_left _ _) (by rwa [Prod.dist_eq] at hdist)
  have hdy : dist y y₀ < δ :=
    lt_of_le_of_lt (le_max_right _ _) (by rwa [Prod.dist_eq] at hdist)
  have hδx : δ ≤ εx := (min_le_left _ _).trans (min_le_left _ _)
  have hδy : δ ≤ εy := (min_le_left _ _).trans (min_le_right _ _)
  have hδε : δ ≤ ε / (Mx + My + 1) := min_le_right _ _
  have hj : ∀ p ∈ ({x, y, x₀, y₀} : Set (Rd d)), ∀ q ∈ ({x, y, x₀, y₀} : Set (Rd d)),
      PcwJoined V p q := by
    have hsub : ({x, y, x₀, y₀} : Set (Rd d)) ⊆ V := by
      intro p hp
      simp only [mem_insert_iff, mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> assumption
    exact fun p hp q hq => pcwJoined_of_isPreconnected hV hVc (hsub hp) (hsub hq)
  have hbx := hx x (Metric.mem_ball.2 (hdx.trans_le hδx))
  have hby := hy y (Metric.mem_ball.2 (hdy.trans_le hδy))
  have habs := abs_lfppDistOn_sub_le (ξ := ξ) hφ hj
  rw [Real.dist_eq]
  have h1 : Mx * dist x x₀ ≤ Mx * δ := mul_le_mul_of_nonneg_left hdx.le hMx
  have h2 : My * dist y y₀ ≤ My * δ := mul_le_mul_of_nonneg_left hdy.le hMy
  have h3 : (Mx + My) * δ < ε := by
    calc (Mx + My) * δ ≤ (Mx + My) * (ε / (Mx + My + 1)) :=
          mul_le_mul_of_nonneg_left hδε (by linarith)
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
          nlinarith
  calc |lfppDistOn ξ φ V x y - lfppDistOn ξ φ V x₀ y₀|
      ≤ lfppDistOn ξ φ V x₀ x + lfppDistOn ξ φ V y₀ y := habs
    _ ≤ Mx * dist x x₀ + My * dist y y₀ := add_le_add hbx hby
    _ < ε := by nlinarith

/-- Continuity in the second variable on `V` (first variable fixed in `V`). -/
theorem continuousOn_lfppDistOn_right (hV : IsOpen V) (hVc : IsPreconnected V)
    (hφ : Continuous φ) (ξ : ℝ) {x : Rd d} (hx : x ∈ V) :
    ContinuousOn (fun y => lfppDistOn ξ φ V x y) V :=
  (continuousOn_lfppDistOn hV hVc hφ ξ).comp (continuousOn_const.prodMk continuousOn_id)
    fun _ hy => ⟨hx, hy⟩

/-- Continuity in the first variable on `V` (second variable fixed in `V`). -/
theorem continuousOn_lfppDistOn_left (hV : IsOpen V) (hVc : IsPreconnected V)
    (hφ : Continuous φ) (ξ : ℝ) {y : Rd d} (hy : y ∈ V) :
    ContinuousOn (fun x => lfppDistOn ξ φ V x y) V :=
  (continuousOn_lfppDistOn hV hVc hφ ξ).comp (continuousOn_id.prodMk continuousOn_const)
    fun _ hx => ⟨hx, hy⟩

/-- **Continuity of the whole-space LFPP metric** of a continuous field. -/
theorem continuous_lfppMetric (hφ : Continuous φ) (ξ : ℝ) :
    Continuous fun p : Rd d × Rd d => lfppMetric ξ φ p.1 p.2 := by
  have h := continuousOn_lfppDistOn isOpen_univ convex_univ.isPreconnected hφ ξ
  rw [univ_prod_univ] at h
  exact continuousOn_univ.1 h

end HigherDimLQGMetric.DGZ
