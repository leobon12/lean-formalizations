import HigherDimLQGContinuity.MetricVersion.Barrier
import HigherDimLQGMetric.Metric.Internal

/-!
# Metric-valued versions (packet E5): `metricVersion_of`

Part C, Theorem `c:thm-metric` before the median normalization (interface `MetricVersionStmt`, IA1 §5, rulings N11,
N20): for `d ≥ 3`, a pairing frame `F` and any family `X` with `PosVersionStmt d X`, almost surely every member
`X(ξ)(g)`, `ξ ∈ S_d`, is a continuous length metric (`metricVersion_of`). The almost-sure event is the intersection of
the invariant good event of `weyl_translates_ae` (continuity in `ξ`, length metrics at the rational parameters), the
positivity of `ae_forall_pos_version` (`c:lem-opt-nondeg`, `c:lem-opt-metric`) and the barriers of
`ae_barrier_version` (`c:lem-opt-proper`); on it the deterministic core `mv_metric_of_family` applies.

Also proved, on the same kind of event: the Euclidean topology (`ae_euclidean_of_small_version`), properness and exact
midpoints at every parameter (`ae_isLength_version`, the full statement of `c:lem-opt-geod`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Every positive subcritical parameter lies in the interior of a rational window contained in `S_d`. -/
theorem mv_exists_rat_window (hd : 2 ≤ d) {ξ : ℝ} (hξ : ξ ∈ subcritSet d) :
    ∃ c c' : ℚ, (c : ℝ) < ξ ∧ ξ < c' ∧ Icc (c : ℝ) c' ⊆ subcritSet d := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (mv_isOpen_subcritSet hd) ξ hξ
  obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn (show ξ - δ / 2 < ξ by linarith)
  obtain ⟨c', hc'1, hc'2⟩ := exists_rat_btwn (show ξ < ξ + δ / 2 by linarith)
  refine ⟨c, c', hc2, hc'1, fun t ht => hball ?_⟩
  rw [mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [ht.1, ht.2]

/-- The almost-sure event of the packet: on it, every member of the family is a continuous length metric and
`(ℝ^d, X(ξ)(g))` is proper. -/
theorem ae_metric_proper_version (hd : 3 ≤ d) (F : PairingFrame d) {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)}
    (hX : PosVersionStmt d X) :
    ∀ᵐ g ∂(normLGFLaw d), ∀ ξ ∈ subcritSet d,
      ∃ M : ContMetric d, M.1 = X ξ g ∧ M.IsLength ∧ ProperSpace M.Space := by
  have hd2 : 2 ≤ d := by omega
  obtain ⟨E, -, hEae, -, hcont, hrat, -⟩ := weyl_translates_ae hd F hX
  filter_upwards [hEae, ae_forall_pos_version hd F hX, ae_barrier_version hd F hX] with g hgE hpos hbar
  refine mv_metric_of_family (mv_isOpen_subcritSet hd2) (hcont g hgE) (hrat g hgE) hpos fun ξ hξ => ?_
  obtain ⟨c, c', hc1, hc2, hJ⟩ := mv_exists_rat_window hd2 hξ
  exact ⟨c, c', hc1, hc2, hJ, hbar c c' (hc1.trans hc2) hJ⟩

/-- **`c:lem-opt-proper`**, the barrier at points: almost surely, for every rational window `[c, c'] ⊆ S_d`,
`inf_{ξ ∈ [c, c']} X(ξ)(g)(0, y) → ∞` as `|y| → ∞` (in the form: for every `L` there is `R` with
`X(ξ)(g)(0, y) > L` for `|y| ≥ R` and all `ξ` of the window). The windows `W_n` of `exists_window_exhaustion` have
rational ends. -/
theorem ae_barrier_point_version (hd : 3 ≤ d) (F : PairingFrame d) {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)}
    (hX : PosVersionStmt d X) :
    ∀ᵐ g ∂(normLGFLaw d), ∀ c c' : ℚ, (c : ℝ) < c' → Icc (c : ℝ) c' ⊆ subcritSet d → ∀ L : ℝ,
      ∃ R : ℝ, ∀ ξ ∈ Icc (c : ℝ) c', ∀ y : Rd d, R ≤ ‖y‖ → L < X ξ g (0, y) := by
  obtain ⟨E, -, hEae, -, hcont, hrat, -⟩ := weyl_translates_ae hd F hX
  filter_upwards [hEae, ae_barrier_version hd F hX] with g hgE hbar c c' hcc hJ
  exact mv_point_barrier (mv_isOpen_subcritSet (by omega)) (hcont g hgE) (hrat g hgE) hJ (hbar c c' hcc hJ)

/-- **`c:lem-opt-proper`**, the Euclidean topology: almost surely, for every positive subcritical `ξ`, small
`X(ξ)(g)`-distances force small Euclidean distances. -/
theorem ae_euclidean_of_small_version (hd : 3 ≤ d) (F : PairingFrame d)
    {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)} (hX : PosVersionStmt d X) :
    ∀ᵐ g ∂(normLGFLaw d), ∀ ξ ∈ subcritSet d,
      ∀ x : Rd d, ∀ ε > 0, ∃ δ > 0, ∀ y : Rd d, X ξ g (x, y) < δ → ‖x - y‖ < ε := by
  have hd2 : 2 ≤ d := by omega
  obtain ⟨E, -, hEae, -, hcont, hrat, -⟩ := weyl_translates_ae hd F hX
  filter_upwards [hEae, ae_forall_pos_version hd F hX] with g hgE hpos ξ hξ
  exact mv_euclidean_of_small (mv_isOpen_subcritSet hd2) (hcont g hgE) (hrat g hgE) hpos hξ

/-- Exact midpoints in a proper length metric (the midpoint of a geodesic, `ContMetric.exists_geodesic`). -/
theorem mv_exists_midpoint {M : ContMetric d} (hL : M.IsLength) [ProperSpace M.Space] (x y : Rd d) :
    ∃ z : Rd d, M.1 (x, z) = M.1 (x, y) / 2 ∧ M.1 (z, y) = M.1 (x, y) / 2 := by
  obtain ⟨P, h0, h1, -, -, hP⟩ := M.exists_geodesic hL x y
  set D := M.1 (x, y) with hD
  have hD0 : 0 ≤ D := M.nonneg x y
  have hm : D / 2 ∈ Icc (0 : ℝ) D := ⟨by linarith, by linarith⟩
  refine ⟨P (D / 2), ?_, ?_⟩
  · have := hP 0 ⟨le_rfl, hD0⟩ (D / 2) hm
    rw [h0, sub_zero, abs_of_nonneg (by linarith)] at this
    exact this
  · have := hP (D / 2) hm D ⟨hD0, le_rfl⟩
    rw [h1, abs_of_nonneg (by linarith)] at this
    rw [this]
    ring

/-- **`c:lem-opt-geod`**: almost surely, for every positive subcritical `ξ`, `X(ξ)(g)` is a proper continuous length
metric in which any two points have an exact midpoint. -/
theorem ae_isLength_version (hd : 3 ≤ d) (F : PairingFrame d) {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)}
    (hX : PosVersionStmt d X) :
    ∀ᵐ g ∂(normLGFLaw d), ∀ ξ ∈ subcritSet d, ∃ M : ContMetric d, M.1 = X ξ g ∧ M.IsLength ∧
      ProperSpace M.Space ∧
        ∀ x y : Rd d, ∃ z : Rd d, X ξ g (x, z) = X ξ g (x, y) / 2 ∧ X ξ g (z, y) = X ξ g (x, y) / 2 := by
  filter_upwards [ae_metric_proper_version hd F hX] with g hg ξ hξ
  obtain ⟨M, hM, hL, hP⟩ := hg ξ hξ
  refine ⟨M, hM, hL, hP, fun x y => ?_⟩
  obtain ⟨z, hz1, hz2⟩ := mv_exists_midpoint hL x y
  rw [hM] at hz1 hz2
  exact ⟨z, hz1, hz2⟩

/-- **`metricVersion_of`** (packet E5, interface `MetricVersionStmt`, IA1 §5): for `d ≥ 3`, a pairing frame and any
family with `PosVersionStmt d X`, almost surely every member `X(ξ)(g)` of the positive-parameter family is a continuous
length metric. -/
theorem metricVersion_of {d : ℕ} (hd : 3 ≤ d) (F : PairingFrame d)
    {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)} (hX : PosVersionStmt d X) : MetricVersionStmt d X := by
  filter_upwards [ae_metric_proper_version hd F hX] with g hg ξ hξ hQ
  obtain ⟨M, hM, hL, -⟩ := hg ξ ⟨hξ, hQ⟩
  exact ⟨M, hM, hL⟩

end HigherDimLQGContinuity
