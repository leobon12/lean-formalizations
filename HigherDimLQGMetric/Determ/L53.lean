import HigherDimLQGMetric.Determ.PerD

/-! Determination of an internal ball distance by all cell observations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open LQGMetric.MetricGeometry
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

variable {d : ℕ}

theorem determ_l53_core {D D' : ContMetric d} {c : ℝ} (hc : 0 ≤ c)
    (hle : ∀ x y : (Rd d), D'.1 (x, y) ≤ c * D.1 (x, y)) {ε R : ℝ} (hε : 0 < ε) {θ : Fin d → ℝ}
    (hθ : θ ∈ determUnitShift d) {P : ℝ → (Rd d)} (hP : Continuous P)
    (hfin : D.len P 0 1 ≠ ⊤) (hPR : MapsTo P (Icc 0 1) (Metric.closedBall 0 R)) {m : ℕ}
    {z w : (Rd d)} (hPm : MapsTo P (Icc 0 1) (Metric.ball 0 (m : ℝ))) (hP0 : P 0 = z) (hP1 : P 1 = w)
    (hnull : LQGMetric.LM.t17LenMeas (D.pt ∘ P) 0 1 (Icc 0 1 ∩ P ⁻¹' determGrid ε θ) = 0)
    (hS : ∀ k ∈ determFixedBox ε R, ∀ u ∈ determCube ε θ k, ∀ v ∈ determCube ε θ k,
      D.internal (determCube ε θ k) u v = D'.internal (determCube ε θ k) u v) :
    determF m z w D' ≤ D.len P 0 1 := by
  obtain ⟨-, -, hs', hs, hfin'⟩ := determ_resample hc hle hε hθ hP
    zero_le_one hfin hPR hnull (k₀ := fun _ => 0) (fun k hk _ => hS k hk)
  have hcurve : LQGMetric.LM.T17Curve (D.pt ∘ P) 0 1 :=
    ⟨zero_le_one, D.continuous_pt.comp_continuousOn hP.continuousOn, hfin⟩
  have hcurve' : LQGMetric.LM.T17Curve (D'.pt ∘ P) 0 1 :=
    ⟨zero_le_one, D'.continuous_pt.comp_continuousOn hP.continuousOn, hfin'⟩
  have heq : D'.len P 0 1 = D.len P 0 1 := by
    have hsum : ∑ k ∈ determFixedBox ε R, determPiece D' P 0 1 ε θ k =
        ∑ k ∈ determFixedBox ε R, determPiece D P 0 1 ε θ k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      unfold determPiece
      rw [determ_lenMeas_eq_of_internal_eq (determ_isOpen_cube ε θ k)
        (hS k hk) hP.continuousOn hcurve hcurve']
    rw [← ENNReal.ofReal_toReal hfin', ← ENNReal.ofReal_toReal hfin, hs', hs, hsum]
  rw [← heq]
  refine (D'.chainInf_le_internal Metric.isOpen_ball z w).trans ?_
  have := internalEDist_le_curveLength (X := D'.Space) (Y := D'.pt '' Metric.ball 0 (m : ℝ))
    (P := D'.pt ∘ P) zero_le_one (D'.continuous_pt.comp_continuousOn hP.continuousOn)
    (fun t ht => ⟨P t, hPm ht, rfl⟩)
  rw [← hP0, ← hP1]
  exact this

/-- **LM Lemma 5.3, per metric** (l. 975–986): for a length metric `d` and `‖z‖, ‖w‖ < m ≤ R`,
for a.e. `θ ∈ [0,1]²`, every `d' ≤ c d` with the same internal metrics as `d` on all squares of
`determFixedBox ε R` has `d'(z,w;B_m) ≤ d(z,w;B_m)`. -/
theorem determ_l53_perD {D : ContMetric d} (hD : D.IsLength) {c : ℝ} (hc : 0 ≤ c) {m : ℕ} {R : ℝ}
    (hmR : (m : ℝ) ≤ R) {z w : (Rd d)} (hz : ‖z‖ < m) (hw : ‖w‖ < m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ θ ∂(volume : Measure (Fin d → ℝ)), θ ∈ determUnitShift d →
      ∀ D' : ContMetric d, (∀ x y : (Rd d), D'.1 (x, y) ≤ c * D.1 (x, y)) →
        (∀ k ∈ determFixedBox ε R, ∀ u ∈ determCube ε θ k, ∀ v ∈ determCube ε θ k,
          D.internal (determCube ε θ k) u v = D'.internal (determCube ε θ k) u v) →
        determF m z w D' ≤ determF m z w D := by
  have hzm : z ∈ Metric.ball (0 : (Rd d)) (m : ℝ) := mem_ball_zero_iff.2 hz
  have hwm : w ∈ Metric.ball (0 : (Rd d)) (m : ℝ) := mem_ball_zero_iff.2 hw
  have hI : D.internal (Metric.ball 0 (m : ℝ)) z w ≠ ⊤ :=
    D.internal_ne_top_of_isPreconnected hD Metric.isOpen_ball (convex_ball _ _).isPreconnected hzm hwm
  have e : determF m z w D = D.internal (Metric.ball 0 (m : ℝ)) z w :=
    (D.internal_eq_chainInf hD Metric.isOpen_ball z w).symm
  have hδ : ∀ j : ℕ, (0 : ℝ) < 1 / ((j : ℝ) + 1) := fun j => by positivity
  choose P hPc hP0 hP1 hPm hPl using fun j : ℕ => determ_near_path D hI (hδ j)
  have hg : ∀ j, ∀ᵐ θ ∂(volume : Measure (Fin d → ℝ)),
      LQGMetric.LM.t17LenMeas (D.pt ∘ P j) 0 1 {t | P j t ∈ determGrid ε θ} = 0 := fun j =>
    @determ_grid_null d ε hε (P j) (hPc j).measurable _
      (determ_sfinite_lenMeas D (P j) 0 1)
  filter_upwards [ae_all_iff.2 hg] with θ hθ hθunit D' hle hS
  refine ENNReal.le_of_forall_pos_le_add fun δ hδpos _ => ?_
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt (show (0 : ℝ) < δ from hδpos)
  have hfin : D.len (P j) 0 1 ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hI, ENNReal.ofReal_ne_top⟩) (hPl j)
  have hPR : MapsTo (P j) (Icc 0 1) (Metric.closedBall 0 R) := fun t ht =>
    Metric.closedBall_subset_closedBall hmR (Metric.ball_subset_closedBall (hPm j ht))
  have h1 := determ_l53_core hc hle hε hθunit (hPc j) hfin hPR (hPm j) (hP0 j) (hP1 j)
    (measure_mono_null inter_subset_right (hθ j)) hS
  calc determF m z w D' ≤ D.len (P j) 0 1 := h1
    _ ≤ D.internal (Metric.ball 0 (m : ℝ)) z w + ENNReal.ofReal (1 / ((j : ℝ) + 1)) := hPl j
    _ ≤ determF m z w D + δ := by
        rw [e]
        refine add_le_add le_rfl (ENNReal.ofReal_le_of_le_toReal ?_)
        rw [ENNReal.coe_toReal]
        exact hj.le

end HigherDimLQGMetric
