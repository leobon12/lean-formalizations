import HigherDimLQGContinuity.MarginalEuclid.HolderMoment
import GaussianLQG.LQG.Euclid.Union

/-! Finite-grid filling for the Euclidean marginal. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The metric value is bounded by the Hölder constant times the Euclidean power. -/
theorem n5_ofReal_metric_le_holder_mul {d : ℕ} (D : ContMetric d)
    {K : Set (Rd d)} {β : ℝ} (_hβ : 0 < β)
    {x y : Rd d} (hx : x ∈ K) (hy : y ∈ K) :
    ENNReal.ofReal (D.1 (x, y)) ≤
      holderConstRd D.1 K β * ENNReal.ofReal (‖x - y‖ ^ β) := by
  by_cases hxy : x = y
  · subst y
    simp [D.apply_self]
  have hd : 0 < ‖x - y‖ ^ β :=
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _
  have h1 := ofReal_div_le_holderConstRd (β := β) D.1 hx hy hxy
  have hmul := mul_le_mul_right h1 (ENNReal.ofReal (‖x - y‖ ^ β))
  rw [mul_comm (ENNReal.ofReal (‖x - y‖ ^ β))
    (ENNReal.ofReal (D.1 (x, y) / ‖x - y‖ ^ β)),
    ← ENNReal.ofReal_mul (div_nonneg (D.nonneg x y) hd.le),
    div_mul_cancel₀ _ (ne_of_gt hd),
    mul_comm (ENNReal.ofReal (‖x - y‖ ^ β)) (holderConstRd D.1 K β)] at hmul
  exact hmul

/-- Four-point metric comparison for the Euclidean error. -/
theorem n5_abs_metric_euclid_sub_le {d : ℕ} (D : ContMetric d)
    (x y u v : Rd d) :
    |D.1 (x, y) - dist x y| ≤
      |D.1 (u, v) - dist u v| + D.1 (x, u) + D.1 (y, v) +
        dist x u + dist y v := by
  have h1 : D.1 (x, y) ≤ D.1 (x, u) + D.1 (u, v) + D.1 (y, v) := by
    have ha := D.apply_triangle x u y
    have hb := D.apply_triangle u v y
    have hc := D.apply_comm v y
    linarith
  have h2 : D.1 (u, v) ≤ D.1 (x, u) + D.1 (x, y) + D.1 (y, v) := by
    have ha := D.apply_triangle u x v
    have hb := D.apply_triangle x y v
    have hc := D.apply_comm u x
    linarith
  have h3 : dist x y ≤ dist x u + dist u v + dist y v := by
    have ha := dist_triangle x u y
    have hb := dist_triangle u v y
    rw [dist_comm v y] at hb
    linarith
  have h4 : dist u v ≤ dist x u + dist x y + dist y v := by
    have ha := dist_triangle u x v
    have hb := dist_triangle x y v
    rw [dist_comm u x] at ha
    linarith
  have ha := le_abs_self (D.1 (u, v) - dist u v)
  have hb := neg_abs_le (D.1 (u, v) - dist u v)
  rw [abs_le]
  constructor <;> linarith

/-- The grid used at scale `s`, with points slightly outside the target ball. -/
def euclidGrid {d : ℕ} (R s : ℝ) : Finset (Rd d) :=
  w3bGrid d 1 (R + 1) (s / (R + 1))

/-- Every point of the target ball has a grid point within `s/8`. -/
theorem exists_euclidGrid_near {d : ℕ} (hd : 1 ≤ d) {R s : ℝ}
    (hR : 1 ≤ R) (hs : 0 < s) (hs1 : s ≤ 1)
    {x : Rd d} (hx : x ∈ closedBall 0 R) :
    ∃ u ∈ euclidGrid R s, ‖x - u‖ ≤ s / 8 := by
  have hR1 : 0 < R + 1 := by linarith
  have hε : 0 < s / (R + 1) := by positivity
  have hε1 : s / (R + 1) ≤ 1 := (div_le_one hR1).2 (by linarith)
  have hx' : ‖x‖ < (1 : ℝ) * (R + 1) := by
    have := mem_closedBall_zero_iff.mp hx
    linarith
  obtain ⟨u, hu, hnear⟩ := w3b_exists_grid_near hd
    (by norm_num : (0 : ℝ) < 1) hR1 hε hε1 hx'
  refine ⟨u, hu, ?_⟩
  convert hnear using 1
  field_simp

/-- Largest error among the finitely many grid pairs. -/
def euclidGridErr {d : ℕ} (D : ContMetric d) (R s : ℝ) : ℝ≥0∞ :=
  ⨆ p ∈ euclidGrid (d := d) R s ×ˢ euclidGrid R s,
    edist (D.1 p) (euclidDistC d p)

/-- Pathwise extension of a grid comparison to the full ball. -/
theorem supDistLU_le_gridErr_add_holder {d : ℕ} (hd : 1 ≤ d)
    (D : ContMetric d) {R s β : ℝ} (hR : 1 ≤ R) (hs : 0 < s)
    (hs1 : s ≤ 1) (hβ : 0 < β) :
    supDistLU d R D.1 (euclidDistC d) ≤
      euclidGridErr D R s +
        2 * holderConstRd D.1 (closedBall 0 (R + 1)) β *
          ENNReal.ofReal ((s / 8) ^ β) + ENNReal.ofReal (s / 4) := by
  unfold supDistLU
  refine iSup₂_le fun p hp => ?_
  obtain ⟨u, hu, hxu⟩ := exists_euclidGrid_near hd hR hs hs1 hp.1
  obtain ⟨v, hv, hyv⟩ := exists_euclidGrid_near hd hR hs hs1 hp.2
  have hxuK : p.1 ∈ closedBall (0 : Rd d) (R + 1) := by
    rw [mem_closedBall_zero_iff]
    have := mem_closedBall_zero_iff.mp hp.1
    linarith
  have hyK : p.2 ∈ closedBall (0 : Rd d) (R + 1) := by
    rw [mem_closedBall_zero_iff]
    have := mem_closedBall_zero_iff.mp hp.2
    linarith
  have huK : u ∈ closedBall (0 : Rd d) (R + 1) := by
    rw [mem_closedBall_zero_iff]
    have h := norm_sub_le p.1 (p.1 - u)
    have hx := mem_closedBall_zero_iff.mp hp.1
    have hs' : s / 8 ≤ 1 := by linarith
    have heq : p.1 - (p.1 - u) = u := by abel
    rw [heq] at h
    linarith
  have hvK : v ∈ closedBall (0 : Rd d) (R + 1) := by
    rw [mem_closedBall_zero_iff]
    have h := norm_sub_le p.2 (p.2 - v)
    have hy := mem_closedBall_zero_iff.mp hp.2
    have hs' : s / 8 ≤ 1 := by linarith
    have heq : p.2 - (p.2 - v) = v := by abel
    rw [heq] at h
    linarith
  have hfour := n5_abs_metric_euclid_sub_le D p.1 p.2 u v
  have hgrid : edist (D.1 (u, v)) (euclidDistC d (u, v)) ≤
      euclidGridErr D R s := by
    exact le_iSup₂ (f := fun p (_ : p ∈ euclidGrid R s ×ˢ euclidGrid R s) =>
      edist (D.1 p) (euclidDistC d p)) (u, v) (Finset.mem_product.mpr ⟨hu, hv⟩)
  have hmetricx := n5_ofReal_metric_le_holder_mul D hβ hxuK huK
  have hmetricy := n5_ofReal_metric_le_holder_mul D hβ hyK hvK
  have hpowx : ENNReal.ofReal (‖p.1 - u‖ ^ β) ≤ ENNReal.ofReal ((s / 8) ^ β) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) hxu hβ.le)
  have hpowy : ENNReal.ofReal (‖p.2 - v‖ ^ β) ≤ ENNReal.ofReal ((s / 8) ^ β) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) hyv hβ.le)
  have hmetricx' := hmetricx.trans (mul_le_mul_right hpowx _)
  have hmetricy' := hmetricy.trans (mul_le_mul_right hpowy _)
  have hDx := D.nonneg p.1 u
  have hDy := D.nonneg p.2 v
  have hreal : |D.1 (p.1, p.2) - dist p.1 p.2| ≤
      |D.1 (u, v) - dist u v| + D.1 (p.1, u) + D.1 (p.2, v) + s / 4 := by
    simp only [dist_eq_norm] at hfour ⊢
    linarith
  rw [edist_dist, Real.dist_eq]
  change ENNReal.ofReal |D.1 (p.1, p.2) - dist p.1 p.2| ≤ _
  have hsum : ENNReal.ofReal (|D.1 (u, v) - dist u v| +
      D.1 (p.1, u) + D.1 (p.2, v) + s / 4) =
      edist (D.1 (u, v)) (euclidDistC d (u, v)) +
      ENNReal.ofReal (D.1 (p.1, u)) + ENNReal.ofReal (D.1 (p.2, v)) +
      ENNReal.ofReal (s / 4) := by
    rw [ENNReal.ofReal_add (add_nonneg (add_nonneg (abs_nonneg _) hDx) hDy)
        (by positivity : 0 ≤ s / 4),
      ENNReal.ofReal_add (add_nonneg (abs_nonneg _) hDx) hDy,
      ENNReal.ofReal_add (abs_nonneg _) hDx]
    simp [edist_dist, Real.dist_eq, euclidDistC]
  calc
    ENNReal.ofReal |D.1 (p.1, p.2) - dist p.1 p.2| ≤
        ENNReal.ofReal (|D.1 (u, v) - dist u v| + D.1 (p.1, u) +
          D.1 (p.2, v) + s / 4) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := hsum
    _ ≤ euclidGridErr D R s + 2 * holderConstRd D.1 (closedBall 0 (R + 1)) β *
          ENNReal.ofReal ((s / 8) ^ β) + ENNReal.ofReal (s / 4) := by
      calc
        _ ≤ (euclidGridErr D R s +
            holderConstRd D.1 (closedBall 0 (R + 1)) β *
              ENNReal.ofReal ((s / 8) ^ β) +
            holderConstRd D.1 (closedBall 0 (R + 1)) β *
              ENNReal.ofReal ((s / 8) ^ β)) + ENNReal.ofReal (s / 4) :=
            add_le_add (add_le_add (add_le_add hgrid hmetricx') hmetricy') le_rfl
        _ = _ := by ring

end HigherDimLQGContinuity
