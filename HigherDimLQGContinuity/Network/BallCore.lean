import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGMetric.Metric.Internal
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Local diameter estimates for open ball networks

The source's Lemma 4.2 bounds intrinsic distances in a finite union of
overlapping open balls. This module records the local consequence of the
doubled-ball upper reference that is used in the radial and graph chains.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)
open HigherDimLQGMetric
open scoped ENNReal

namespace HigherDimLQGContinuity

/-- A doubled-ball reference bounds any two points of its inner ball in a
larger domain containing the double ball. -/
theorem q4_internal_le_of_doubled_ball {d : ℕ} (D : ContMetric d)
    {W U : Set (Rd d)} {H σ ρ : ℝ} {z x y : Rd d}
    (hup : DUpper D W H σ) (hρ : 0 < ρ)
    (hW : closedBall z (2 * ρ) ⊆ W)
    (hU : ball z (2 * ρ) ⊆ U)
    (hx : x ∈ ball z ρ) (hy : y ∈ ball z ρ) :
    D.internal U x y ≤ ENNReal.ofReal (H * ρ ^ σ) := by
  calc
    D.internal U x y ≤ D.internal (ball z (2 * ρ)) x y := D.internal_anti hU x y
    _ ≤ diamIn D (ball z (2 * ρ)) (ball z ρ) := by
      unfold diamIn
      exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy le_rfl)
    _ ≤ ENNReal.ofReal (H * ρ ^ σ) := hup z ρ hρ hW

/-- Distances along a radial line, with the scalar displayed explicitly. -/
private theorem q4_radial_dist {d : ℕ} (q x : Rd d) (a b : ℝ) :
    dist (q + a • (x - q)) (q + b • (x - q)) = |a - b| * dist q x := by
  rw [dist_eq_norm, show q + a • (x - q) - (q + b • (x - q)) =
      (a - b) • (x - q) by module, norm_smul, Real.norm_eq_abs, dist_eq_norm]
  rw [norm_sub_rev]

/-- The dyadic radial points approach the endpoint from the ball centre. -/
private def q4_radial {d : ℕ} (q x : Rd d) (n : ℕ) : Rd d :=
  q + (1 - (1 / 2 : ℝ) ^ n) • (x - q)

/-- A centre for a doubled ball containing two successive radial points. -/
private def q4_radialCentre {d : ℕ} (q x : Rd d) (n : ℕ) : Rd d :=
  q + (1 - 3 / 4 * (1 / 2 : ℝ) ^ n) • (x - q)

/-- Radius of the doubled-ball reference at radial scale `n`. -/
private def q4_radialRadius {d : ℕ} (q x : Rd d) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ n * dist q x / 3

private theorem q4_radialRadius_pos {d : ℕ} {q x : Rd d} (hqx : q ≠ x) (n : ℕ) :
    0 < q4_radialRadius q x n := by
  unfold q4_radialRadius
  exact div_pos (mul_pos (by positivity) (dist_pos.mpr hqx)) (by norm_num)

private theorem q4_radial_step {d : ℕ} {q x : Rd d} (hqx : q ≠ x) (n : ℕ) :
    q4_radial q x n ∈ ball (q4_radialCentre q x n) (q4_radialRadius q x n) ∧
    q4_radial q x (n + 1) ∈
      ball (q4_radialCentre q x n) (q4_radialRadius q x n) := by
  have hpow : 0 < (1 / 2 : ℝ) ^ n := by positivity
  have hdist : 0 < dist q x := dist_pos.mpr hqx
  constructor
  · rw [mem_ball, q4_radial, q4_radialCentre, q4_radial_dist]
    unfold q4_radialRadius
    have h : |(1 - (1 / 2 : ℝ) ^ n) - (1 - 3 / 4 * (1 / 2 : ℝ) ^ n)| =
        (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n := by
      rw [abs_of_nonpos (by nlinarith)]
      ring
    rw [h]
    nlinarith
  · rw [mem_ball, q4_radial, q4_radialCentre, q4_radial_dist]
    unfold q4_radialRadius
    rw [pow_succ]
    have h : |(1 - (1 / 2 : ℝ) ^ n * (1 / 2)) -
        (1 - 3 / 4 * (1 / 2 : ℝ) ^ n)| =
        (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n := by
      rw [abs_of_nonneg (by nlinarith)]
      ring
    rw [h]
    nlinarith

/-- Each doubled ball used by the radial chain stays inside the original ball. -/
private theorem q4_radial_double_subset {d : ℕ} {q x : Rd d} {t : ℝ}
    (hx : x ∈ ball q t) (n : ℕ) :
    closedBall (q4_radialCentre q x n) (2 * q4_radialRadius q x n) ⊆ ball q t := by
  have hp0 : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  have hp1 : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hdist : dist q x < t := by simpa only [mem_ball, dist_comm] using hx
  have hcenter : dist q (q4_radialCentre q x n) =
      (1 - 3 / 4 * (1 / 2 : ℝ) ^ n) * dist q x := by
    rw [q4_radialCentre]
    conv_lhs => arg 1; rw [show q = q + (0 : ℝ) • (x - q) by simp]
    rw [q4_radial_dist, abs_of_nonpos (by nlinarith)]
    ring
  intro y hy
  rw [mem_closedBall] at hy
  rw [mem_ball]
  rw [dist_comm y q]
  rw [dist_comm y (q4_radialCentre q x n)] at hy
  have htri := dist_triangle q (q4_radialCentre q x n) y
  have hbound : dist q (q4_radialCentre q x n) +
      2 * q4_radialRadius q x n ≤ dist q x := by
    rw [hcenter]
    unfold q4_radialRadius
    nlinarith [dist_nonneg (x := q) (y := x)]
  exact lt_of_le_of_lt (le_trans htri (le_trans (add_le_add_right hy _) hbound)) hdist

private theorem q4_radial_tendsto {d : ℕ} (q x : Rd d) :
    Filter.Tendsto (q4_radial q x) Filter.atTop (nhds x) := by
  have hp : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hs : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n • (x - q))
      Filter.atTop (nhds 0) := by
    simpa only [zero_smul] using hp.smul_const (x - q)
  have h := (tendsto_const_nhds (x := x)).sub hs
  convert h using 1
  · funext n
    simp only [q4_radial]
    module
  · simp

private theorem q4_radial_mem_ball {d : ℕ} {q x : Rd d} {t : ℝ}
    (hqx : q ≠ x) (hx : x ∈ ball q t) (n : ℕ) :
    q4_radial q x n ∈ ball q t := by
  have hr := q4_radialRadius_pos hqx n
  have hstep := (q4_radial_step hqx n).1
  apply q4_radial_double_subset hx n
  exact Metric.closedBall_subset_closedBall (by linarith : q4_radialRadius q x n ≤
    2 * q4_radialRadius q x n) (Metric.ball_subset_closedBall hstep)

private theorem q4_radial_step_bound {d : ℕ} (D : ContMetric d)
    {W : Set (Rd d)} {H σ t : ℝ} {q x : Rd d}
    (hup : DUpper D W H σ) (hqx : q ≠ x)
    (hx : x ∈ ball q t) (hW : closedBall q t ⊆ W) (n : ℕ) :
    D.internal (ball q t) (q4_radial q x n) (q4_radial q x (n + 1)) ≤
      ENNReal.ofReal H * ENNReal.ofReal ((q4_radialRadius q x n) ^ σ) := by
  have hr := q4_radialRadius_pos hqx n
  have hsub := q4_radial_double_subset hx n
  have hW' : closedBall (q4_radialCentre q x n)
      (2 * q4_radialRadius q x n) ⊆ W :=
    hsub.trans (Metric.ball_subset_closedBall.trans hW)
  have hstep := q4_radial_step hqx n
  calc
    _ ≤ ENNReal.ofReal (H * (q4_radialRadius q x n) ^ σ) :=
      q4_internal_le_of_doubled_ball D hup hr hW'
        (Metric.ball_subset_closedBall.trans hsub) hstep.1 hstep.2
    _ = ENNReal.ofReal H * ENNReal.ofReal ((q4_radialRadius q x n) ^ σ) := by
      rw [mul_comm H, ENNReal.ofReal_mul (Real.rpow_nonneg hr.le σ), mul_comm]

private theorem q4_radial_chain_bound {d : ℕ} (D : ContMetric d)
    {W : Set (Rd d)} {H σ t : ℝ} {q x : Rd d}
    (hup : DUpper D W H σ) (hqx : q ≠ x)
    (hx : x ∈ ball q t) (hW : closedBall q t ⊆ W) (n : ℕ) :
    D.internal (ball q t) q (q4_radial q x n) ≤
      ENNReal.ofReal H *
        ∑ j ∈ Finset.range n, ENNReal.ofReal ((q4_radialRadius q x j) ^ σ) := by
  induction n with
  | zero =>
      have ht : 0 < t := lt_of_le_of_lt (dist_nonneg) (by simpa only [mem_ball] using hx)
      simp only [q4_radial, pow_zero, sub_self, zero_smul, add_zero,
        D.internal_self (mem_ball_self ht), Finset.range_zero, Finset.sum_empty,
        mul_zero, le_refl]
  | succ n ih =>
      calc
        D.internal (ball q t) q (q4_radial q x (n + 1)) ≤
            D.internal (ball q t) q (q4_radial q x n) +
              D.internal (ball q t) (q4_radial q x n) (q4_radial q x (n + 1)) :=
          D.internal_triangle _ _ _ _
        _ ≤ ENNReal.ofReal H *
              ∑ j ∈ Finset.range n, ENNReal.ofReal ((q4_radialRadius q x j) ^ σ) +
            ENNReal.ofReal H * ENNReal.ofReal ((q4_radialRadius q x n) ^ σ) :=
          add_le_add ih (q4_radial_step_bound D hup hqx hx hW n)
        _ = ENNReal.ofReal H *
              ∑ j ∈ Finset.range (n + 1), ENNReal.ofReal ((q4_radialRadius q x j) ^ σ) := by
          rw [Finset.sum_range_succ, mul_add]

private theorem q4_radial_cost_sum_le {d : ℕ} {q x : Rd d} {t σ : ℝ}
    (hx : x ∈ ball q t) (hσ : 0 < σ) (n : ℕ) :
    (∑ j ∈ Finset.range n, ENNReal.ofReal ((q4_radialRadius q x j) ^ σ)) ≤
      ENNReal.ofReal (t ^ σ / (1 - (1 / 2 : ℝ) ^ σ)) := by
  let a : ℝ := (1 / 2 : ℝ) ^ σ
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hσ
  have hden : 0 < 1 - a := by linarith
  have hdist : dist q x < t := by simpa only [mem_ball, dist_comm] using hx
  have ht : 0 < t := lt_of_le_of_lt dist_nonneg hdist
  have hbase : (dist q x / 3) ^ σ ≤ t ^ σ :=
    Real.rpow_le_rpow (by positivity) (by linarith [dist_nonneg (x := q) (y := x)]) hσ.le
  have hterm (j : ℕ) : (q4_radialRadius q x j) ^ σ =
      (dist q x / 3) ^ σ * a ^ j := by
    unfold q4_radialRadius
    rw [show (1 / 2 : ℝ) ^ j * dist q x / 3 =
        (dist q x / 3) * (1 / 2 : ℝ) ^ j by ring,
      Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    exact (Real.rpow_pow_comm (by norm_num) σ j).symm
  have hsum : (∑ j ∈ Finset.range n, (q4_radialRadius q x j) ^ σ) ≤
      t ^ σ / (1 - a) := by
    simp_rw [hterm]
    rw [← Finset.mul_sum]
    have hgeom := (summable_geometric_of_lt_one ha0 ha1).sum_le_tsum
      (Finset.range n) (fun j _ => pow_nonneg ha0 j)
    rw [tsum_geometric_of_lt_one ha0 ha1] at hgeom
    have hbase0 : 0 ≤ (dist q x / 3) ^ σ := by positivity
    calc
      (dist q x / 3) ^ σ * ∑ j ∈ Finset.range n, a ^ j ≤
          (dist q x / 3) ^ σ * (1 - a)⁻¹ :=
        mul_le_mul_of_nonneg_left hgeom hbase0
      _ ≤ t ^ σ * (1 - a)⁻¹ :=
        mul_le_mul_of_nonneg_right hbase (inv_nonneg.mpr hden.le)
      _ = t ^ σ / (1 - a) := by ring
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ =>
    Real.rpow_nonneg (by unfold q4_radialRadius; positivity) σ)]
  exact ENNReal.ofReal_le_ofReal (by simpa only [a] using hsum)

/-- The radial chain gives a uniform bound from the centre to any point of an
open ball whose closure lies in the reference domain. -/
theorem q4_internal_center_ball_le {d : ℕ} (D : ContMetric d)
    {W : Set (Rd d)} {H σ t : ℝ} {q x : Rd d}
    (hup : DUpper D W H σ) (hσ : 0 < σ)
    (hx : x ∈ ball q t) (hW : closedBall q t ⊆ W) :
    D.internal (ball q t) q x ≤
      2 * (ENNReal.ofReal H *
        ENNReal.ofReal (t ^ σ / (1 - (1 / 2 : ℝ) ^ σ))) := by
  have ht : 0 < t := lt_of_le_of_lt dist_nonneg
    (by simpa only [mem_ball] using hx)
  have hq : q ∈ ball q t := mem_ball_self ht
  by_cases hqx : q = x
  · subst x
    simp only [D.internal_self hq, zero_le]
  let ρ : ℝ := (t - dist q x) / 4
  have hρ : 0 < ρ := by
    dsimp [ρ]
    have := (show dist q x < t by simpa only [mem_ball, dist_comm] using hx)
    linarith
  have hρt : ρ ≤ t := by
    dsimp [ρ]
    nlinarith [dist_nonneg (x := q) (y := x)]
  have hdouble : closedBall x (2 * ρ) ⊆ ball q t := by
    intro z hz
    rw [mem_ball, dist_comm z q]
    have htri := dist_triangle q x z
    have hzx : dist x z ≤ 2 * ρ := by simpa only [mem_closedBall, dist_comm] using hz
    have hqx' : dist q x < t := by simpa only [mem_ball, dist_comm] using hx
    dsimp [ρ] at *
    linarith
  have hnear : ∀ᶠ n : ℕ in Filter.atTop, q4_radial q x n ∈ ball x ρ :=
    (q4_radial_tendsto q x).eventually (isOpen_ball.mem_nhds (mem_ball_self hρ))
  obtain ⟨n, hn⟩ := hnear.exists
  let u : ℝ := t ^ σ / (1 - (1 / 2 : ℝ) ^ σ)
  have hden : 0 < 1 - (1 / 2 : ℝ) ^ σ := sub_pos.mpr
    (Real.rpow_lt_one (by norm_num) (by norm_num) hσ)
  have hρu : ρ ^ σ ≤ u := by
    have hpow : ρ ^ σ ≤ t ^ σ := Real.rpow_le_rpow hρ.le hρt hσ.le
    dsimp [u]
    have htp : 0 ≤ t ^ σ := Real.rpow_nonneg ht.le σ
    apply le_trans hpow
    apply (le_div_iff₀ hden).2
    nlinarith [show (1 / 2 : ℝ) ^ σ ≥ 0 by positivity]
  have hchain : D.internal (ball q t) q (q4_radial q x n) ≤
      ENNReal.ofReal H * ENNReal.ofReal u :=
    (q4_radial_chain_bound D hup hqx hx hW n).trans
      (by simpa only [mul_comm] using
        (mul_le_mul_right (q4_radial_cost_sum_le hx hσ n) (ENNReal.ofReal H)))
  have htail : D.internal (ball q t) (q4_radial q x n) x ≤
      ENNReal.ofReal H * ENNReal.ofReal u := by
    have h := q4_internal_le_of_doubled_ball D hup hρ
      (hdouble.trans (Metric.ball_subset_closedBall.trans hW))
      (Metric.ball_subset_closedBall.trans hdouble) hn (mem_ball_self hρ)
    rw [mul_comm H, ENNReal.ofReal_mul (Real.rpow_nonneg hρ.le σ), mul_comm] at h
    exact h.trans (by simpa only [mul_comm] using
      (mul_le_mul_right (ENNReal.ofReal_le_ofReal hρu) (ENNReal.ofReal H)))
  calc
    D.internal (ball q t) q x ≤
        D.internal (ball q t) q (q4_radial q x n) +
          D.internal (ball q t) (q4_radial q x n) x :=
      D.internal_triangle _ _ _ _
    _ ≤ (ENNReal.ofReal H * ENNReal.ofReal u) +
          (ENNReal.ofReal H * ENNReal.ofReal u) := add_le_add hchain htail
    _ = 2 * (ENNReal.ofReal H * ENNReal.ofReal u) := by ring

/-- Uniform internal diameter of one open ball, using radial chains from its
centre. The coefficient is finite for every positive exponent. -/
theorem q4_internal_ball_le {d : ℕ} (D : ContMetric d)
    {W : Set (Rd d)} {H σ t : ℝ} {q x y : Rd d}
    (hup : DUpper D W H σ) (hσ : 0 < σ)
    (hx : x ∈ ball q t) (hy : y ∈ ball q t)
    (hW : closedBall q t ⊆ W) :
    D.internal (ball q t) x y ≤
      ENNReal.ofReal ((4 / (1 - (1 / 2 : ℝ) ^ σ)) * H * t ^ σ) := by
  let u : ℝ := t ^ σ / (1 - (1 / 2 : ℝ) ^ σ)
  have ht : 0 < t := lt_of_le_of_lt dist_nonneg
    (by simpa only [mem_ball] using hx)
  have hden : 0 < 1 - (1 / 2 : ℝ) ^ σ := sub_pos.mpr
    (Real.rpow_lt_one (by norm_num) (by norm_num) hσ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hconvert : ENNReal.ofReal H * ENNReal.ofReal u = ENNReal.ofReal (u * H) := by
    rw [ENNReal.ofReal_mul hu, mul_comm]
  calc
    D.internal (ball q t) x y ≤
        D.internal (ball q t) x q + D.internal (ball q t) q y :=
      D.internal_triangle _ _ _ _
    _ ≤ 2 * (ENNReal.ofReal H * ENNReal.ofReal u) +
          2 * (ENNReal.ofReal H * ENNReal.ofReal u) := by
      apply add_le_add
      · rw [D.internal_comm]
        exact q4_internal_center_ball_le D hup hσ hx hW
      · exact q4_internal_center_ball_le D hup hσ hy hW
    _ = ENNReal.ofReal ((4 / (1 - (1 / 2 : ℝ) ^ σ)) * H * t ^ σ) := by
      have hfour : (2 : ℝ≥0∞) * (ENNReal.ofReal H * ENNReal.ofReal u) +
          2 * (ENNReal.ofReal H * ENNReal.ofReal u) =
          4 * (ENNReal.ofReal H * ENNReal.ofReal u) := by ring
      rw [hfour, hconvert]
      have hfourReal : (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) := by norm_num
      rw [hfourReal, ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (4 : ℝ))]
      congr 1
      dsimp [u]
      ring

/-- The internal triangle inequality transports local bounds along a simple
path in an overlap graph. Each ball is charged only once. -/
private theorem q4_path_internal_bound {d : ℕ} {V : Type*} [DecidableEq V]
    (D : ContMetric d) (U : Set (Rd d)) (G : SimpleGraph V)
    (B : V → Set (Rd d)) (C : V → ℝ≥0∞)
    (hlocal : ∀ i, ∀ x ∈ B i, ∀ y ∈ B i, D.internal U x y ≤ C i)
    (hoverlap : ∀ i j, G.Adj i j → (B i ∩ B j).Nonempty)
    {a b : V} (p : G.Walk a b) :
    p.IsPath → ∀ x ∈ B a, ∀ y ∈ B b,
      D.internal U x y ≤ ∑ i ∈ p.support.toFinset, C i := by
  induction p with
  | nil =>
      intro _ x hx y hy
      simpa only [SimpleGraph.Walk.support_nil, List.toFinset_cons,
        List.toFinset_nil, Finset.insert_empty, Finset.sum_singleton] using
        hlocal _ x hx y hy
  | @cons u v w hadj p ih =>
      intro hp x hx y hy
      obtain ⟨hptail, hunot⟩ := (SimpleGraph.Walk.cons_isPath_iff hadj p).mp hp
      obtain ⟨z, hzu, hzv⟩ := hoverlap u v hadj
      have hhead := hlocal u x hx z hzu
      have htail := ih hptail z hzv y hy
      have hnot : u ∉ p.support.toFinset := by
        simpa only [List.mem_toFinset] using hunot
      calc
        D.internal U x y ≤ D.internal U x z + D.internal U z y :=
          D.internal_triangle U x z y
        _ ≤ C u + ∑ i ∈ p.support.toFinset, C i := add_le_add hhead htail
        _ = ∑ i ∈ (SimpleGraph.Walk.cons hadj p).support.toFinset, C i := by
          rw [SimpleGraph.Walk.support_cons, List.toFinset_cons, Finset.sum_insert hnot]

/-- Lemma 4.2's open-ball core: a connected overlap graph gives a uniform
internal diameter bound, with each ball charged once. -/
theorem internal_le_union_balls {d : ℕ} {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : ContMetric d),
      ∀ {W : Set (Rd d)} {H : ℝ}, DUpper D W H σ →
      ∀ (n : ℕ) (q : Fin n → Rd d) (t : Fin n → ℝ),
        (∀ i, 0 < t i) →
        (∀ i, closedBall (q i) (t i) ⊆ W) →
        (SimpleGraph.fromRel (fun i j : Fin n =>
          (ball (q i) (t i) ∩ ball (q j) (t j)).Nonempty)).Connected →
        ∀ x ∈ ⋃ i, ball (q i) (t i), ∀ y ∈ ⋃ i, ball (q i) (t i),
          D.internal (⋃ i, ball (q i) (t i)) x y ≤
            ENNReal.ofReal (C * H * ∑ i, t i ^ σ) := by
  let C : ℝ := 4 / (1 - (1 / 2 : ℝ) ^ σ)
  have hden : 0 < 1 - (1 / 2 : ℝ) ^ σ := sub_pos.mpr
    (Real.rpow_lt_one (by norm_num) (by norm_num) hσ)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro D W H hup n q t ht hW hconn x hx y hy
  classical
  let U : Set (Rd d) := ⋃ i, ball (q i) (t i)
  let G : SimpleGraph (Fin n) := SimpleGraph.fromRel
    (fun i j => (ball (q i) (t i) ∩ ball (q j) (t j)).Nonempty)
  have hlocal : ∀ i, ∀ u ∈ ball (q i) (t i), ∀ v ∈ ball (q i) (t i),
      D.internal U u v ≤ ENNReal.ofReal (C * H * t i ^ σ) := by
    intro i u hu v hv
    have hsub : ball (q i) (t i) ⊆ U := by
      intro z hz
      exact mem_iUnion.mpr ⟨i, hz⟩
    exact (D.internal_anti hsub u v).trans
      (q4_internal_ball_le D hup hσ hu hv (hW i))
  have hoverlap : ∀ i j, G.Adj i j →
      (ball (q i) (t i) ∩ ball (q j) (t j)).Nonempty := by
    intro i j hij
    rcases (SimpleGraph.fromRel_adj _ i j).mp hij with ⟨_, h | h⟩
    · exact h
    · obtain ⟨z, hzj, hzi⟩ := h
      exact ⟨z, hzi, hzj⟩
  obtain ⟨a, hxa⟩ := mem_iUnion.mp hx
  obtain ⟨b, hyb⟩ := mem_iUnion.mp hy
  obtain ⟨p, hp⟩ := hconn.exists_isPath a b
  have hpath := q4_path_internal_bound D U G
    (fun i => ball (q i) (t i))
    (fun i => ENNReal.ofReal (C * H * t i ^ σ)) hlocal hoverlap p hp x hxa y hyb
  have hsupport : (∑ i ∈ p.support.toFinset,
      ENNReal.ofReal (C * H * t i ^ σ)) ≤
      ∑ i : Fin n, ENNReal.ofReal (C * H * t i ^ σ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => zero_le)
  have hsum : (∑ i : Fin n, ENNReal.ofReal (C * H * t i ^ σ)) =
      ENNReal.ofReal (C * H * ∑ i : Fin n, t i ^ σ) := by
    have hterm (i : Fin n) : ENNReal.ofReal (C * H * t i ^ σ) =
        ENNReal.ofReal (C * H) * ENNReal.ofReal (t i ^ σ) := by
      rw [mul_comm (C * H), ENNReal.ofReal_mul (Real.rpow_nonneg (ht i).le σ), mul_comm]
    simp_rw [hterm]
    rw [← Finset.mul_sum,
      ← ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (ht i).le σ),
      mul_comm (C * H), ENNReal.ofReal_mul (Finset.sum_nonneg
        (fun i _ => Real.rpow_nonneg (ht i).le σ)), mul_comm]
  exact hpath.trans (hsupport.trans (hsum.le))

/-- The same open-ball estimate for an arbitrary finite index type. This
version applies directly to the subtype of a network's finite ball finset. -/
theorem q4_internal_le_fintype_balls {d : ℕ} {ι : Type*} [Fintype ι]
    {σ : ℝ} (hσ : 0 < σ)
    (D : ContMetric d)
    {W : Set (Rd d)} {H : ℝ} (hup : DUpper D W H σ)
    (q : ι → Rd d) (t : ι → ℝ)
    (ht : ∀ i, 0 < t i)
    (hW : ∀ i, closedBall (q i) (t i) ⊆ W)
    (hconn : (SimpleGraph.fromRel (fun i j : ι =>
      (ball (q i) (t i) ∩ ball (q j) (t j)).Nonempty)).Connected)
    (x y : Rd d)
    (hx : x ∈ ⋃ i, ball (q i) (t i))
    (hy : y ∈ ⋃ i, ball (q i) (t i)) :
    D.internal (⋃ i, ball (q i) (t i)) x y ≤
      ENNReal.ofReal ((4 / (1 - (1 / 2 : ℝ) ^ σ)) * H *
        ∑ i, t i ^ σ) := by
  classical
  let C : ℝ := 4 / (1 - (1 / 2 : ℝ) ^ σ)
  let U : Set (Rd d) := ⋃ i, ball (q i) (t i)
  let G : SimpleGraph ι := SimpleGraph.fromRel
    (fun i j => (ball (q i) (t i) ∩ ball (q j) (t j)).Nonempty)
  have hlocal : ∀ i, ∀ u ∈ ball (q i) (t i), ∀ v ∈ ball (q i) (t i),
      D.internal U u v ≤ ENNReal.ofReal (C * H * t i ^ σ) := by
    intro i u hu v hv
    have hsub : ball (q i) (t i) ⊆ U := by
      intro z hz
      exact mem_iUnion.mpr ⟨i, hz⟩
    exact (D.internal_anti hsub u v).trans
      (q4_internal_ball_le D hup hσ hu hv (hW i))
  have hoverlap : ∀ i j, G.Adj i j →
      (ball (q i) (t i) ∩ ball (q j) (t j)).Nonempty := by
    intro i j hij
    rcases (SimpleGraph.fromRel_adj _ i j).mp hij with ⟨_, h | h⟩
    · exact h
    · obtain ⟨z, hzj, hzi⟩ := h
      exact ⟨z, hzi, hzj⟩
  obtain ⟨a, hxa⟩ := mem_iUnion.mp hx
  obtain ⟨b, hyb⟩ := mem_iUnion.mp hy
  obtain ⟨p, hp⟩ := hconn.exists_isPath a b
  have hpath := q4_path_internal_bound D U G
    (fun i => ball (q i) (t i))
    (fun i => ENNReal.ofReal (C * H * t i ^ σ)) hlocal hoverlap p hp x hxa y hyb
  have hsupport : (∑ i ∈ p.support.toFinset,
      ENNReal.ofReal (C * H * t i ^ σ)) ≤
      ∑ i : ι, ENNReal.ofReal (C * H * t i ^ σ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => zero_le)
  have hsum : (∑ i : ι, ENNReal.ofReal (C * H * t i ^ σ)) =
      ENNReal.ofReal (C * H * ∑ i : ι, t i ^ σ) := by
    have hterm (i : ι) : ENNReal.ofReal (C * H * t i ^ σ) =
        ENNReal.ofReal (C * H) * ENNReal.ofReal (t i ^ σ) := by
      rw [mul_comm (C * H), ENNReal.ofReal_mul (Real.rpow_nonneg (ht i).le σ), mul_comm]
    simp_rw [hterm]
    rw [← Finset.mul_sum,
      ← ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (ht i).le σ),
      mul_comm (C * H), ENNReal.ofReal_mul (Finset.sum_nonneg
        (fun i _ => Real.rpow_nonneg (ht i).le σ)), mul_comm]
  exact hpath.trans (hsupport.trans (hsum.le))

end HigherDimLQGContinuity
