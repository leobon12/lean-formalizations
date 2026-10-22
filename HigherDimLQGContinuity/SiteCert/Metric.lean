import HigherDimLQGContinuity.Labels.OrderBasic
import Mathlib.Algebra.Order.Field.GeomSum
import HigherDimLQGContinuity.Network.BallCore
import HigherDimLQGContinuity.Forcing.Confinement

/-!
# Deterministic metric facts for the site certificate (packet Q7b)

Source: blueprint Part B, the remark after `b:def-dupper` (diameters of closed balls from the doubled-ball upper
reference), `b:lem-unionballs` (the one-ball radial bound, **without** the length property: a finite dyadic chain and
one last doubled ball, exactly as in the blueprint's proof), and the proof of `b:thm-sitecert`(iv), items (C3), (C5),
(C6), (C9) and (C10)(b)–(c).

* `q7b_diamIn_closedBall_le`: `DUp(G, W, H, σ)` and `B̄_{4ρ}(z) ⊆ W` give `diamIn G W (B̄_ρ(z)) ≤ H (2ρ)^σ`.
* `q7b_internal_center_le`, `q7b_internal_ball_le`: for **any** continuous metric with `DUp(G, W, H, σ)`, `σ > 0`,
  `H ≥ 0` and `B̄_t(q) ⊆ W`: `G(q, x; B_t(q)) ≤ C_σ H t^σ` and `G(x, y; B_t(q)) ≤ 2 C_σ H t^σ` for `x, y ∈ B_t(q)`,
  where `C_σ = siteCS σ = 2^σ + (2^σ - 1)⁻¹`. (Q4's `q4_internal_ball_le` needs the length property; the secondary
  metric of the certificate is not assumed to be a length metric, so this version is needed for (C10)(d).)
* `q7b_exists_mem_ball_near`: a point of `B̄_{g+ς}(c)` is within `2ς` of a point of `B_g(c)` (`0 < ς < g`).
* `q7b_collar_inner`, `q7b_collar_outer`: the collar crossings (C6) from (R3).
* `q7b_closedBall_subset_siteA`: balls of radius `< 1` about collector points lie in `A`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology
open scoped ENNReal
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

variable {d : ℕ}

/-! ## Diameters -/

theorem q7b_diamIn_le {G : ContMetric d} {V A : Set (Rd d)} {c : ℝ≥0∞}
    (h : ∀ x ∈ A, ∀ y ∈ A, G.internal V x y ≤ c) : diamIn G V A ≤ c :=
  iSup₂_le fun x hx => iSup₂_le fun y hy => h x hx y hy

theorem q7b_internal_le_diamIn (G : ContMetric d) {V A : Set (Rd d)} {x y : Rd d} (hx : x ∈ A)
    (hy : y ∈ A) : G.internal V x y ≤ diamIn G V A :=
  le_iSup₂_of_le x hx (le_iSup₂_of_le y hy le_rfl)

theorem q7b_diamIn_mono (G : ContMetric d) (V : Set (Rd d)) {A B : Set (Rd d)} (hAB : A ⊆ B) :
    diamIn G V A ≤ diamIn G V B :=
  q7b_diamIn_le fun _ hx _ hy => q7b_internal_le_diamIn G (hAB hx) (hAB hy)

/-- **Diameter of a closed ball** (remark after `b:def-dupper`): if `DUp(G, W, H, σ)` and `B̄_{4ρ}(z) ⊆ W`, then
`diamIn G W (B̄_ρ(z)) ≤ H (2ρ)^σ`. -/
theorem q7b_diamIn_closedBall_le {G : ContMetric d} {W : Set (Rd d)} {H σ ρ : ℝ} {z : Rd d}
    (hG : DUpper G W H σ) (hρ : 0 < ρ) (hW : closedBall z (4 * ρ) ⊆ W) :
    diamIn G W (closedBall z ρ) ≤ ENNReal.ofReal (H * (2 * ρ) ^ σ) := by
  refine q7b_diamIn_le fun x hx y hy => ?_
  have h2 : (0 : ℝ) < 2 * ρ := by positivity
  have hx' : x ∈ ball z (2 * ρ) := closedBall_subset_ball (by linarith) hx
  have hy' : y ∈ ball z (2 * ρ) := closedBall_subset_ball (by linarith) hy
  have hW' : closedBall z (2 * (2 * ρ)) ⊆ W := by
    rw [show 2 * (2 * ρ) = 4 * ρ by ring]
    exact hW
  exact q4_internal_le_of_doubled_ball G hG h2 hW' (ball_subset_closedBall.trans hW') hx' hy'

/-! ## The one-ball radial bound without the length property -/

private theorem q7b_two_rpow_gt_one {σ : ℝ} (hσ : 0 < σ) : 1 < (2 : ℝ) ^ σ :=
  Real.one_lt_rpow (by norm_num) hσ

/-- `∑_{k < n} (2^{-σ})^{k+1} ≤ (2^σ - 1)⁻¹`. -/
private theorem q7b_geom_bound {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    ∑ k ∈ Finset.range n, ((1 / 2 : ℝ) ^ σ) ^ (k + 1) ≤ ((2 : ℝ) ^ σ - 1)⁻¹ := by
  set r : ℝ := (1 / 2 : ℝ) ^ σ with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have h2 := q7b_two_rpow_gt_one hσ
  have hr_eq : r = ((2 : ℝ) ^ σ)⁻¹ := by
    rw [hr, Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow, one_div]
  have hr1 : r < 1 := by
    rw [hr_eq]
    exact inv_lt_one_of_one_lt₀ h2
  have hsum : ∑ k ∈ Finset.range n, r ^ (k + 1) = ∑ i ∈ Finset.Ico 1 (n + 1), r ^ i := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by simp) fun k _ => ?_
    rw [add_comm]
  rw [hsum]
  refine (geom_sum_Ico_le_of_lt_one hr0 hr1).trans (le_of_eq ?_)
  rw [pow_one, hr_eq]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ σ - 1 := by linarith
  field_simp

/-- **One ball, radial chain** (`b:lem-unionballs`, proof, "one ball"; any continuous metric): if
`DUp(G, W, H, σ)` with `H ≥ 0`, `σ > 0` and `B̄_t(q) ⊆ W`, then `G(q, x; B_t(q)) ≤ C_σ H t^σ` for every
`x ∈ B_t(q)`, with `C_σ = 2^σ + (2^σ - 1)⁻¹`. The chain `x_k = q + (1 - 2^{-k})(x - q)` uses the doubled balls about
the midpoints of `[x_k, x_{k+1}]` with radius `(3/8) 2^{-k} |x - q|`; the last step is one doubled ball about `x`. -/
theorem q7b_internal_center_le {G : ContMetric d} {W : Set (Rd d)} {H σ t : ℝ} {q x : Rd d}
    (hG : DUpper G W H σ) (hH : 0 ≤ H) (hσ : 0 < σ) (hW : closedBall q t ⊆ W)
    (hx : x ∈ ball q t) :
    G.internal (ball q t) q x ≤ ENNReal.ofReal (siteCS σ * H * t ^ σ) := by
  have ht : 0 < t := pos_of_mem_ball hx
  by_cases hxq : x = q
  · subst hxq
    rw [G.internal_self (mem_ball_self ht)]
    exact zero_le
  set w : Rd d := x - q with hw
  set a : ℝ := ‖w‖ with ha
  have ha0 : 0 < a := norm_pos_iff.2 (sub_ne_zero.2 hxq)
  have hat : a < t := by
    rw [mem_ball, dist_eq_norm] at hx
    exact hx
  have hWb : ball q t ⊆ W := ball_subset_closedBall.trans hW
  set p : ℕ → Rd d := fun k => q + (1 - (1 / 2 : ℝ) ^ k) • w with hp
  have hhalf : ∀ k : ℕ, (0 : ℝ) < (1 / 2 : ℝ) ^ k := fun k => by positivity
  have hhalf1 : ∀ k : ℕ, (1 / 2 : ℝ) ^ k ≤ 1 := fun k => pow_le_one₀ (by norm_num) (by norm_num)
  -- one dyadic step
  have hstep : ∀ k : ℕ, G.internal (ball q t) (p k) (p (k + 1)) ≤
      ENNReal.ofReal (H * ((1 / 2 : ℝ) ^ (k + 1) * t) ^ σ) := by
    intro k
    set m : Rd d := q + (1 - 3 / 4 * (1 / 2 : ℝ) ^ k) • w with hm
    set ρ : ℝ := 3 / 8 * (1 / 2 : ℝ) ^ k * a with hρ
    have hk := hhalf k
    have hk1 := hhalf1 k
    have hρ0 : 0 < ρ := by positivity
    have e1 : p k - m = (-(1 / 4 * (1 / 2 : ℝ) ^ k)) • w := by
      simp only [hp, hm]
      module
    have e2 : p (k + 1) - m = (1 / 4 * (1 / 2 : ℝ) ^ k) • w := by
      simp only [hp, hm, pow_succ]
      module
    have e3 : m - q = (1 - 3 / 4 * (1 / 2 : ℝ) ^ k) • w := by
      simp only [hm]
      module
    have hpk : p k ∈ ball m ρ := by
      rw [mem_ball, dist_eq_norm, e1, norm_smul, Real.norm_eq_abs, abs_neg,
        abs_of_pos (by positivity), ← ha, hρ]
      nlinarith
    have hpk1 : p (k + 1) ∈ ball m ρ := by
      rw [mem_ball, dist_eq_norm, e2, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), ← ha, hρ]
      nlinarith
    have hmq : ‖m - q‖ = (1 - 3 / 4 * (1 / 2 : ℝ) ^ k) * a := by
      rw [e3, norm_smul, Real.norm_eq_abs, abs_of_pos (by nlinarith)]
    have hsub : closedBall m (2 * ρ) ⊆ ball q t := by
      intro y hy
      rw [mem_closedBall, dist_eq_norm] at hy
      rw [mem_ball, dist_eq_norm]
      calc ‖y - q‖ = ‖(y - m) + (m - q)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖y - m‖ + ‖m - q‖ := norm_add_le _ _
        _ ≤ 2 * ρ + (1 - 3 / 4 * (1 / 2 : ℝ) ^ k) * a := by rw [hmq]; linarith
        _ = a := by rw [hρ]; ring
        _ < t := hat
    have h1 := q4_internal_le_of_doubled_ball G hG hρ0 (hsub.trans hWb)
      (ball_subset_closedBall.trans hsub) hpk hpk1
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have hρle : ρ ≤ (1 / 2 : ℝ) ^ (k + 1) * t := by
      rw [hρ, pow_succ]
      nlinarith
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hρ0.le hρle hσ.le) hH
  -- the chain
  have hterm : ∀ k : ℕ, 0 ≤ H * ((1 / 2 : ℝ) ^ (k + 1) * t) ^ σ := fun k =>
    mul_nonneg hH (Real.rpow_nonneg (by positivity) _)
  have hchain : ∀ n : ℕ, G.internal (ball q t) q (p n) ≤
      ENNReal.ofReal (∑ k ∈ Finset.range n, H * ((1 / 2 : ℝ) ^ (k + 1) * t) ^ σ) := by
    intro n
    induction n with
    | zero =>
      have hp0 : p 0 = q := by simp [hp]
      rw [hp0, G.internal_self (mem_ball_self ht)]
      exact zero_le
    | succ n ih =>
      calc G.internal (ball q t) q (p (n + 1))
          ≤ G.internal (ball q t) q (p n) + G.internal (ball q t) (p n) (p (n + 1)) :=
            G.internal_triangle _ _ _ _
        _ ≤ ENNReal.ofReal (∑ k ∈ Finset.range n, H * ((1 / 2 : ℝ) ^ (k + 1) * t) ^ σ) +
            ENNReal.ofReal (H * ((1 / 2 : ℝ) ^ (n + 1) * t) ^ σ) := add_le_add ih (hstep n)
        _ = ENNReal.ofReal (∑ k ∈ Finset.range (n + 1), H * ((1 / 2 : ℝ) ^ (k + 1) * t) ^ σ) := by
            rw [Finset.sum_range_succ, ENNReal.ofReal_add (Finset.sum_nonneg fun k _ => hterm k) (hterm n)]
  -- the sum of the chain
  have hsum : ∀ n : ℕ, ∑ k ∈ Finset.range n, H * ((1 / 2 : ℝ) ^ (k + 1) * t) ^ σ ≤
      H * t ^ σ * ((2 : ℝ) ^ σ - 1)⁻¹ := by
    intro n
    have heq : ∀ k : ℕ, H * ((1 / 2 : ℝ) ^ (k + 1) * t) ^ σ = H * t ^ σ * ((1 / 2 : ℝ) ^ σ) ^ (k + 1) := by
      intro k
      rw [Real.mul_rpow (by positivity) ht.le, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
        mul_comm ((k + 1 : ℕ) : ℝ) σ, Real.rpow_mul (by norm_num), Real.rpow_natCast]
      ring
    simp_rw [heq]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (q7b_geom_bound hσ n) (mul_nonneg hH (Real.rpow_nonneg ht.le _))
  -- the last doubled ball
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < (t - a) / (4 * a) by
    have : 0 < t - a := by linarith
    positivity) (show (1 / 2 : ℝ) < 1 by norm_num)
  have hn' : 4 * a * (1 / 2 : ℝ) ^ n < t - a := by
    have h4a : 0 < 4 * a := by positivity
    have := (lt_div_iff₀ h4a).1 hn
    linarith
  set ρ' : ℝ := 2 * (1 / 2 : ℝ) ^ n * a with hρ'
  have hρ'0 : 0 < ρ' := by have := hhalf n; positivity
  have hxp : x - p n = ((1 / 2 : ℝ) ^ n) • w := by
    simp only [hp, hw]
    module
  have hpn : p n ∈ ball x ρ' := by
    rw [mem_ball, dist_comm, dist_eq_norm, hxp, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hhalf n), ← ha, hρ']
    have := hhalf n
    nlinarith
  have hxx : x ∈ ball x ρ' := mem_ball_self hρ'0
  have hsub' : closedBall x (2 * ρ') ⊆ ball q t := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    rw [mem_ball, dist_eq_norm]
    calc ‖y - q‖ = ‖(y - x) + (x - q)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖y - x‖ + ‖x - q‖ := norm_add_le _ _
      _ ≤ 2 * ρ' + a := by rw [← hw, ← ha]; linarith
      _ < t := by rw [hρ']; linarith
  have hlast := q4_internal_le_of_doubled_ball G hG hρ'0 (hsub'.trans hWb)
    (ball_subset_closedBall.trans hsub') hpn hxx
  have hlast' : H * ρ' ^ σ ≤ (2 : ℝ) ^ σ * H * t ^ σ := by
    have hρ't : ρ' ≤ 2 * t := by
      rw [hρ']
      have := hhalf1 n
      have := hhalf n
      nlinarith
    calc H * ρ' ^ σ ≤ H * (2 * t) ^ σ :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hρ'0.le hρ't hσ.le) hH
      _ = (2 : ℝ) ^ σ * H * t ^ σ := by
          rw [Real.mul_rpow (by norm_num) ht.le]
          ring
  have hfin : ∑ k ∈ Finset.range n, H * ((1 / 2 : ℝ) ^ (k + 1) * t) ^ σ + H * ρ' ^ σ ≤
      siteCS σ * H * t ^ σ := by
    have h1 := hsum n
    unfold siteCS
    nlinarith
  calc G.internal (ball q t) q x ≤ G.internal (ball q t) q (p n) + G.internal (ball q t) (p n) x :=
        G.internal_triangle _ _ _ _
    _ ≤ ENNReal.ofReal (∑ k ∈ Finset.range n, H * ((1 / 2 : ℝ) ^ (k + 1) * t) ^ σ) +
        ENNReal.ofReal (H * ρ' ^ σ) := add_le_add (hchain n) hlast
    _ = ENNReal.ofReal (∑ k ∈ Finset.range n, H * ((1 / 2 : ℝ) ^ (k + 1) * t) ^ σ + H * ρ' ^ σ) :=
        (ENNReal.ofReal_add (Finset.sum_nonneg fun k _ => hterm k)
          (mul_nonneg hH (Real.rpow_nonneg hρ'0.le _))).symm
    _ ≤ ENNReal.ofReal (siteCS σ * H * t ^ σ) := ENNReal.ofReal_le_ofReal hfin

/-- **Two points of one ball** (`b:lem-unionballs`, one ball; any continuous metric): `G(x, y; B_t(q)) ≤
2 C_σ H t^σ`. -/
theorem q7b_internal_ball_le {G : ContMetric d} {W : Set (Rd d)} {H σ t : ℝ} {q x y : Rd d}
    (hG : DUpper G W H σ) (hH : 0 ≤ H) (hσ : 0 < σ) (hW : closedBall q t ⊆ W)
    (hx : x ∈ ball q t) (hy : y ∈ ball q t) :
    G.internal (ball q t) x y ≤ ENNReal.ofReal (2 * siteCS σ * H * t ^ σ) := by
  have ht : 0 < t := pos_of_mem_ball hx
  have hC : 0 ≤ siteCS σ * H * t ^ σ :=
    mul_nonneg (mul_nonneg (siteCS_pos hσ).le hH) (Real.rpow_nonneg ht.le _)
  calc G.internal (ball q t) x y ≤ G.internal (ball q t) x q + G.internal (ball q t) q y :=
        G.internal_triangle _ _ _ _
    _ = G.internal (ball q t) q x + G.internal (ball q t) q y := by rw [G.internal_comm _ x q]
    _ ≤ ENNReal.ofReal (siteCS σ * H * t ^ σ) + ENNReal.ofReal (siteCS σ * H * t ^ σ) :=
        add_le_add (q7b_internal_center_le hG hH hσ hW hx) (q7b_internal_center_le hG hH hσ hW hy)
    _ = ENNReal.ofReal (2 * siteCS σ * H * t ^ σ) := by
        rw [← ENNReal.ofReal_add hC hC]
        congr 1
        ring

/-! ## A nearby point of an open ball -/

/-- A point of `B̄_{g+ς}(c)` is within `2ς` of a point of the open ball `B_g(c)` (`0 < ς < g`). -/
theorem q7b_exists_mem_ball_near {c x : Rd d} {g ς : ℝ} (hς : 0 < ς) (hςg : ς < g)
    (hx : x ∈ closedBall c (g + ς)) : ∃ y ∈ ball c g, dist x y ≤ 2 * ς := by
  have hgς : 0 < g + ς := by linarith
  set τ : ℝ := (g - ς) / (g + ς) with hτ
  have hτ0 : 0 ≤ τ := div_nonneg (by linarith) hgς.le
  have hτ1 : 1 - τ = 2 * ς / (g + ς) := by
    rw [hτ]
    field_simp
    ring
  refine ⟨c + τ • (x - c), ?_, ?_⟩
  · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ0]
    rw [mem_closedBall, dist_eq_norm] at hx
    calc τ * ‖x - c‖ ≤ τ * (g + ς) := mul_le_mul_of_nonneg_left hx hτ0
      _ = g - ς := by rw [hτ]; field_simp
      _ < g := by linarith
  · have e : x - (c + τ • (x - c)) = (1 - τ) • (x - c) := by module
    rw [dist_eq_norm, e, norm_smul, Real.norm_eq_abs, hτ1, abs_of_nonneg (by positivity)]
    rw [mem_closedBall, dist_eq_norm] at hx
    calc 2 * ς / (g + ς) * ‖x - c‖ ≤ 2 * ς / (g + ς) * (g + ς) :=
          mul_le_mul_of_nonneg_left hx (by positivity)
      _ = 2 * ς := by field_simp

/-! ## Balls about collector points and the collars -/

theorem q7b_norm_of_mem_siteC {x : Rd d} (hx : x ∈ siteC d) : 3 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 5 / 2 := by
  have h := hx
  simp only [siteC, annCl, mem_ofPred_eq, sub_zero] at h
  exact h

/-- A ball of radius `< 1` about a collector point lies in the inspection `A`. -/
theorem q7b_closedBall_subset_siteA {x : Rd d} {ρ : ℝ} (hx : x ∈ siteC d) (hρ : ρ < 1) :
    closedBall x ρ ⊆ siteA d := by
  obtain ⟨h1, h2⟩ := q7b_norm_of_mem_siteC hx
  intro y hy
  rw [mem_closedBall, dist_eq_norm] at hy
  have hyx : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
    calc ‖y‖ = ‖x + (y - x)‖ := by rw [add_sub_cancel]
      _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
  have hxy : ‖x‖ ≤ ‖y‖ + ‖y - x‖ := by
    calc ‖x‖ = ‖y - (y - x)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖y‖ + ‖y - x‖ := norm_sub_le _ _
  show y ∈ annA d
  simp only [annA, ann, mem_ofPred_eq, sub_zero]
  constructor <;> linarith

/-- **Inner collar** ((C6) from (R3)): a path from `∂B_{3/2}` to `∂B_{1/2}` has `D`-length at least the internal
crossing distance in `A` between `∂B_1` and `∂B_{3/2}`. -/
theorem q7b_collar_inner (D : ContMetric d) {P : ℝ → Rd d} (hP : ContinuousOn P (Icc 0 1))
    (h0 : ‖P 0‖ = 3 / 2) (h1 : ‖P 1‖ = 1 / 2) :
    setDistIn D (siteA d) (sphere (0 : Rd d) 1) (sphere (0 : Rd d) (3 / 2)) ≤ D.len P 0 1 := by
  obtain ⟨p, q, hp0, hpq, hq1, hgp, hgq, hband⟩ :=
    q6_downcross_times (g := fun t => ‖P t‖) zero_le_one hP.norm (show (1 : ℝ) < 3 / 2 by norm_num)
      (by simp only [h0]; norm_num) (by simp only [h1]; norm_num)
  have hmaps : MapsTo P (Icc p q) (siteA d) := by
    intro t ht
    obtain ⟨hlo, hhi⟩ := hband t ht
    show P t ∈ annA d
    simp only [annA, ann, mem_ofPred_eq, sub_zero]
    constructor <;> linarith
  have hlen : D.internal (siteA d) (P p) (P q) ≤ D.len P 0 1 :=
    (D.internal_le_len hpq.le (hP.mono (Icc_subset_Icc hp0 hq1)) hmaps).trans (D.len_mono P hp0 hq1)
  have hPq : P q ∈ sphere (0 : Rd d) 1 := by
    rw [mem_sphere_zero_iff_norm]
    exact hgq
  have hPp : P p ∈ sphere (0 : Rd d) (3 / 2) := by
    rw [mem_sphere_zero_iff_norm]
    exact hgp
  calc setDistIn D (siteA d) (sphere (0 : Rd d) 1) (sphere (0 : Rd d) (3 / 2))
      ≤ D.internal (siteA d) (P q) (P p) := iInf₂_le_of_le (P q) hPq (iInf₂_le (P p) hPp)
    _ = D.internal (siteA d) (P p) (P q) := D.internal_comm _ _ _
    _ ≤ D.len P 0 1 := hlen

/-- **Outer collar** ((C6) from (R3)): a path from `∂B_{5/2}` to `∂B_{7/2}` has `D`-length at least the internal
crossing distance in `A` between `∂B_{5/2}` and `∂B_3`. -/
theorem q7b_collar_outer (D : ContMetric d) {P : ℝ → Rd d} (hP : ContinuousOn P (Icc 0 1))
    (h0 : ‖P 0‖ = 5 / 2) (h1 : ‖P 1‖ = 7 / 2) :
    setDistIn D (siteA d) (sphere (0 : Rd d) (5 / 2)) (sphere (0 : Rd d) 3) ≤ D.len P 0 1 := by
  obtain ⟨p, q, hp0, hpq, hq1, hgp, hgq, hband⟩ :=
    q6_upcross_times (g := fun t => ‖P t‖) zero_le_one hP.norm (show (5 / 2 : ℝ) < 3 by norm_num)
      (by simp only [h0]; norm_num) (by simp only [h1]; norm_num)
  have hmaps : MapsTo P (Icc p q) (siteA d) := by
    intro t ht
    obtain ⟨hlo, hhi⟩ := hband t ht
    show P t ∈ annA d
    simp only [annA, ann, mem_ofPred_eq, sub_zero]
    constructor <;> linarith
  have hlen : D.internal (siteA d) (P p) (P q) ≤ D.len P 0 1 :=
    (D.internal_le_len hpq.le (hP.mono (Icc_subset_Icc hp0 hq1)) hmaps).trans (D.len_mono P hp0 hq1)
  have hPp : P p ∈ sphere (0 : Rd d) (5 / 2) := by
    rw [mem_sphere_zero_iff_norm]
    exact hgp
  have hPq : P q ∈ sphere (0 : Rd d) 3 := by
    rw [mem_sphere_zero_iff_norm]
    exact hgq
  calc setDistIn D (siteA d) (sphere (0 : Rd d) (5 / 2)) (sphere (0 : Rd d) 3)
      ≤ D.internal (siteA d) (P p) (P q) := iInf₂_le_of_le (P p) hPp (iInf₂_le (P q) hPq)
    _ ≤ D.len P 0 1 := hlen

end HigherDimLQGContinuity
