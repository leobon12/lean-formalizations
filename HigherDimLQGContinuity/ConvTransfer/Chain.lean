import HigherDimLQGContinuity.ConvTransfer.Median
import HigherDimLQGMetric.DGZ.FunctionalsLaw

/-!
# Finite chaining for the convolution upper moment transfer
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLFPP (Rd)
open HigherDimLQGMetric.DGZ

/-- Twenty links turn a local bound at radius at most one into a bound on an
internal diameter at radius at most four. -/
theorem convEnv_diam_of_local {d : ℕ} {ξ σ S t H a : ℝ}
    {ψ : Rd d → ℝ} (hψ : Continuous ψ)
    (ht : 0 < t) (ht4 : t ≤ 4) (hH : 0 ≤ H) (ha : 0 ≤ a)
    {w : Rd d} (hw : w ∈ closedBall (0 : Rd d) (S - 4))
    (hLocal : ∀ z ∈ closedBall (0 : Rd d) S, ∀ s ∈ Ioc (0 : ℝ) 1,
      ∀ x ∈ ball z s, ∀ y ∈ ball z s,
        HigherDimLFPP.lfppDistOn ξ ψ (ball z (3 / 2 * s)) x y ≤ H * s ^ σ * a) :
    lfppDiam ξ ψ (ball w t) (ball w (29 / 20 * t)) ≤
      20 * H * (t / 5) ^ σ * a := by
  let τ : ℝ := t / 5
  have hτ0 : 0 < τ := by dsimp [τ]; positivity
  have hτ1 : τ ≤ 1 := by dsimp [τ]; linarith
  have hC : 0 ≤ 20 * H * τ ^ σ * a := by positivity
  apply lfppDiam_le hC
  intro x hx y hy
  let v : ℕ → Rd d := fun i => AffineMap.lineMap x y ((i : ℝ) / 20)
  let V : Set (Rd d) := ball w (29 / 20 * t)
  let Wi : ℕ → Set (Rd d) := fun i =>
    if i < 20 then ball (v i) (3 / 2 * τ) else V
  have hxy : dist x y < 2 * t := by
    have h := dist_triangle x w y
    have hx' : dist x w < t := hx
    have hy' : dist w y < t := by
      simpa only [dist_comm] using (Metric.mem_ball.mp hy)
    linarith
  have hcoeff (i : ℕ) :
      dist ((i : ℝ) / 20) (((i + 1 : ℕ) : ℝ) / 20) = 1 / 20 := by
    rw [Real.dist_eq]
    simp only [Nat.cast_add, Nat.cast_one]
    have he : (i : ℝ) / 20 - ((i : ℝ) + 1) / 20 = -(1 / 20 : ℝ) := by ring
    rw [he, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 20)]
  have hv (i : ℕ) (hi : i ≤ 20) : v i ∈ ball w t := by
    apply (convex_ball w t).lineMap_mem hx hy
    constructor
    · positivity
    · exact (div_le_one (by norm_num : (0 : ℝ) < 20)).2 (by exact_mod_cast hi)
  have hstep (i : ℕ) : dist (v i) (v (i + 1)) < τ := by
    have he := dist_lineMap_lineMap x y ((i : ℝ) / 20)
      (((i + 1 : ℕ) : ℝ) / 20)
    change dist (v i) (v (i + 1)) = _ at he
    rw [hcoeff] at he
    rw [he]
    dsimp [τ]
    nlinarith
  have hW : ∀ i, Wi i ⊆ V := by
    intro i q hq
    by_cases hi : i < 20
    · have hqi : dist q (v i) < 3 / 2 * τ := by
        simpa [Wi, hi, Metric.mem_ball] using hq
      have hvi : dist (v i) w < t := Metric.mem_ball.mp (hv i hi.le)
      have htri := dist_triangle q (v i) w
      change dist q w < 29 / 20 * t
      dsimp [τ] at hqi
      linarith
    · simpa [Wi, hi] using hq
  have hj : ∀ i < 20, HigherDimLFPP.PcwJoined (Wi i) (v i) (v (i + 1)) := by
    intro i hi
    have hj' : HigherDimLFPP.PcwJoined (ball (v i) (3 / 2 * τ))
        (v i) (v (i + 1)) := by
      apply HigherDimLFPP.PcwJoined.of_convex (convex_ball _ _)
      · exact mem_ball_self (by dsimp [τ]; positivity)
      · change dist (v (i + 1)) (v i) < 3 / 2 * τ
        rw [dist_comm]
        linarith [hstep i]
    simpa [Wi, hi] using hj'
  have hsmall (i : ℕ) (hi : i < 20) :
      HigherDimLFPP.lfppDistOn ξ ψ (Wi i) (v i) (v (i + 1)) ≤
        H * τ ^ σ * a := by
    have hvi : v i ∈ closedBall (0 : Rd d) S := by
      have h := dist_triangle (v i) w (0 : Rd d)
      have hvw : dist (v i) w < t := Metric.mem_ball.mp (hv i hi.le)
      have hw0 : dist w (0 : Rd d) ≤ S - 4 := Metric.mem_closedBall.mp hw
      exact Metric.mem_closedBall.mpr (by linarith)
    have hLoc := hLocal (v i) hvi τ ⟨hτ0, hτ1⟩
      (v i) (mem_ball_self hτ0) (v (i + 1))
      (by change dist (v (i + 1)) (v i) < τ
          rw [dist_comm]
          exact hstep i)
    simpa [Wi, hi] using hLoc
  have hchain := HigherDimLFPP.lfppDistOn_le_sum (ζ := ξ) hψ v Wi hW 20 hj
  have hv0 : v 0 = x := by simp only [v, Nat.cast_zero, zero_div, AffineMap.lineMap_apply_zero]
  have hv20 : v 20 = y := by
    simp only [v, Nat.cast_ofNat, div_self (by norm_num : (20 : ℝ) ≠ 0),
      AffineMap.lineMap_apply_one]
  rw [hv0, hv20] at hchain
  have hsum : (∑ i ∈ Finset.range 20,
      HigherDimLFPP.lfppDistOn ξ ψ (Wi i) (v i) (v (i + 1))) ≤
      ∑ _i ∈ Finset.range 20, H * τ ^ σ * a := by
    apply Finset.sum_le_sum
    intro i hi
    exact hsmall i (Finset.mem_range.mp hi)
  calc
    HigherDimLFPP.lfppDistOn ξ ψ (ball w (29 / 20 * t)) x y ≤
        ∑ i ∈ Finset.range 20,
          HigherDimLFPP.lfppDistOn ξ ψ (Wi i) (v i) (v (i + 1)) := by
            simpa only [V] using hchain
    _ ≤ ∑ _i ∈ Finset.range 20, H * τ ^ σ * a := hsum
    _ = 20 * H * (t / 5) ^ σ * a := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      dsimp [τ]
      ring

end HigherDimLQGContinuity
