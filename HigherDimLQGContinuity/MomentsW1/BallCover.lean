import HigherDimLQGContinuity.MomentsW1.NormCosts

/-! A finite cover transfers the cubical self-internal modulus to confined balls. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory Set Metric
open HigherDimLFPP (Rd lfppDistOn PcwJoined lfppDistOn_le_sum)
open HigherDimLFPP.DGZ (obox cbox obox_subset_cbox mem_obox_self
  abs_apply_le_norm convex_obox)
open HigherDimLQGMetric.DGZ (selfDiam lfppDistOn_le_selfDiam norm_sub_le_of_mem_cbox)

variable {d : ℕ}

/-- A fixed number of small boxes suffices to connect two points in a ball. -/
def wnBallLinks (d : ℕ) : ℕ := ⌈8*Real.sqrt (d:ℝ)⌉₊+1

theorem wnBallLinks_pos (d : ℕ) : 0 < wnBallLinks d := by
  dsimp [wnBallLinks]
  omega

theorem wnBallLinks_mesh (d : ℕ) :
    8*Real.sqrt (d:ℝ) ≤ (wnBallLinks d:ℝ) := by
  have hceil := Nat.le_ceil (8*Real.sqrt (d:ℝ))
  dsimp [wnBallLinks]
  push_cast
  linarith

theorem wnBall_of_cubes (hd : 2 ≤ d) {φ : Rd d → ℝ} (hφ : Continuous φ)
    {ξ σ R B : ℝ} (hσ : 0 < σ) (_hR : 1 ≤ R) (hB : 0 ≤ B)
    (hcube : ∀ w ∈ cbox (0 : Rd d) (R+1), ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      selfDiam ξ φ w ρ ≤ B*ρ^σ)
    {z : Rd d} (hz : z ∈ closedBall (0 : Rd d) R)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {x y : Rd d} (hx : x ∈ ball z s) (hy : y ∈ ball z s) :
    lfppDistOn ξ φ (ball z (3/2*s)) x y ≤
      (wnBallLinks d:ℝ)*B*s^σ := by
  let N : ℕ := wnBallLinks d
  let τ : ℝ := s/(4*Real.sqrt (d:ℝ))
  let V : Set (Rd d) := ball z (3/2*s)
  let v : ℕ → Rd d := fun i => AffineMap.lineMap x y ((i:ℝ)/N)
  let Wi : ℕ → Set (Rd d) := fun i => if i < N then obox (v i) τ else V
  have hd0 : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hsqrtd : 1 ≤ Real.sqrt (d:ℝ) := by
    have hd1 : (1:ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    simpa using Real.sqrt_le_sqrt hd1
  have hsqrt0 : 0 < Real.sqrt (d:ℝ) := by linarith
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτs : τ ≤ s := by
    dsimp [τ]
    apply (div_le_iff₀ (by positivity : 0 < 4*Real.sqrt (d:ℝ))).2
    nlinarith
  have hτ1 : τ ≤ 1 := hτs.trans hs1
  have hN0 : (0:ℝ) < N := by exact_mod_cast wnBallLinks_pos d
  have hNmesh : 2*s ≤ (N:ℝ)*τ := by
    have hN := wnBallLinks_mesh d
    have hτid : τ*(4*Real.sqrt (d:ℝ)) = s := by
      dsimp [τ]
      field_simp
    nlinarith [mul_nonneg (show 0 ≤ (N:ℝ)-8*Real.sqrt (d:ℝ) by linarith) hτ.le]
  have hxy : dist x y < 2*s := by
    have h := dist_triangle x z y
    have hx' := Metric.mem_ball.mp hx
    have hy' : dist z y < s := by simpa [dist_comm] using Metric.mem_ball.mp hy
    linarith
  have hv (i : ℕ) (hi : i ≤ N) : v i ∈ ball z s := by
    apply (convex_ball z s).lineMap_mem hx hy
    constructor
    · positivity
    · exact (div_le_one hN0).2 (by exact_mod_cast hi)
  have hstep (i : ℕ) : dist (v i) (v (i+1)) < τ := by
    have hcoeff : dist ((i:ℝ)/N) (((i+1:ℕ):ℝ)/N) = 1/(N:ℝ) := by
      rw [Real.dist_eq]
      simp only [Nat.cast_add, Nat.cast_one]
      have he : (i:ℝ)/N-((i:ℝ)+1)/N = -(1/(N:ℝ)) := by ring
      rw [he, abs_neg, abs_of_pos (one_div_pos.mpr hN0)]
    have he := dist_lineMap_lineMap x y ((i:ℝ)/N) (((i+1:ℕ):ℝ)/N)
    change dist (v i) (v (i+1)) = _ at he
    rw [hcoeff] at he
    have hprod : dist x y < (N:ℝ)*τ := hxy.trans_le hNmesh
    rw [he]
    rw [one_div, mul_comm]
    exact (div_lt_iff₀ hN0).2 (by simpa [mul_comm] using hprod)
  have hWi : ∀ i, Wi i ⊆ V := by
    intro i u hu
    by_cases hi : i < N
    · have hbox : u ∈ obox (v i) τ := by simpa [Wi, hi] using hu
      have hvi : v i ∈ ball z s := hv i hi.le
      have hnorm := norm_sub_le_of_mem_cbox
        (obox_subset_cbox _ _ hbox)
        (obox_subset_cbox _ _ (mem_obox_self (v i) hτ))
      have hdist : dist u (v i) ≤ s/2 := by
        have hτid : 2*Real.sqrt (d:ℝ)*τ = s/2 := by
          dsimp [τ]
          field_simp
          ring
        rw [dist_eq_norm]
        linarith
      have htri := dist_triangle u (v i) z
      have hvz := Metric.mem_ball.mp hvi
      change dist u z < 3/2*s
      linarith
    · simpa [Wi, hi] using hu
  have hj : ∀ i < N, PcwJoined (Wi i) (v i) (v (i+1)) := by
    intro i hi
    have hcenter : v i ∈ obox (v i) τ := mem_obox_self _ hτ
    have hnext : v (i+1) ∈ obox (v i) τ := by
      intro t
      have hcoord : |v (i+1) t-v i t| ≤ ‖v (i+1)-v i‖ := by
        simpa only [PiLp.sub_apply] using abs_apply_le_norm (v (i+1)-v i) t
      have hdist := hstep i
      rw [dist_eq_norm, norm_sub_rev] at hdist
      exact hcoord.trans_lt hdist
    have hj' := PcwJoined.of_convex (convex_obox (v i) τ) hcenter hnext
    simpa [Wi, hi] using hj'
  have hsmall (i : ℕ) (hi : i < N) :
      lfppDistOn ξ φ (Wi i) (v i) (v (i+1)) ≤ B*τ^σ := by
    have hcenter : v i ∈ obox (v i) τ := mem_obox_self _ hτ
    have hnext : v (i+1) ∈ obox (v i) τ := by
      intro t
      have hcoord : |v (i+1) t-v i t| ≤ ‖v (i+1)-v i‖ := by
        simpa only [PiLp.sub_apply] using abs_apply_le_norm (v (i+1)-v i) t
      have hdist := hstep i
      rw [dist_eq_norm, norm_sub_rev] at hdist
      exact hcoord.trans_lt hdist
    have hw : v i ∈ cbox (0 : Rd d) (R+1) := by
      intro t
      have hzR : ‖z‖ ≤ R := by simpa [dist_eq_norm] using Metric.mem_closedBall.mp hz
      have hvi := Metric.mem_ball.mp (hv i hi.le)
      have htri : ‖v i‖ ≤ ‖v i-z‖+‖z‖ := by
        calc
          ‖v i‖ = ‖(v i-z)+z‖ := by simp
          _ ≤ ‖v i-z‖+‖z‖ := norm_add_le _ _
      have hcoord := abs_apply_le_norm (v i) t
      have hnorm : ‖v i-z‖ < s := by simpa [dist_eq_norm] using hvi
      have habs : |v i t| ≤ R+1 := by linarith
      simpa using habs
    have hdiam := hcube (v i) hw τ hτ hτ1
    have hdist := lfppDistOn_le_selfDiam (ξ := ξ) hφ hcenter hnext
    simpa [Wi, hi] using hdist.trans hdiam
  have hchain := lfppDistOn_le_sum (ζ := ξ) hφ v Wi hWi N hj
  have hv0 : v 0 = x := by simp [v]
  have hvN : v N = y := by
    simp only [v]
    rw [div_self hN0.ne', AffineMap.lineMap_apply_one]
  rw [hv0, hvN] at hchain
  have hsum : (∑ i ∈ Finset.range N, lfppDistOn ξ φ (Wi i) (v i) (v (i+1))) ≤
      ∑ _i ∈ Finset.range N, B*τ^σ :=
    Finset.sum_le_sum fun i hi => hsmall i (Finset.mem_range.mp hi)
  have hpow : τ^σ ≤ s^σ := Real.rpow_le_rpow hτ.le hτs hσ.le
  have hNB : 0 ≤ (N:ℝ)*B := mul_nonneg (Nat.cast_nonneg _) hB
  calc
    lfppDistOn ξ φ (ball z (3/2*s)) x y ≤
        ∑ i ∈ Finset.range N, lfppDistOn ξ φ (Wi i) (v i) (v (i+1)) := by
          simpa only [V] using hchain
    _ ≤ ∑ _i ∈ Finset.range N, B*τ^σ := hsum
    _ = (N:ℝ)*B*τ^σ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ (N:ℝ)*B*s^σ := mul_le_mul_of_nonneg_left hpow hNB
    _ = (wnBallLinks d:ℝ)*B*s^σ := rfl

end HigherDimLQGContinuity
