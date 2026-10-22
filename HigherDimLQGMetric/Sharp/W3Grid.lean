import HigherDimLQGMetric.Sharp.GridNear
import HigherDimLQGMetric.Sharp.GridCount

/-! Finite dyadic grids concentrated near a compact set. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- A fixed compact set has dyadic lattice covers with the cardinality needed
for the all-scale sphere-average estimate. Only grid points near the set are
retained, so their surrounding balls remain in any prescribed neighbourhood. -/
theorem w3_dyadic_grids (hd : 1 ≤ d) {K : Set (Rd d)} {R c : ℝ}
    (hR : 0 < R) (hK : ∀ x ∈ K, ‖x‖ ≤ R) (hc : 0 < c) :
    ∃ CG : ℝ, 0 < CG ∧ ∃ H : ℕ → Finset (Rd d),
      (∀ n, ((H n).card : ℝ) ≤ CG * 2 ^ (d * n)) ∧
      (∀ n, ∀ x ∈ K, ∃ w ∈ H n, ‖x - w‖ ≤ (c / 2 ^ n) / 64) ∧
      (∀ n, ∀ w ∈ H n, ∃ x ∈ K, ‖w - x‖ ≤ (c / 2 ^ n) / 64) ∧
      (∀ n, ∀ w ∈ H n, ‖w‖ ≤ R + c) := by
  classical
  let B : ℝ := R + c
  have hB : 0 < B := by dsimp [B]; positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  let ρ : ℕ → ℝ := fun n => c / 2 ^ n
  let s : ℕ → ℝ := fun n => ρ n / (64 * d)
  let N : ℕ → ℕ := fun n => ⌈B / s n⌉₊ + 1
  let H : ℕ → Finset (Rd d) := fun n =>
    (shellGridBox d (N n) (s n)).filter
      (fun w => ∃ x ∈ K, ‖w - x‖ ≤ ρ n / 64)
  let L : ℝ := 64 * d * B / c + 2
  let CG : ℝ := (2 * L + 1) ^ d
  have hCG : 0 < CG := by dsimp [CG, L]; positivity
  have hρ (n : ℕ) : 0 < ρ n := by dsimp [ρ]; positivity
  have hs (n : ℕ) : 0 < s n := by dsimp [s]; positivity
  have hρc (n : ℕ) : ρ n ≤ c := by
    dsimp [ρ]
    have hp : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    exact div_le_self hc.le hp
  have hratio (n : ℕ) : B / s n = (64 * d * B / c) * 2 ^ n := by
    dsimp [s, ρ]
    field_simp
  have hN (n : ℕ) : (N n : ℝ) < B / s n + 2 := by
    dsimp [N]
    have hb : 0 ≤ B / s n := (div_pos hB (hs n)).le
    have hceil := Nat.ceil_lt_add_one hb
    push_cast
    linarith
  have hNbound (n : ℕ) : (N n : ℝ) ≤ L * 2 ^ n := by
    have hp : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have hN' := hN n
    rw [hratio n] at hN'
    dsimp [L]
    nlinarith only [hN', hp]
  have hnear (n : ℕ) (x : Rd d) (hx : x ∈ K) :
      ∃ w ∈ H n, ‖x - w‖ ≤ ρ n / 64 := by
    obtain ⟨w, hwgrid, hw⟩ := exists_gridPt_near (hs n) x
    have hw' : ‖x - w‖ ≤ ρ n / 64 := by
      dsimp [s] at hw
      have hdne : (d : ℝ) ≠ 0 := hdR.ne'
      convert hw using 1; field_simp
    have hnorm : ‖w‖ < B := by
      have ht : ‖w‖ ≤ ‖x‖ + ‖x - w‖ := by
        have he : w = x - (x - w) := by abel
        calc
          ‖w‖ = ‖x - (x - w)‖ := congrArg norm he
          _ ≤ ‖x‖ + ‖x - w‖ := norm_sub_le x (x - w)
      have hsmall : ρ n / 64 < c := by
        have hc' := hρc n
        linarith only [hc', hc]
      dsimp [B]
      linarith only [ht, hK x hx, hw', hsmall]
    have hwbox : w ∈ shellGridBox d (N n) (s n) := by
      apply grid_ball_subset_shellGridBox (hs n) hB.le
      exact ⟨hwgrid, by simpa only [Metric.mem_ball, dist_zero_right] using hnorm⟩
    refine ⟨w, Finset.mem_filter.mpr ⟨hwbox, ?_⟩, hw'⟩
    exact ⟨x, hx, by simpa only [norm_sub_rev] using hw'⟩
  have hpoint (n : ℕ) (w : Rd d) (hw : w ∈ H n) :
      ∃ x ∈ K, ‖w - x‖ ≤ ρ n / 64 :=
    (Finset.mem_filter.mp hw).2
  have hbound (n : ℕ) (w : Rd d) (hw : w ∈ H n) : ‖w‖ ≤ B := by
    obtain ⟨x, hx, hnear⟩ := hpoint n w hw
    have ht : ‖w‖ ≤ ‖x‖ + ‖w - x‖ := by
      have he : w = x + (w - x) := by abel
      calc
        ‖w‖ = ‖x + (w - x)‖ := congrArg norm he
        _ ≤ ‖x‖ + ‖w - x‖ := norm_add_le x (w - x)
    dsimp [B]
    linarith only [ht, hK x hx, hnear, hρc n, hρ n]
  have hcard (n : ℕ) : ((H n).card : ℝ) ≤ CG * 2 ^ (d * n) := by
    have hfilter : (H n).card ≤ (shellGridBox d (N n) (s n)).card :=
      Finset.card_filter_le _ _
    have hbox := card_shellGridBox_le d (N n) (s n)
    have hcardR : ((H n).card : ℝ) ≤ (2 * (N n : ℝ) + 1) ^ d := by
      exact_mod_cast hfilter.trans hbox
    have hp : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have hbase : 2 * (N n : ℝ) + 1 ≤ (2 * L + 1) * 2 ^ n := by
      nlinarith only [hNbound n, hp]
    have hpow : (2 * (N n : ℝ) + 1) ^ d ≤ ((2 * L + 1) * 2 ^ n) ^ d :=
      pow_le_pow_left₀ (by positivity) hbase d
    calc
      ((H n).card : ℝ) ≤ (2 * (N n : ℝ) + 1) ^ d := hcardR
      _ ≤ ((2 * L + 1) * 2 ^ n) ^ d := hpow
      _ = CG * 2 ^ (d * n) := by simp only [CG, mul_pow, ← pow_mul, mul_comm]
  exact ⟨CG, hCG, H, hcard,
    (by simpa only [ρ] using hnear),
    (by simpa only [ρ] using hpoint),
    (by simpa only [B] using hbound)⟩

/-- An affine image of a grid point whose normalized position is close to `K`
has a Euclidean `2rρ`-ball inside the affine image of the open set. -/
theorem w3_affine_grid_ball {K U : Set (Rd d)} {δ c r : ℝ}
    (hδU : Metric.cthickening δ K ⊆ U) (hc : 0 < c)
    (hcδ : 3 * c ≤ δ) (hr : 0 < r)
    (z w : Rd d) (n : ℕ)
    (hnear : ∃ x ∈ K, ‖w - x‖ ≤ (c / 2 ^ n) / 64) :
    Metric.closedBall (z + r • w) (2 * (c * r / 2 ^ n)) ⊆
      affineSet r z U := by
  obtain ⟨x, hx, hwx⟩ := hnear
  intro y hy
  let u : Rd d := r⁻¹ • (y - z)
  have he : z + r • u = y := by
    dsimp [u]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  have hρ : c / 2 ^ n ≤ c :=
    div_le_self hc.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hwx' : dist (z + r • w) (z + r • x) ≤ r * ((c / 2 ^ n) / 64) := by
    rw [dist_eq_norm]
    have hv : (z + r • w) - (z + r • x) = r • (w - x) := by
      rw [smul_sub]
      abel
    rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left hwx hr.le
  have hyx : dist y (z + r • x) ≤ r * δ := by
    have hyw : dist y (z + r • w) ≤ 2 * (c * r / 2 ^ n) :=
      Metric.mem_closedBall.mp hy
    have htri := dist_triangle y (z + r • w) (z + r • x)
    have hδρ : (2 + 1 / 64 : ℝ) * (c / 2 ^ n) ≤ δ := by
      nlinarith only [hρ, hcδ, hc]
    have hm := mul_le_mul_of_nonneg_left hδρ hr.le
    have heq : 2 * (c * r / 2 ^ n) + r * (c / 2 ^ n / 64) =
        r * ((2 + 1 / 64) * (c / 2 ^ n)) := by ring
    linarith only [htri, hyw, hwx', hm, heq]
  have hscale : dist y (z + r • x) = r * dist u x := by
    rw [← he, dist_eq_norm, dist_eq_norm]
    have hv : (z + r • u) - (z + r • x) = r • (u - x) := by
      rw [smul_sub]
      abel
    rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hux : dist u x ≤ δ := by
    rw [hscale] at hyx
    exact (mul_le_mul_iff_of_pos_left hr).mp hyx
  have hu : u ∈ U := hδU (Metric.mem_cthickening_of_dist_le u x δ K hx hux)
  exact ⟨u, hu, he⟩

/-- Fixed normalized grids, affine-scaled at any location and scale, satisfy
the deterministic hypotheses of the multiscale chaining lemma. -/
theorem w3_affine_grids (hd : 1 ≤ d) {K U : Set (Rd d)}
    {R c δ : ℝ} (hR : 0 < R) (hK : ∀ x ∈ K, ‖x‖ ≤ R)
    (hc : 0 < c) (hcδ : 3 * c ≤ δ)
    (hδU : Metric.cthickening δ K ⊆ U) :
    ∃ CG : ℝ, 0 < CG ∧ ∃ H : ℕ → Finset (Rd d),
      (∀ n, ((H n).card : ℝ) ≤ CG * 2 ^ (d * n)) ∧
      (∀ n, ∀ w ∈ H n, ‖w‖ ≤ R + c) ∧
      ∀ {r : ℝ}, 0 < r → ∀ z : Rd d,
        let G : ℕ → Finset (Rd d) := fun n =>
          (H n).image (fun w => z + r • w)
        (∀ n, ((G n).card : ℝ) ≤ CG * 2 ^ (d * n)) ∧
        (∀ n, ∀ y ∈ affineSet r z K,
          ∃ w ∈ G n, ‖y - w‖ ≤ (c * r / 2 ^ n) / 64) ∧
        (∀ n, ∀ w ∈ G n,
          Metric.closedBall w (2 * (c * r / 2 ^ n)) ⊆ affineSet r z U) := by
  classical
  obtain ⟨CG, hCG, H, hcard, hcover, hpoint, hbound⟩ :=
    w3_dyadic_grids hd hR hK hc
  refine ⟨CG, hCG, H, hcard, hbound, ?_⟩
  intro r hr z
  let G : ℕ → Finset (Rd d) := fun n => (H n).image (fun w => z + r • w)
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have hh : (G n).card ≤ (H n).card := Finset.card_image_le
    exact (by exact_mod_cast hh : ((G n).card : ℝ) ≤ (H n).card).trans (hcard n)
  · intro n y hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨w, hw, hnear⟩ := hcover n x hx
    refine ⟨z + r • w, Finset.mem_image.mpr ⟨w, hw, rfl⟩, ?_⟩
    have hv : (z + r • x) - (z + r • w) = r • (x - w) := by
      rw [smul_sub]
      abel
    rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hm := mul_le_mul_of_nonneg_left hnear hr.le
    calc
      r * ‖x - w‖ ≤ r * ((c / 2 ^ n) / 64) := hm
      _ = (c * r / 2 ^ n) / 64 := by ring
  · intro n w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact w3_affine_grid_ball hδU hc hcδ hr z v n (hpoint n v hv)

end HigherDimLQGMetric
