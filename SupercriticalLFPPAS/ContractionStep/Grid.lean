import Mathlib

set_option autoImplicit false

namespace SupercriticalLFPPAS.ContractionStep

/-- A finite square of integer lattice indices. -/
def latticeIndices (N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(N : ℤ)) (N : ℤ)).product (Finset.Icc (-(N : ℤ)) (N : ℤ))

/-- The point indexed by `(i,j)` in the square grid of mesh `q`. -/
def latticePoint (q : ℝ) (ij : ℤ × ℤ) : ℂ :=
  ⟨q * (ij.1 : ℝ), q * (ij.2 : ℝ)⟩

theorem latticeIndices_card (N : ℕ) : (latticeIndices N).card = (2 * N + 1) ^ 2 := by
  have hIcc : ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℤ) = 2 * (N : ℤ) + 1 := by
    have hn : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg N
    have hb : -(N : ℤ) ≤ (N : ℤ) + 1 := by omega
    rw [Int.card_Icc_of_le (a := -(N : ℤ)) (b := (N : ℤ)) hb]
    ring
  have hNat : (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
    exact_mod_cast hIcc
  change ((Finset.Icc (-(N : ℤ)) (N : ℤ)).product
    (Finset.Icc (-(N : ℤ)) (N : ℤ))).card = (2 * N + 1) ^ 2
  rw [Finset.product_eq_sprod, Finset.card_product, hNat]
  ring

/-- Every point of `B_R` is within `10q` of a point in the finite square grid, as soon as the
index square extends beyond `B_{R+1}`. -/
theorem lattice_cover (q R : ℝ) (hq : 0 < q) (_hR : 1 ≤ R) (N : ℕ)
    (hN : (R + 1) / q ≤ (N : ℝ)) (z : ℂ) (hz : ‖z‖ < R) :
    ∃ ij ∈ latticeIndices N, dist z (latticePoint q ij) < 10 * q := by
  let ix : ℤ := Int.floor (z.re / q)
  let iy : ℤ := Int.floor (z.im / q)
  have hzre : -R < z.re ∧ z.re < R := by
    have h := Complex.abs_re_le_norm z
    have habs : |z.re| < R := lt_of_le_of_lt h hz
    exact abs_lt.mp habs
  have hzim : -R < z.im ∧ z.im < R := by
    have h := Complex.abs_im_le_norm z
    have habs : |z.im| < R := lt_of_le_of_lt h hz
    exact abs_lt.mp habs
  have hRN : R + 1 ≤ q * (N : ℝ) := by
    have := (div_le_iff₀ hq).mp hN
    nlinarith
  have hixlo : -(N : ℝ) < z.re / q := by
    apply (lt_div_iff₀ hq).2
    nlinarith
  have hixhi : z.re / q < (N : ℝ) := (div_lt_iff₀ hq).2 (by nlinarith [hzre.2])
  have hiylo : -(N : ℝ) < z.im / q := by
    apply (lt_div_iff₀ hq).2
    nlinarith
  have hiyhi : z.im / q < (N : ℝ) := (div_lt_iff₀ hq).2 (by nlinarith [hzim.2])
  have hixlo' : -(N : ℤ) ≤ ix := by
    dsimp [ix]
    have hfloor := Int.lt_floor_add_one (z.re / q)
    have hcast : (-(N : ℤ) : ℝ) < z.re / q := by exact_mod_cast hixlo
    have : (-(N : ℝ) - 1) < (Int.floor (z.re / q) : ℝ) := by nlinarith
    have hcast' : -(N : ℤ) - 1 < Int.floor (z.re / q) := by exact_mod_cast this
    omega
  have hixhi' : ix ≤ (N : ℤ) := by
    dsimp [ix]
    have hf := Int.floor_le (z.re / q)
    have hfcast : (Int.floor (z.re / q) : ℝ) ≤ (N : ℝ) := le_of_lt (lt_of_le_of_lt hf hixhi)
    exact_mod_cast hfcast
  have hiylo' : -(N : ℤ) ≤ iy := by
    dsimp [iy]
    have hfloor := Int.lt_floor_add_one (z.im / q)
    have hcast : (-(N : ℤ) : ℝ) < z.im / q := by exact_mod_cast hiylo
    have : (-(N : ℝ) - 1) < (Int.floor (z.im / q) : ℝ) := by nlinarith
    have hcast' : -(N : ℤ) - 1 < Int.floor (z.im / q) := by exact_mod_cast this
    omega
  have hiyhi' : iy ≤ (N : ℤ) := by
    dsimp [iy]
    have hf := Int.floor_le (z.im / q)
    have hfcast : (Int.floor (z.im / q) : ℝ) ≤ (N : ℝ) := le_of_lt (lt_of_le_of_lt hf hiyhi)
    exact_mod_cast hfcast
  have hmem : (ix, iy) ∈ latticeIndices N := by
    simp [latticeIndices, hixlo', hixhi', hiylo', hiyhi']
  have hxerr0 : 0 ≤ z.re - q * (ix : ℝ) := by
    dsimp [ix]
    have hf := Int.floor_le (z.re / q)
    have hmul := mul_le_mul_of_nonneg_left hf hq.le
    have hcancel : q * (z.re / q) = z.re := by
      rw [mul_comm q (z.re / q), div_mul_cancel₀ _ hq.ne']
    rw [hcancel] at hmul
    linarith
  have hxerr1 : z.re - q * (ix : ℝ) < q := by
    dsimp [ix]
    have hf := Int.lt_floor_add_one (z.re / q)
    have hmul := mul_lt_mul_of_pos_left hf hq
    have hcancel : q * (z.re / q) = z.re := by
      rw [mul_comm q (z.re / q), div_mul_cancel₀ _ hq.ne']
    rw [hcancel] at hmul
    ring_nf at hmul ⊢
    nlinarith
  have hyerr0 : 0 ≤ z.im - q * (iy : ℝ) := by
    dsimp [iy]
    have hf := Int.floor_le (z.im / q)
    have hmul := mul_le_mul_of_nonneg_left hf hq.le
    have hcancel : q * (z.im / q) = z.im := by
      rw [mul_comm q (z.im / q), div_mul_cancel₀ _ hq.ne']
    rw [hcancel] at hmul
    linarith
  have hyerr1 : z.im - q * (iy : ℝ) < q := by
    dsimp [iy]
    have hf := Int.lt_floor_add_one (z.im / q)
    have hmul := mul_lt_mul_of_pos_left hf hq
    have hcancel : q * (z.im / q) = z.im := by
      rw [mul_comm q (z.im / q), div_mul_cancel₀ _ hq.ne']
    rw [hcancel] at hmul
    ring_nf at hmul ⊢
    nlinarith
  refine ⟨(ix, iy), hmem, ?_⟩
  rw [dist_eq_norm]
  have hre : (z - latticePoint q (ix, iy)).re = z.re - q * (ix : ℝ) := by simp [latticePoint]
  have him : (z - latticePoint q (ix, iy)).im = z.im - q * (iy : ℝ) := by simp [latticePoint]
  have hnorm := Complex.norm_le_abs_re_add_abs_im (z - latticePoint q (ix, iy))
  have hxabs : |z.re - q * (ix : ℝ)| < q := by rw [abs_of_nonneg hxerr0]; exact hxerr1
  have hyabs : |z.im - q * (iy : ℝ)| < q := by rw [abs_of_nonneg hyerr0]; exact hyerr1
  calc
    ‖z - latticePoint q (ix, iy)‖ ≤ |z.re - q * (ix : ℝ)| + |z.im - q * (iy : ℝ)| := by
      simpa [hre, him] using hnorm
    _ < 2 * q := by linarith
    _ < 10 * q := by nlinarith [hq]

end SupercriticalLFPPAS.ContractionStep
