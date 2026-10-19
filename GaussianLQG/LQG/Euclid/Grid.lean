import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Int.Interval

/-!
# The grid of mesh `s` (blueprint Lemma `lem:euclidean`, Steps 3 and 4)

For `s ∈ (0, 1]` and `R ≥ 0` let `N = ⌈R/s⌉₊ + 1` and let `Λ = {s(m + i n) : |m|, |n| ≤ N}`, indexed
by `gridIdx s R = {-N, …, N}²` (`gridPt s (m, n) = s(m + i n)`). Then:

* `card_gridIdx_le`: `#Λ ≤ ((2R + 5)/s)²`;
* `norm_gridPt_le`: every grid point lies in `B̄_{2R+4}(0)`;
* `exists_gridPt_near`: every `z ∈ B̄_R(0)` is within distance `s` of a grid point.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace GaussianLQG

/-- `N = ⌈R/s⌉₊ + 1`. -/
def gridN (s R : ℝ) : ℕ := ⌈R / s⌉₊ + 1

/-- The index set `{-N, …, N}²` of the grid. -/
def gridIdx (s R : ℝ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(gridN s R : ℤ)) (gridN s R) ×ˢ Finset.Icc (-(gridN s R : ℤ)) (gridN s R)

/-- The grid point `s(m + i n)`. -/
def gridPt (s : ℝ) (i : ℤ × ℤ) : ℂ := ⟨s * i.1, s * i.2⟩

theorem card_Icc_gridN (s R : ℝ) :
    (Finset.Icc (-(gridN s R : ℤ)) (gridN s R)).card = 2 * gridN s R + 1 := by
  rw [Int.card_Icc]
  omega

theorem card_gridIdx (s R : ℝ) : (gridIdx s R).card = (2 * gridN s R + 1) ^ 2 := by
  rw [gridIdx, Finset.card_product, card_Icc_gridN, sq]

/-- `N ≤ R/s + 2`. -/
theorem gridN_le {s R : ℝ} (hs : 0 < s) (hR : 0 ≤ R) : (gridN s R : ℝ) ≤ R / s + 2 := by
  have h := Nat.ceil_lt_add_one (div_nonneg hR hs.le)
  rw [gridN, Nat.cast_add, Nat.cast_one]
  linarith

/-- `#Λ ≤ ((2R + 5)/s)²` for `0 < s ≤ 1`, `R ≥ 0`. -/
theorem card_gridIdx_le {s R : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hR : 0 ≤ R) :
    ((gridIdx s R).card : ℝ) ≤ ((2 * R + 5) / s) ^ 2 := by
  rw [card_gridIdx, Nat.cast_pow]
  have hN := gridN_le hs hR
  have h1 : ((2 * gridN s R + 1 : ℕ) : ℝ) ≤ (2 * R + 5) / s := by
    push_cast
    have h5 : 5 ≤ 5 / s := by
      rw [le_div_iff₀ hs]
      linarith
    have : 2 * (R / s) + 5 ≤ (2 * R + 5) / s := by
      rw [add_div, mul_div_assoc]
      linarith
    linarith
  exact pow_le_pow_left₀ (by positivity) h1 2

theorem abs_le_gridN_of_mem {s R : ℝ} {i : ℤ × ℤ} (hi : i ∈ gridIdx s R) :
    |(i.1 : ℝ)| ≤ gridN s R ∧ |(i.2 : ℝ)| ≤ gridN s R := by
  rw [gridIdx, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hi
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hi
  refine ⟨abs_le.2 ⟨?_, ?_⟩, abs_le.2 ⟨?_, ?_⟩⟩
  · have := (Int.cast_le (R := ℝ)).2 h1
    push_cast at this
    exact this
  · exact_mod_cast h2
  · have := (Int.cast_le (R := ℝ)).2 h3
    push_cast at this
    exact this
  · exact_mod_cast h4

/-- Every grid point lies in `B̄_{2R+4}(0)` (for `0 < s ≤ 1`, `R ≥ 0`). -/
theorem norm_gridPt_le {s R : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hR : 0 ≤ R) {i : ℤ × ℤ}
    (hi : i ∈ gridIdx s R) : ‖gridPt s i‖ ≤ 2 * R + 4 := by
  obtain ⟨h1, h2⟩ := abs_le_gridN_of_mem hi
  have hN := gridN_le hs hR
  have hsN : s * (gridN s R : ℝ) ≤ R + 2 := by
    calc s * (gridN s R : ℝ) ≤ s * (R / s + 2) := mul_le_mul_of_nonneg_left hN hs.le
      _ = R + 2 * s := by field_simp
      _ ≤ R + 2 := by linarith
  calc ‖gridPt s i‖ ≤ |(gridPt s i).re| + |(gridPt s i).im| := Complex.norm_le_abs_re_add_abs_im _
    _ = s * |(i.1 : ℝ)| + s * |(i.2 : ℝ)| := by
        simp only [gridPt, abs_mul, abs_of_pos hs]
    _ ≤ s * gridN s R + s * gridN s R := by gcongr
    _ ≤ 2 * R + 4 := by linarith

/-- Every `z ∈ B̄_R(0)` is within distance `s` of a grid point (for `s > 0`). -/
theorem exists_gridPt_near {s R : ℝ} (hs : 0 < s) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ∃ i ∈ gridIdx s R, ‖z - gridPt s i‖ ≤ s := by
  set m : ℤ := round (z.re / s) with hm
  set n : ℤ := round (z.im / s) with hn
  have hRs : R / s ≤ ⌈R / s⌉₊ := Nat.le_ceil _
  have hNR : (⌈R / s⌉₊ : ℝ) + 1 = gridN s R := by rw [gridN]; push_cast; ring
  have hcoord : ∀ x : ℝ, |x| ≤ R → |x - s * round (x / s)| ≤ s / 2 ∧
      -(gridN s R : ℤ) ≤ round (x / s) ∧ round (x / s) ≤ (gridN s R : ℤ) := by
    intro x hx
    have hr := abs_sub_round (x / s)
    have hxs : |x / s| ≤ R / s := by
      rw [abs_div, abs_of_pos hs]
      exact div_le_div_of_nonneg_right hx hs.le
    refine ⟨?_, ?_, ?_⟩
    · have e : x - s * round (x / s) = s * (x / s - round (x / s)) := by field_simp
      rw [e, abs_mul, abs_of_pos hs]
      calc s * |x / s - round (x / s)| ≤ s * (1 / 2) := mul_le_mul_of_nonneg_left hr hs.le
        _ = s / 2 := by ring
    · have h1 : -(gridN s R : ℝ) ≤ (round (x / s) : ℝ) := by
        have := (abs_le.1 hr).2
        have := (abs_le.1 hxs).1
        linarith
      exact_mod_cast h1
    · have h1 : (round (x / s) : ℝ) ≤ (gridN s R : ℝ) := by
        have := (abs_le.1 hr).1
        have := (abs_le.1 hxs).2
        linarith
      exact_mod_cast h1
  obtain ⟨hre, hm1, hm2⟩ := hcoord z.re ((Complex.abs_re_le_norm z).trans hz)
  obtain ⟨him, hn1, hn2⟩ := hcoord z.im ((Complex.abs_im_le_norm z).trans hz)
  refine ⟨(m, n), ?_, ?_⟩
  · rw [gridIdx, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨hm1, hm2⟩, hn1, hn2⟩
  · calc ‖z - gridPt s (m, n)‖ ≤ |(z - gridPt s (m, n)).re| + |(z - gridPt s (m, n)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = |z.re - s * m| + |z.im - s * n| := by simp only [gridPt, Complex.sub_re, Complex.sub_im]
      _ ≤ s / 2 + s / 2 := add_le_add hre him
      _ = s := by ring

end GaussianLQG
