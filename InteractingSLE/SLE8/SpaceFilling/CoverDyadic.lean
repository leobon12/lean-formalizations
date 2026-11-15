import QuantumZipper.Common.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.Basic

/-!
# κ = 8 space filling, Lemma 4: dyadic intervals and their Whitney points

Source: the user's note *Space filling of a continuous SLE₈ trace*
(`source/external/SLE8SF/sle8_space_filling_formalization.pdf`, §3, Lemma 4 and its proof, p. 4).

The bookkeeping of Lemma 4. For `m ∈ ℕ` and `j ∈ ℤ`:

* `dyIcc m j = [j 2^{-m}, (j+1) 2^{-m}]`, the dyadic interval `I`;
* `dyPt m j = c(I) + i|I| = (j + 1/2) 2^{-m} + i 2^{-m}`, its point `z_I`;
* `dyIdx L m = {j : -L 2^m ≤ j < L 2^m}`, the index set of `D_m(L)`;
* `dyDesc L n k j`, the indices of the level-`(n+k)` descendants of `I_{n,j}` in `D_{n+k}(L)`
  (`j' / 2^k = j`).

## Main results

* `sum_dyIdx_sum_dyDesc`: every descendant has exactly one level-`n` ancestor;
* `dist_dyPt_succ_le`: a child's point is within `(3/5)|I|` of its parent's point (the
  bounded-hyperbolic-distance step of (3.4));
* `floor_mem_dyDesc`, `floor_mul_two_pow_succ_ediv_two`, `tendsto_dyPt_floor`: the nested chain of
  dyadic intervals containing a point `x`, whose points converge to `x`;
* `exists_mem_dyIdx_mem_dyIcc`: the intervals of `D_n(L)` cover `[-L, L]` (`L ≥ 1`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology

namespace InteractingSLE.SLE8.SpaceFilling

open QuantumZipper

/-! ## Definitions -/

/-- The **Whitney point** `z_I = c(I) + i|I| = (j + 1/2) 2^{-m} + i 2^{-m}` of the dyadic interval
`I = [j 2^{-m}, (j+1) 2^{-m}]`. -/
def dyPt (m : ℕ) (j : ℤ) : ℂ :=
  ((((j : ℝ) + 1 / 2) / 2 ^ m : ℝ) : ℂ) + ((1 / 2 ^ m : ℝ) : ℂ) * I

/-- The **dyadic interval** `I_{m,j} = [j 2^{-m}, (j+1) 2^{-m}]`. -/
def dyIcc (m : ℕ) (j : ℤ) : Set ℝ := Icc ((j : ℝ) / 2 ^ m) (((j : ℝ) + 1) / 2 ^ m)

/-- The index set of `D_m(L)`: `j = -L 2^m, …, L 2^m - 1`. -/
def dyIdx (L m : ℕ) : Finset ℤ := Finset.Ico (-((L : ℤ) * 2 ^ m)) ((L : ℤ) * 2 ^ m)

/-- The indices `j'` of the level-`(n+k)` intervals of `D_{n+k}(L)` contained in `I_{n,j}`. -/
def dyDesc (L n k : ℕ) (j : ℤ) : Finset ℤ := (dyIdx L (n + k)).filter fun j' => j' / 2 ^ k = j

variable {L m n k : ℕ} {j j' : ℤ}

@[simp] theorem dyPt_re (m : ℕ) (j : ℤ) : (dyPt m j).re = ((j : ℝ) + 1 / 2) / 2 ^ m := by
  rw [dyPt, add_re, ofReal_re, re_ofReal_mul, I_re, mul_zero, add_zero]

@[simp] theorem dyPt_im (m : ℕ) (j : ℤ) : (dyPt m j).im = 1 / 2 ^ m := by
  rw [dyPt, add_im, ofReal_im, im_ofReal_mul, I_im, mul_one, zero_add]

theorem dyPt_im_pos (m : ℕ) (j : ℤ) : 0 < (dyPt m j).im := by
  rw [dyPt_im]; positivity

theorem dyPt_mem_H (m : ℕ) (j : ℤ) : dyPt m j ∈ H := dyPt_im_pos m j

theorem mem_dyIdx : j ∈ dyIdx L m ↔ -((L : ℤ) * 2 ^ m) ≤ j ∧ j < (L : ℤ) * 2 ^ m := by
  simp [dyIdx]

theorem card_dyIdx (L m : ℕ) : (dyIdx L m).card = 2 * L * 2 ^ m := by
  rw [dyIdx, Int.card_Ico]
  have : (L : ℤ) * 2 ^ m - -((L : ℤ) * 2 ^ m) = ((2 * L * 2 ^ m : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast]

theorem mem_dyDesc : j' ∈ dyDesc L n k j ↔ j' ∈ dyIdx L (n + k) ∧ j' / 2 ^ k = j := by
  simp [dyDesc]

/-! ## Integer division by powers of two -/

theorem two_pow_pos_int (k : ℕ) : (0 : ℤ) < 2 ^ k := by positivity

theorem ediv_two_pow_eq_iff (k : ℕ) : j' / 2 ^ k = j ↔ j * 2 ^ k ≤ j' ∧ j' < (j + 1) * 2 ^ k := by
  rw [← Int.le_ediv_iff_mul_le (two_pow_pos_int k), ← Int.ediv_lt_iff_lt_mul (two_pow_pos_int k)]
  omega

/-- The ancestor of an index of `D_{n+k}(L)` lies in `D_n(L)`. -/
theorem ediv_mem_dyIdx (h : j' ∈ dyIdx L (n + k)) : j' / 2 ^ k ∈ dyIdx L n := by
  rw [mem_dyIdx] at h ⊢
  have hk := two_pow_pos_int k
  have e : (L : ℤ) * 2 ^ (n + k) = (L * 2 ^ n) * 2 ^ k := by rw [pow_add]; ring
  rw [e] at h
  constructor
  · rw [Int.le_ediv_iff_mul_le hk]; linarith
  · rw [Int.ediv_lt_iff_lt_mul hk]; linarith

/-- **Every descendant has exactly one ancestor.** Summing over `D_n(L)` the sums over the
level-`(n+k)` descendants gives the sum over `D_{n+k}(L)`. -/
theorem sum_dyIdx_sum_dyDesc {M : Type*} [AddCommMonoid M] (L n k : ℕ) (g : ℤ → M) :
    ∑ j ∈ dyIdx L n, ∑ j' ∈ dyDesc L n k j, g j' = ∑ j' ∈ dyIdx L (n + k), g j' :=
  Finset.sum_fiberwise_of_maps_to (fun _ hj' => ediv_mem_dyIdx hj') g

/-! ## Real positions -/

theorem two_pow_pos_real (m : ℕ) : (0 : ℝ) < 2 ^ m := by positivity

/-- A descendant's point lies above the ancestor interval. -/
theorem dyPt_re_mem_dyIcc_of_mem_dyDesc (hj' : j' ∈ dyDesc L n k j) :
    (dyPt (n + k) j').re ∈ dyIcc n j := by
  rw [mem_dyDesc, ediv_two_pow_eq_iff] at hj'
  obtain ⟨-, h1, h2⟩ := hj'
  have h1' : (j : ℝ) * 2 ^ k ≤ j' := by exact_mod_cast h1
  have h2' : (j' : ℝ) + 1 ≤ ((j : ℝ) + 1) * 2 ^ k := by exact_mod_cast h2
  have hn := two_pow_pos_real n
  have hk := two_pow_pos_real k
  rw [dyPt_re, dyIcc, pow_add]
  constructor
  · rw [div_le_div_iff₀ hn (mul_pos hn hk)]
    nlinarith
  · rw [div_le_div_iff₀ (mul_pos hn hk) hn]
    nlinarith

theorem dyIcc_subset_Icc (hj : j ∈ dyIdx L n) : dyIcc n j ⊆ Icc (-(L : ℝ)) L := by
  rw [mem_dyIdx] at hj
  have h1 : -((L : ℝ) * 2 ^ n) ≤ j := by exact_mod_cast hj.1
  have h2 : (j : ℝ) + 1 ≤ (L : ℝ) * 2 ^ n := by exact_mod_cast hj.2
  have hn := two_pow_pos_real n
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  constructor
  · calc -(L : ℝ) = -((L : ℝ) * 2 ^ n) / 2 ^ n := by field_simp
      _ ≤ (j : ℝ) / 2 ^ n := div_le_div_of_nonneg_right h1 hn.le
      _ ≤ x := hx1
  · calc x ≤ ((j : ℝ) + 1) / 2 ^ n := hx2
      _ ≤ (L : ℝ) * 2 ^ n / 2 ^ n := div_le_div_of_nonneg_right h2 hn.le
      _ = L := by field_simp

theorem dyPt_re_mem_dyIcc (m : ℕ) (j : ℤ) : (dyPt m j).re ∈ dyIcc m j := by
  have hm := two_pow_pos_real m
  rw [dyPt_re, dyIcc]
  constructor
  · exact div_le_div_of_nonneg_right (by linarith) hm.le
  · exact div_le_div_of_nonneg_right (by linarith) hm.le

theorem abs_dyPt_re_le (hj : j ∈ dyIdx L m) : |(dyPt m j).re| ≤ L :=
  abs_le.2 (dyIcc_subset_Icc hj (dyPt_re_mem_dyIcc m j))

theorem dyIcc_length {x x' : ℝ} (hx : x ∈ dyIcc m j) (hx' : x' ∈ dyIcc m j) :
    |x - x'| ≤ 1 / 2 ^ m := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h1', h2'⟩ := hx'
  have e : ((j : ℝ) + 1) / 2 ^ m - (j : ℝ) / 2 ^ m = 1 / 2 ^ m := by ring
  rw [abs_le]; constructor <;> linarith

/-- **Cover.** For `L ≥ 1`, the intervals of `D_n(L)` cover `[-L, L]`. -/
theorem exists_mem_dyIdx_mem_dyIcc (hL : 1 ≤ L) {x : ℝ} (hx : x ∈ Icc (-(L : ℝ)) L) (n : ℕ) :
    ∃ j ∈ dyIdx L n, x ∈ dyIcc n j := by
  have hn := two_pow_pos_real n
  obtain ⟨hx1, hx2⟩ := hx
  rcases hx2.lt_or_eq with hlt | heq
  · refine ⟨⌊x * 2 ^ n⌋, ?_, ?_⟩
    · rw [mem_dyIdx]
      constructor
      · rw [Int.le_floor]; push_cast; nlinarith
      · rw [Int.floor_lt]; push_cast; nlinarith
    · rw [dyIcc]
      constructor
      · rw [div_le_iff₀ hn]; exact Int.floor_le _
      · rw [le_div_iff₀ hn]; exact (Int.lt_floor_add_one _).le
  · refine ⟨(L : ℤ) * 2 ^ n - 1, ?_, ?_⟩
    · rw [mem_dyIdx]
      have : (1 : ℤ) ≤ (L : ℤ) * 2 ^ n := by
        have h1 : (1 : ℤ) ≤ L := by exact_mod_cast hL
        have h2 : (1 : ℤ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
        nlinarith
      constructor <;> omega
    · rw [dyIcc, heq]
      push_cast
      constructor
      · rw [div_le_iff₀ hn]; linarith
      · rw [le_div_iff₀ hn]; linarith

/-! ## The nested chain through a point -/

/-- `⌊x 2^{n+k}⌋ / 2^k = ⌊x 2^n⌋`. -/
theorem floor_mul_two_pow_add_ediv (x : ℝ) (n k : ℕ) :
    ⌊x * 2 ^ (n + k)⌋ / 2 ^ k = ⌊x * 2 ^ n⌋ := by
  rw [ediv_two_pow_eq_iff]
  have hk := two_pow_pos_real k
  have e : x * 2 ^ (n + k) = x * 2 ^ n * 2 ^ k := by rw [pow_add]; ring
  constructor
  · rw [Int.le_floor, e]; push_cast
    exact mul_le_mul_of_nonneg_right (Int.floor_le _) hk.le
  · rw [Int.floor_lt, e]; push_cast
    exact mul_lt_mul_of_pos_right (Int.lt_floor_add_one _) hk

theorem floor_mul_two_pow_succ_ediv_two (x : ℝ) (m : ℕ) :
    ⌊x * 2 ^ (m + 1)⌋ / 2 = ⌊x * 2 ^ m⌋ := by
  simpa using floor_mul_two_pow_add_ediv x m 1

theorem floor_mul_two_pow_eq {x : ℝ} (hx : x ∈ Ico ((j : ℝ) / 2 ^ n) (((j : ℝ) + 1) / 2 ^ n)) :
    ⌊x * 2 ^ n⌋ = j := by
  have hn := two_pow_pos_real n
  rw [Int.floor_eq_iff]
  obtain ⟨h1, h2⟩ := hx
  constructor
  · rwa [div_le_iff₀ hn] at h1
  · rwa [lt_div_iff₀ hn] at h2

/-- The chain through `x ∈ [j 2^{-n}, (j+1) 2^{-n})` consists of descendants of `I_{n,j}`. -/
theorem floor_mem_dyDesc (hj : j ∈ dyIdx L n) {x : ℝ}
    (hx : x ∈ Ico ((j : ℝ) / 2 ^ n) (((j : ℝ) + 1) / 2 ^ n)) (k : ℕ) :
    ⌊x * 2 ^ (n + k)⌋ ∈ dyDesc L n k j := by
  have hdiv : ⌊x * 2 ^ (n + k)⌋ / 2 ^ k = j := by
    rw [floor_mul_two_pow_add_ediv, floor_mul_two_pow_eq hx]
  refine mem_dyDesc.2 ⟨?_, hdiv⟩
  rw [ediv_two_pow_eq_iff] at hdiv
  rw [mem_dyIdx] at hj ⊢
  have hk := two_pow_pos_int k
  have e : (L : ℤ) * 2 ^ (n + k) = (L * 2 ^ n) * 2 ^ k := by rw [pow_add]; ring
  rw [e]
  constructor <;> nlinarith

/-- A child's Whitney point is within `(3/5)|I|` of its parent's: the segment `[z_I, z_J]` stays in
the disk of radius `(3/5) Im z_I` about `z_I`, at bounded hyperbolic distance. -/
theorem dist_dyPt_succ_le (m : ℕ) (j' : ℤ) :
    dist (dyPt (m + 1) j') (dyPt m (j' / 2)) ≤ 3 / 5 * (dyPt m (j' / 2)).im := by
  have hm := two_pow_pos_real m
  have hdecomp : (j' : ℝ) = 2 * ((j' / 2 : ℤ) : ℝ) + ((j' % 2 : ℤ) : ℝ) := by
    have := Int.mul_ediv_add_emod j' 2
    exact_mod_cast this.symm
  have hr : ((j' % 2 : ℤ) : ℝ) = 0 ∨ ((j' % 2 : ℤ) : ℝ) = 1 := by
    rcases Int.emod_two_eq_zero_or_one j' with h | h <;> simp [h]
  rw [Complex.dist_eq_re_im, dyPt_re, dyPt_re, dyPt_im, dyPt_im, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  set q : ℝ := ((j' / 2 : ℤ) : ℝ)
  set r : ℝ := ((j' % 2 : ℤ) : ℝ)
  rw [hdecomp, show (2 : ℝ) ^ (m + 1) = 2 ^ m * 2 from pow_succ 2 m]
  have hre : (2 * q + r + 1 / 2) / (2 ^ m * 2) - (q + 1 / 2) / 2 ^ m = (r - 1 / 2) / (2 * 2 ^ m) := by
    field_simp; ring
  have him : 1 / (2 ^ m * 2) - 1 / (2 : ℝ) ^ m = -(1 / 2) / 2 ^ m := by
    field_simp; ring
  rw [hre, him, div_pow, div_pow, mul_pow, mul_pow, div_pow]
  have hr2 : (r - 1 / 2) ^ 2 = 1 / 4 := by rcases hr with h | h <;> rw [h] <;> norm_num
  rw [hr2]
  have hu : (0 : ℝ) < (1 / 2 ^ m) ^ 2 := by positivity
  have e1 : 1 / 4 / (2 ^ 2 * ((2 : ℝ) ^ m) ^ 2) + (-(1 / 2)) ^ 2 / ((2 : ℝ) ^ m) ^ 2 =
      5 / 16 * (1 / 2 ^ m) ^ 2 := by field_simp; ring
  have e2 : (3 : ℝ) ^ 2 / 5 ^ 2 * (1 / 2 ^ m) ^ 2 = 9 / 25 * (1 / 2 ^ m) ^ 2 := by norm_num
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right (by norm_num) hu.le

/-- The chain's Whitney points approach `x`: `|z_{m}(x) - x| ≤ 2 · 2^{-m}`. -/
theorem dist_dyPt_floor_le (x : ℝ) (m : ℕ) : dist (dyPt m ⌊x * 2 ^ m⌋) (x : ℂ) ≤ 2 / 2 ^ m := by
  have hm := two_pow_pos_real m
  rw [dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [sub_re, sub_im, dyPt_re, dyPt_im, ofReal_re, ofReal_im, sub_zero]
  have h1 := Int.floor_le (x * 2 ^ m)
  have h2 := Int.lt_floor_add_one (x * 2 ^ m)
  have e1 : (((⌊x * 2 ^ m⌋ : ℤ) : ℝ) + 1 / 2) / 2 ^ m - x =
      (((⌊x * 2 ^ m⌋ : ℤ) : ℝ) + 1 / 2 - x * 2 ^ m) / 2 ^ m := by field_simp
  rw [e1, abs_div, abs_of_pos hm, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ m),
    ← add_div, div_le_div_iff_of_pos_right hm]
  have : |((⌊x * 2 ^ m⌋ : ℤ) : ℝ) + 1 / 2 - x * 2 ^ m| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  linarith

theorem tendsto_dyPt_floor (x : ℝ) :
    Tendsto (fun m : ℕ => dyPt m ⌊x * 2 ^ m⌋) atTop (𝓝 (x : ℂ)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have h2 : Tendsto (fun m : ℕ => (2 : ℝ) / 2 ^ m) atTop (𝓝 0) := by
    have : Tendsto (fun m : ℕ => (2 : ℝ) * (1 / 2) ^ m) atTop (𝓝 (2 * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul 2
    simpa [div_eq_mul_inv] using this
  exact squeeze_zero (fun _ => dist_nonneg) (fun m => dist_dyPt_floor_le x m) h2

end InteractingSLE.SLE8.SpaceFilling
