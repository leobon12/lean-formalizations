import Mathlib

/-!
# Finite lattice nets

Finite subsets of the square lattice and of a one dimensional mesh, together with their covering
estimates. The complex-ball net is moved inward before rounding so its centers remain in the open ball.
-/

set_option autoImplicit false

open Set Metric

namespace MatedCRTHarmonic.MesoGrid

noncomputable def gridPoint (s : ℝ) (m n : ℤ) : ℂ := ⟨s * (m : ℝ), s * (n : ℝ)⟩

lemma gridPoint_eq_scaledInt (s : ℝ) (m n : ℤ) :
    gridPoint s m n = (s : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I) := by
  apply Complex.ext
  · simp [gridPoint, Complex.mul_re, Complex.mul_im]
  · simp [gridPoint, Complex.mul_re, Complex.mul_im]

lemma gridPoint_floor_dist_lt {s : ℝ} (hs : 0 < s) (w : ℂ) :
    dist w (gridPoint s (Int.floor (w.re / s)) (Int.floor (w.im / s))) < 2 * s := by
  let m : ℤ := Int.floor (w.re / s)
  let n : ℤ := Int.floor (w.im / s)
  let dx : ℝ := w.re - s * (m : ℝ)
  let dy : ℝ := w.im - s * (n : ℝ)
  have hdx0 : 0 ≤ dx := by
    dsimp [dx, m]
    have h := Int.floor_le (w.re / s)
    have h' := (le_div_iff₀ hs).mp h
    nlinarith
  have hdxs : dx < s := by
    dsimp [dx, m]
    have h := Int.lt_floor_add_one (w.re / s)
    rw [div_lt_iff₀ hs] at h
    nlinarith
  have hdy0 : 0 ≤ dy := by
    dsimp [dy, n]
    have h := Int.floor_le (w.im / s)
    have h' := (le_div_iff₀ hs).mp h
    nlinarith
  have hdys : dy < s := by
    dsimp [dy, n]
    have h := Int.lt_floor_add_one (w.im / s)
    rw [div_lt_iff₀ hs] at h
    nlinarith
  have heq : w - gridPoint s m n = (dx : ℂ) + (dy : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [gridPoint, dx, dy]
    · simp [gridPoint, dx, dy]
  rw [Complex.dist_eq, heq]
  calc
    ‖(dx : ℂ) + (dy : ℂ) * Complex.I‖ ≤ ‖(dx : ℂ)‖ + ‖(dy : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = dx + dy := by simp [abs_of_nonneg hdx0, abs_of_nonneg hdy0]
    _ < 2 * s := by linarith

lemma floor_mem_symmetric_Icc {x B : ℝ} (hx : |x| ≤ B) :
    Int.floor x ∈ Set.Icc (-((Nat.ceil (B + 1) : ℕ) : ℤ)) ((Nat.ceil (B + 1) : ℕ) : ℤ) := by
  have hN : B + 1 ≤ (Nat.ceil (B + 1) : ℝ) := Nat.le_ceil _
  have hx' := abs_le.mp hx
  constructor
  · change -((Nat.ceil (B + 1) : ℕ) : ℤ) ≤ Int.floor x
    have hr : -(Nat.ceil (B + 1) : ℝ) ≤ (Int.floor x : ℝ) := by
      nlinarith [Int.floor_le x, Int.lt_floor_add_one x, hx'.1, hN]
    exact_mod_cast hr
  · change Int.floor x ≤ ((Nat.ceil (B + 1) : ℕ) : ℤ)
    have hr : (Int.floor x : ℝ) ≤ Nat.ceil (B + 1) := by
      exact (Int.floor_le x).trans (le_trans hx'.2 (by linarith))
    exact_mod_cast hr

noncomputable def gridBound (r s : ℝ) : ℤ := (Nat.ceil (r / s + 1) : ℤ)

noncomputable def gridBallFinset (s r : ℝ) : Finset ℂ := by
  classical
  let I : Finset ℤ := Finset.Icc (-gridBound r s) (gridBound r s)
  exact ((I.product I).image (fun ij => gridPoint s ij.1 ij.2)).filter
    (fun z => z ∈ ball (0 : ℂ) r)

lemma mem_gridBallFinset_of_mem_box {s r : ℝ} {m n : ℤ}
    (hm : m ∈ Finset.Icc (-gridBound r s) (gridBound r s))
    (hn : n ∈ Finset.Icc (-gridBound r s) (gridBound r s))
    (hz : gridPoint s m n ∈ ball (0 : ℂ) r) :
    gridPoint s m n ∈ gridBallFinset s r := by
  classical
  simp only [gridBallFinset, Finset.mem_filter, Finset.mem_image]
  refine ⟨?_, hz⟩
  refine ⟨(m, n), ?_, rfl⟩
  exact Finset.mem_product.mpr ⟨hm, hn⟩

lemma gridPoint_norm_le_of_close {v z : ℂ} {r t : ℝ} (hv : ‖v‖ ≤ r) (h : dist v z ≤ t) :
    ‖z‖ ≤ r + t := by
  have h' : ‖z - v‖ ≤ t := by simpa [Complex.dist_eq, norm_sub_rev] using h
  have hdecomp : z = (z - v) + v := by abel
  rw [hdecomp]
  calc
    ‖(z - v) + v‖ ≤ ‖z - v‖ + ‖v‖ := norm_add_le _ _
    _ ≤ r + t := by linarith

lemma gridBallFinset_isNet {s D : ℝ} (hs : 0 < s) (hsmall : 3 * s < 2 * D) :
    ∀ w ∈ ball (0 : ℂ) (2 * D),
      ∃ z ∈ gridBallFinset s (2 * D), dist w z ≤ 6 * s := by
  classical
  intro w hw
  let r : ℝ := 2 * D - 3 * s
  let v : ℂ := if ‖w‖ ≤ r then w else (((r / ‖w‖ : ℝ) : ℂ) * w)
  have hrpos : 0 < r := by dsimp [r]; linarith
  have hwnorm : ‖w‖ < 2 * D := by
    simpa [Metric.mem_ball, Complex.dist_eq] using hw
  have hvnorm : ‖v‖ ≤ r := by
    dsimp [v]
    split_ifs with hin
    · exact hin
    · have hden : 0 < ‖w‖ := lt_trans hrpos (lt_of_not_ge hin)
      have hnum : 0 ≤ r := hrpos.le
      rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hnum hden.le)]
      exact le_of_eq (div_mul_cancel₀ r hden.ne')
  let m : ℤ := Int.floor (v.re / s)
  let n : ℤ := Int.floor (v.im / s)
  let z : ℂ := gridPoint s m n
  have hdistvz : dist v z < 2 * s := by
    dsimp [z, m, n]
    exact gridPoint_floor_dist_lt hs v
  have hznorm : ‖z‖ < 2 * D := by
    have hzle := gridPoint_norm_le_of_close (r := r) (t := 2 * s) hvnorm hdistvz.le
    dsimp [r] at hzle
    linarith
  have hvcoord : ‖v‖ ≤ 2 * D := by
    have := hvnorm
    dsimp [r] at this
    linarith
  have hmBound : |v.re / s| ≤ (2 * D) / s := by
    have hcoord : |v.re| ≤ 2 * D := (Complex.abs_re_le_norm v).trans hvcoord
    rw [abs_div, abs_of_pos hs]
    exact (div_le_div_iff_of_pos_right hs).2 hcoord
  have hnBound : |v.im / s| ≤ (2 * D) / s := by
    have hcoord : |v.im| ≤ 2 * D := (Complex.abs_im_le_norm v).trans hvcoord
    rw [abs_div, abs_of_pos hs]
    exact (div_le_div_iff_of_pos_right hs).2 hcoord
  have hm : m ∈ Finset.Icc (-gridBound (2 * D) s) (gridBound (2 * D) s) := by
    dsimp [m]
    simpa [gridBound] using floor_mem_symmetric_Icc hmBound
  have hn : n ∈ Finset.Icc (-gridBound (2 * D) s) (gridBound (2 * D) s) := by
    dsimp [n]
    simpa [gridBound] using floor_mem_symmetric_Icc hnBound
  have hz : z ∈ gridBallFinset s (2 * D) := by
    apply mem_gridBallFinset_of_mem_box hm hn
    simpa [z, Metric.mem_ball, Complex.dist_eq] using hznorm
  have hdistwv : dist w v ≤ 3 * s := by
    dsimp [v]
    split_ifs with hin
    · simp
      positivity
    · have hden : 0 < ‖w‖ := lt_trans hrpos (lt_of_not_ge hin)
      have hnum : 0 ≤ r := hrpos.le
      have hratio : 0 ≤ r / ‖w‖ ∧ r / ‖w‖ < 1 := by
        constructor
        · exact div_nonneg hnum hden.le
        · exact (div_lt_one hden).2 (lt_of_not_ge hin)
      have heq : w - ((r / ‖w‖ : ℝ) : ℂ) * w = ((1 - r / ‖w‖ : ℝ) : ℂ) * w := by
        apply Complex.ext
        · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
          ring
        · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
          ring
      rw [Complex.dist_eq, heq, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hratio.2.le)]
      have hnormeq : (r / ‖w‖) * ‖w‖ = r := div_mul_cancel₀ r hden.ne'
      dsimp [r]
      nlinarith [hwnorm]
  refine ⟨z, hz, ?_⟩
  calc
    dist w z ≤ dist w v + dist v z := dist_triangle w v z
    _ ≤ 3 * s + 2 * s := add_le_add hdistwv hdistvz.le
    _ ≤ 6 * s := by linarith

noncomputable def gridIntervalFinset (s l u : ℝ) : Finset ℝ := by
  classical
  exact Finset.filter (fun r => r ∈ Set.Icc l u)
    ((Finset.Icc (Int.floor (l / s)) (Int.ceil (u / s))).image
      (fun k : ℤ => s * (k : ℝ)))

lemma mem_gridIntervalFinset_of_index {s l u : ℝ} {k : ℤ}
    (hk : k ∈ Finset.Icc (Int.floor (l / s)) (Int.ceil (u / s)))
    (hr : s * (k : ℝ) ∈ Set.Icc l u) :
    s * (k : ℝ) ∈ gridIntervalFinset s l u := by
  classical
  simp only [gridIntervalFinset, Finset.mem_filter]
  constructor
  · apply Finset.mem_image.mpr
    exact ⟨k, hk, rfl⟩
  · exact hr

lemma gridIntervalFinset_isNet {s l u : ℝ} (hs : 0 < s) (hwidth : l + s ≤ u) :
    ∀ t ∈ Set.Icc l u, ∃ r ∈ gridIntervalFinset s l u, dist t r ≤ s := by
  classical
  intro t ht
  let k : ℤ := if l ≤ s * (Int.floor (t / s) : ℝ) then Int.floor (t / s) else Int.ceil (l / s)
  have hfloor_le_t : s * (Int.floor (t / s) : ℝ) ≤ t := by
    have h := Int.floor_le (t / s)
    have h' := (le_div_iff₀ hs).mp h
    nlinarith
  have hceil_lower : l ≤ s * (Int.ceil (l / s) : ℝ) := by
    have h := Int.le_ceil (l / s)
    have h' := (div_le_iff₀ hs).mp h
    nlinarith
  have hceil_upper : s * (Int.ceil (l / s) : ℝ) < l + s := by
    have h := Int.ceil_lt_add_one (l / s)
    have h' := mul_lt_mul_of_pos_left h hs
    have hdiv : s * (l / s) = l := mul_div_cancel₀ l hs.ne'
    rw [mul_add, hdiv] at h'
    nlinarith
  have hkbox : k ∈ Finset.Icc (Int.floor (l / s)) (Int.ceil (u / s)) := by
    dsimp [k]
    split_ifs with hcase
    · simp only [Finset.mem_Icc]
      constructor
      · exact Int.floor_mono ((div_le_div_iff_of_pos_right hs).2 ht.1)
      · exact (Int.floor_mono ((div_le_div_iff_of_pos_right hs).2 ht.2)).trans
          (Int.floor_le_ceil (u / s))
    · simp only [Finset.mem_Icc]
      constructor
      · exact Int.floor_le_ceil (l / s)
      · exact Int.ceil_mono ((div_le_div_iff_of_pos_right hs).2 (le_trans ht.1 ht.2))
  have hrange : s * (k : ℝ) ∈ Set.Icc l u := by
    dsimp [k]
    split_ifs with hcase
    · constructor
      · exact hcase
      · exact hfloor_le_t.trans ht.2
    · constructor
      · exact hceil_lower
      · exact hceil_upper.le.trans hwidth
  have hmem := mem_gridIntervalFinset_of_index hkbox hrange
  refine ⟨s * (k : ℝ), hmem, ?_⟩
  have hdist : |t - s * (k : ℝ)| ≤ s := by
    dsimp [k]
    split_ifs with hcase
    · have hnonneg : 0 ≤ t - s * (Int.floor (t / s) : ℝ) := by linarith
      have hlt : t - s * (Int.floor (t / s) : ℝ) < s := by
        have h := Int.lt_floor_add_one (t / s)
        rw [div_lt_iff₀ hs] at h
        nlinarith
      rw [abs_of_nonneg hnonneg]
      exact hlt.le
    ·
      have hfloorbelow : s * (Int.floor (t / s) : ℝ) < l := by
        exact lt_of_not_ge hcase
      have htUpper : t < l + s := by
        have h := Int.lt_floor_add_one (t / s)
        have h' := mul_lt_mul_of_pos_left h hs
        have hdiv : s * (t / s) = t := mul_div_cancel₀ t hs.ne'
        rw [hdiv] at h'
        nlinarith [hfloorbelow]
      rw [abs_le]
      constructor
      · linarith [hceil_upper, ht.1]
      · linarith [hceil_lower, htUpper]
  simpa [Real.dist_eq, abs_sub_comm] using hdist

end MatedCRTHarmonic.MesoGrid
