import QuantumZipper.Common.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Complex.Basic

/-!
# EXT-RS D2: a Hardy–Littlewood lemma on the upper half-plane

If `f` is holomorphic on `H` and `‖f' z‖ ≤ C · (min 1 (Im z))^(β−1)` on `H ∩ closedBall 0 (R+2)`
with `0 < β ≤ 1`, then `f` is `β`-Hölder on `H ∩ closedBall 0 R`.

Source: Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (Springer 1992), §4.6, eq. (7),
p. 92, and P. Duren, *Theory of Hᵖ Spaces* (Academic Press 1970), §5.2, Theorem 5.1
(Hardy–Littlewood), pp. 74–75, the "if" direction (disk version: integrate `f'` radially and
along a circle; here the half-plane analogue, vertical and horizontal segments); Rohde–Schramm, *Basic properties
of SLE*, proof of Thm 5.2, last paragraph (p. 22). We follow that argument: integrate `f'` along
`z → z + i t → w + i t → w` with `t = min ‖z − w‖ 1`. The vertical pieces are bounded by a
comparison-function (fencing) argument (`image_norm_le_of_norm_deriv_right_le_deriv_boundary'`)
instead of an explicit integral, and the horizontal piece by the mean value inequality.
The clamp `t ≤ 1` (for large `‖z − w‖`) is ours.
-/

noncomputable section

open Complex Set Metric

namespace QuantumZipper
namespace RS

/-- `(min 1 u)^(β−1) ≤ u^(β−1) + 1` for `u > 0`. -/
lemma hl_min_rpow_le {u β : ℝ} (hu : 0 < u) :
    (min 1 u) ^ (β - 1) ≤ u ^ (β - 1) + 1 := by
  rcases le_total 1 u with h | h
  · rw [min_eq_left h, Real.one_rpow]; linarith [Real.rpow_nonneg hu.le (β - 1)]
  · rw [min_eq_right h]; linarith

/-- Vertical piece: `‖f (z + i t) − f z‖ ≤ (C/β) t^β + C t`. -/
theorem hl_vertical {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f H) {C β : ℝ} (hC : 0 ≤ C)
    (hβ : 0 < β) (hβ1 : β ≤ 1) {z : ℂ} (hz : z ∈ H) {t : ℝ} (ht : 0 ≤ t)
    (hbd : ∀ s ∈ Icc (0 : ℝ) t,
      ‖deriv f (z + I * s)‖ ≤ C * (min 1 (z + I * s).im) ^ (β - 1)) :
    ‖f (z + I * t) - f z‖ ≤ C / β * t ^ β + C * t := by
  have hy : 0 < z.im := hz
  set y := z.im
  have him : ∀ s : ℝ, (z + I * s).im = y + s := fun s => by simp [y]
  set φ : ℝ → ℂ := fun s => f (z + I * s) - f z
  set B : ℝ → ℝ := fun s => C / β * ((y + s) ^ β - y ^ β) + C * s
  have hγ : ∀ s : ℝ, HasDerivAt (fun x : ℝ => z + I * (x : ℂ)) I s := fun s => by
    simpa using ((hasDerivAt_id s).ofReal_comp.const_mul I).const_add z
  have hφ : ∀ s : ℝ, 0 ≤ s → HasDerivAt φ (deriv f (z + I * s) * I) s := by
    intro s hs
    have hmem : z + I * s ∈ H := show 0 < (z + I * s).im by rw [him]; linarith
    have hfd : DifferentiableAt ℂ f (z + I * s) := hf.differentiableAt (isOpen_H.mem_nhds hmem)
    exact (hfd.hasDerivAt.comp s (hγ s)).sub_const (f z)
  have hB : ∀ s : ℝ, 0 ≤ s → HasDerivAt B (C * (y + s) ^ (β - 1) + C) s := by
    intro s hs
    have h1 : HasDerivAt (fun x : ℝ => (y + x) ^ β) (1 * β * (y + s) ^ (β - 1)) s :=
      ((hasDerivAt_id s).const_add y).rpow_const (Or.inl (by simp; linarith))
    have h2 := ((h1.sub_const (y ^ β)).const_mul (C / β)).add ((hasDerivAt_id s).const_mul C)
    have hβ0 := hβ.ne'
    refine h2.congr_deriv ?_
    rw [one_mul, mul_one, ← mul_assoc, div_mul_cancel₀ C hβ0]
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary' (a := 0) (b := t) (f := φ)
    (f' := fun s => deriv f (z + I * s) * I) (B := B) (B' := fun s => C * (y + s) ^ (β - 1) + C)
    (fun s hs => (hφ s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hφ s hs.1).hasDerivWithinAt)
    (by simp [φ, B])
    (fun s hs => (hB s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hB s hs.1).hasDerivWithinAt)
    (by
      intro s hs
      have hs' : s ∈ Icc (0 : ℝ) t := ⟨hs.1, hs.2.le⟩
      rw [norm_mul, Complex.norm_I, mul_one]
      refine (hbd s hs').trans ?_
      rw [him]
      have := hl_min_rpow_le (β := β) (show 0 < y + s by linarith [hs.1])
      nlinarith)
    (x := t) ⟨ht, le_rfl⟩
  refine key.trans ?_
  simp only [B]
  have hsub := Real.rpow_add_le_add_rpow hy.le ht hβ.le hβ1
  have : 0 ≤ C / β := div_nonneg hC hβ.le
  nlinarith

/-- Vertical piece, clamped: for `t ≤ 1`, `‖f (z + i t) − f z‖ ≤ (C/β + C) t^β`. -/
theorem hl_vertical' {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f H) {C β : ℝ} (hC : 0 ≤ C)
    (hβ : 0 < β) (hβ1 : β ≤ 1) {z : ℂ} (hz : z ∈ H) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hbd : ∀ s ∈ Icc (0 : ℝ) t,
      ‖deriv f (z + I * s)‖ ≤ C * (min 1 (z + I * s).im) ^ (β - 1)) :
    ‖f (z + I * t) - f z‖ ≤ (C / β + C) * t ^ β := by
  have h := hl_vertical hf hC hβ hβ1 hz ht hbd
  have h2 : t ≤ t ^ β := Real.self_le_rpow_of_le_one ht ht1 hβ1
  nlinarith

/-- **D2 (Hardy–Littlewood).** Pommerenke, *Boundary Behaviour*, §4.6 eq. (7), p. 92. -/
theorem hardyLittlewood_holder {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f H) {C β R : ℝ}
    (hC : 0 ≤ C) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hbd : ∀ p ∈ H, ‖p‖ ≤ R + 2 → ‖deriv f p‖ ≤ C * (min 1 p.im) ^ (β - 1)) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ z ∈ H, ∀ w ∈ H, ‖z‖ ≤ R → ‖w‖ ≤ R →
      ‖f z - f w‖ ≤ C' * ‖z - w‖ ^ β := by
  have hCβ : 0 ≤ C / β + C := by positivity
  refine ⟨2 * (C / β + C) + C * max 1 (2 * R), by positivity, ?_⟩
  intro z hz w hw hzR hwR
  set h := ‖z - w‖ with hh
  rcases (norm_nonneg (z - w)).eq_or_lt with h0 | hpos
  · have : z = w := sub_eq_zero.1 (norm_eq_zero.1 h0.symm)
    subst this; rw [hh, ← h0, Real.zero_rpow hβ.ne', mul_zero]; simp
  set t := min h 1 with htdef
  have ht0 : 0 < t := lt_min hpos one_pos
  have ht1 : t ≤ 1 := min_le_right _ _
  have hth : t ≤ h := min_le_left _ _
  have htβ : t ^ β ≤ h ^ β := Real.rpow_le_rpow ht0.le hth hβ.le
  have hnormI : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ u : ℂ, ‖u‖ ≤ R → ‖u + I * s‖ ≤ R + 2 := by
    intro s hs0 hs1 u hu
    have := norm_add_le u (I * s)
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hs0] at this
    linarith
  have hvert : ∀ u ∈ H, ‖u‖ ≤ R → ‖f (u + I * t) - f u‖ ≤ (C / β + C) * t ^ β := by
    intro u hu huR
    refine hl_vertical' hf hC hβ hβ1 hu ht0.le ht1 fun s hs => hbd _ ?_ ?_
    · have hu' : 0 < u.im := hu
      show 0 < (u + I * s).im; simp; linarith [hs.1]
    · exact hnormI s hs.1 (hs.2.trans ht1) u huR
  -- horizontal piece
  set a := z + I * t
  set b := w + I * t
  have hseg : ∀ p ∈ segment ℝ a b, t ≤ p.im ∧ ‖p‖ ≤ R + 2 := by
    intro p hp
    obtain ⟨μ, ν, hμ, hν, hμν, rfl⟩ := hp
    have hz' : 0 < z.im := hz
    have hw' : 0 < w.im := hw
    constructor
    · simp [a, b]
      nlinarith
    · have ha := hnormI t ht0.le ht1 z hzR
      have hb := hnormI t ht0.le ht1 w hwR
      calc ‖μ • a + ν • b‖ ≤ μ * ‖a‖ + ν * ‖b‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, norm_smul, Real.norm_of_nonneg hμ, Real.norm_of_nonneg hν]
        _ ≤ μ * (R + 2) + ν * (R + 2) := by gcongr
        _ = R + 2 := by rw [← add_mul, hμν, one_mul]
  have hhor : ‖f b - f a‖ ≤ C * t ^ (β - 1) * ‖b - a‖ := by
    refine (convex_segment a b).norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ) ?_ ?_
      (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
    · intro p hp
      have : p ∈ H := show 0 < p.im from ht0.trans_le (hseg p hp).1
      exact hf.differentiableAt (isOpen_H.mem_nhds this)
    · intro p hp
      obtain ⟨h1, h2⟩ := hseg p hp
      have hpH : p ∈ H := show 0 < p.im from ht0.trans_le h1
      refine (hbd p hpH h2).trans ?_
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos ht0 (le_min ht1 h1) (by linarith : β - 1 ≤ 0)) hC
  have hba : ‖b - a‖ = h := by
    rw [hh, ← norm_neg]; congr 1; simp [a, b]
  rw [hba] at hhor
  have hhor' : C * t ^ (β - 1) * h ≤ C * max 1 (2 * R) * h ^ β := by
    rcases le_total h 1 with h1 | h1
    · have : t = h := min_eq_left h1
      rw [this, mul_assoc, ← Real.rpow_add_one hpos.ne', sub_add_cancel]
      have e : ‖z - w‖ = h := hh.symm
      simp only [e]
      exact mul_le_mul_of_nonneg_right ((mul_one C).symm.le.trans (mul_le_mul_of_nonneg_left (le_max_left 1 (2 * R)) hC))
        (Real.rpow_nonneg (e ▸ hpos.le) β)
    · have : t = 1 := min_eq_right h1
      rw [this, Real.one_rpow, mul_one, mul_assoc]
      gcongr
      have hh2 : h ≤ 2 * R := by
        have := norm_sub_le z w; rw [← hh] at this; linarith
      have : 1 ≤ h ^ β := Real.one_le_rpow h1 hβ.le
      calc h ≤ max 1 (2 * R) := hh2.trans (le_max_right _ _)
        _ = max 1 (2 * R) * 1 := (mul_one _).symm
        _ ≤ max 1 (2 * R) * h ^ β := by gcongr
  have hz1 := hvert z hz hzR
  have hw1 := hvert w hw hwR
  have htri : ‖f z - f w‖ ≤ ‖f a - f z‖ + ‖f b - f a‖ + ‖f b - f w‖ := by
    calc ‖f z - f w‖ = ‖-(f a - f z) + (f a - f b) + (f b - f w)‖ := by congr 1; ring
      _ ≤ ‖-(f a - f z) + (f a - f b)‖ + ‖f b - f w‖ := norm_add_le _ _
      _ ≤ ‖f a - f z‖ + ‖f b - f a‖ + ‖f b - f w‖ := by
          gcongr
          refine (norm_add_le _ _).trans ?_
          rw [norm_neg, norm_sub_rev (f a) (f b)]
  nlinarith [mul_le_mul_of_nonneg_left htβ hCβ]

end RS
end QuantumZipper
