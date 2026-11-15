/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedImageCancel

/-!
# A uniform bound for the seeded logarithmic noise

Packet PROVE-ZHAN-GT4-A22. The apparent seed poles cancel before taking
bounds. Only the separated original source gap needs a positive lower bound.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4
namespace SeedData

/-- A deterministic bound for the cancelled logarithmic noise. -/
def noiseBound {n : ℕ} (κ : ℝ) (rr : Fin n → ℝ) (r L₀ Lrem c₀ : ℝ) : ℝ :=
  (|dualAlpha κ| + ∑ m, |rr m|) * ((384 / r) / Real.exp (-L₀)) +
    1 / 2 * (Real.exp L₀ / (Real.exp (-Lrem) * c₀) + 1 / c₀)

/-- Expand the difference of the spatial log derivatives after cancelling
its original and image seed contributions. -/
theorem ellX_driver_eq_cancelled {n : ℕ} (s : SeedData n) (t : ℝ) :
    s.ellX t (s.W t) = dualAlpha s.κ * (s.A 2 t / s.A 1 t) -
      1 / 2 * (s.A 1 t / (s.A 0 t - s.A20 t) - 1 / (s.W t - s.V₀ t)) +
      ∑ m, s.r m * (s.A 1 t / (s.A 0 t - s.B0 t m) - 1 / (s.W t - s.V m t)) := by
  simp only [ellX, F_driver, dualLogSpaceX, zero_div, mul_zero, Vv]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  ring

/-- Clear interval geometry bounds the noise even at coincident own seeds. -/
theorem abs_ellX_driver_le {n : ℕ} (s : SeedData n) {A : Set ℂ}
    {T t r L₀ Lrem c₀ : ℝ} {I : Set ℝ}
    (h : OwnData s.W A s.φ T s.a s.W') (ht : t ∈ Icc (0 : ℝ) T)
    (hr : 0 < r) (hc₀ : 0 < c₀) (hI : Convex ℝ I)
    (hW : s.W t ∈ I) (hV : ∀ m, s.V m t ∈ I)
    (hclear : ∀ x ∈ I, Disjoint (ball (x : ℂ) r)
      ((fun z => QuantumZipper.fwdMap s.W t z + s.W t) '' A))
    (hb : ∀ x ∈ I, deriv (s.F 0 t) x ∈ Icc (Real.exp (-L₀)) (Real.exp L₀))
    (hremote : s.RemoteScale t Lrem) (hgap : c₀ ≤ |s.W t - s.V₀ t|) :
    |s.ellX t (s.W t)| ≤ noiseBound s.κ s.r r L₀ Lrem c₀ := by
  have hfd : ∀ x ∈ I, HasDerivAt (s.F 0 t) (s.F 1 t x) x := by
    intro x hx
    have hd := (h.ownExt_props ht (hclear x hx)).1
    have hd' := hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))
    change HasDerivAt (fun y : ℝ => (ownExt s.W s.W' s.a s.φ t y).re)
      (deriv (ownExt s.W s.W' s.a s.φ t) x).re x
    exact hd'.hasDerivAt.real_of_complex
  have hsd : ∀ x ∈ I, HasDerivAt (s.F 1 t) (s.F 2 t x) x := by
    intro x hx
    have hder := (h.ownExt_props ht (hclear x hx)).1.deriv isOpen_ball
    have hd := hder.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))
    change HasDerivAt (fun y : ℝ => (deriv (ownExt s.W s.W' s.a s.φ t) y).re)
      (deriv (deriv (ownExt s.W s.W' s.a s.φ t)) x).re x
    exact hd.hasDerivAt.real_of_complex
  have h₂ : ∀ x ∈ I, |s.F 2 t x| ≤ 384 / r := by
    intro x hx
    exact (Complex.abs_re_le_norm _).trans
      (h.norm_deriv2_ownExt_le ht (hclear x hx) (mem_ball_self (by positivity)))
  have h₁ : ∀ x ∈ I, Real.exp (-L₀) ≤ s.F 1 t x := by
    intro x hx
    rw [← (hfd x hx).deriv]
    exact (hb x hx).1
  have hA1p : 0 < s.A 1 t := (Real.exp_pos _).trans_le (h₁ _ hW)
  have hA1b : |s.A 1 t| ≤ Real.exp L₀ := by
    rw [abs_of_pos hA1p, ← s.F_driver 1, ← (hfd _ hW).deriv]
    exact (hb _ hW).2
  have hquot : |s.A 2 t / s.A 1 t| ≤ (384 / r) / Real.exp (-L₀) := by
    rw [abs_div, abs_of_pos hA1p]
    exact (div_le_div_of_nonneg_right (h₂ _ hW) hA1p.le).trans
      (div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) (h₁ _ hW))
  have hmark : ∀ m, |s.A 1 t / (s.A 0 t - s.B0 t m) - 1 / (s.W t - s.V m t)| ≤
      (384 / r) / Real.exp (-L₀) := fun m =>
    abs_reciprocal_cancel_le hI hfd hsd (Real.exp_pos _) (by positivity) h₁ h₂ hW (hV m)
  have hgp := hc₀.trans_le hgap
  have hrem : Real.exp (-Lrem) * |s.W t - s.V₀ t| ≤ |s.A 0 t - s.A20 t| := by
    have hh := hremote.driver.1
    rw [abs_div] at hh
    exact (le_div_iff₀ hgp).1 hh
  have himg : Real.exp (-Lrem) * c₀ ≤ |s.A 0 t - s.A20 t| :=
    (mul_le_mul_of_nonneg_left hgap (Real.exp_pos _).le).trans hrem
  have hip : 0 < |s.A 0 t - s.A20 t| := (mul_pos (Real.exp_pos _) hc₀).trans_le himg
  have hother : |s.A 1 t / (s.A 0 t - s.A20 t) - 1 / (s.W t - s.V₀ t)| ≤
      Real.exp L₀ / (Real.exp (-Lrem) * c₀) + 1 / c₀ := by
    apply (abs_sub _ _).trans
    apply add_le_add
    · rw [abs_div]
      exact (div_le_div_of_nonneg_right hA1b hip.le).trans
        (div_le_div_of_nonneg_left (Real.exp_pos _).le (mul_pos (Real.exp_pos _) hc₀) himg)
    · rw [abs_div, abs_one]
      exact div_le_div_of_nonneg_left zero_le_one hc₀ hgap
  rw [s.ellX_driver_eq_cancelled]
  have hm := abs_sum_mul_le (r := s.r) hmark
  have hq := mul_le_mul_of_nonneg_left hquot (abs_nonneg (dualAlpha s.κ))
  have ho := mul_le_mul_of_nonneg_left hother (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [← abs_mul] at hq
  have ho' : |1 / 2 * (s.A 1 t / (s.A 0 t - s.A20 t) - 1 / (s.W t - s.V₀ t))| ≤
      1 / 2 * (Real.exp L₀ / (Real.exp (-Lrem) * c₀) + 1 / c₀) := by
    rwa [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have htri := abs_add_le
    (dualAlpha s.κ * (s.A 2 t / s.A 1 t) -
      1 / 2 * (s.A 1 t / (s.A 0 t - s.A20 t) - 1 / (s.W t - s.V₀ t)))
    (∑ m, s.r m * (s.A 1 t / (s.A 0 t - s.B0 t m) - 1 / (s.W t - s.V m t)))
  have htri' := abs_sub (dualAlpha s.κ * (s.A 2 t / s.A 1 t))
    (1 / 2 * (s.A 1 t / (s.A 0 t - s.A20 t) - 1 / (s.W t - s.V₀ t)))
  unfold noiseBound
  linarith only [htri, htri', hq, ho', hm]

end SeedData
end InteractingSLE.ZhanGT4
