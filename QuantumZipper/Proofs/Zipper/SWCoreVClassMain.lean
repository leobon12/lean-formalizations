import QuantumZipper.Proofs.Zipper.SWCoreVClass

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-V-CLASS: the rescaling theorem for the boundary map class

Task SWC-V-CLASS (helper of SWC-V, `handoff/SW-CORE.md` §5). Sheffield–Wang, arXiv:1605.06171,
Lemma 3.4, (3.17)–(3.19), p. 15, for the rational class `BdryClass a b ρ M m` (derivative bounds
by Cauchy's estimates instead of de Branges/Koebe; see `SWCoreVClass.lean`).

`bdryClass_rescale`: uniformly over the class, over `t ∈ [a,b]` and over `r ∈ (0, r₀)`, with
`D = ψ'(t)` (real, `m ≤ D ≤ C`) and `T u = (ψ(t + r u) − ψ(t)) / (r D)`:
`‖T u − u‖ ≤ C r` on the closed unit disc, `T` is `(1/2, 2)`-bi-Lipschitz there, maps the closed
upper half of the disc into the closed upper half plane, and is continuous on the disc.
-/

noncomputable section

open Metric Set Filter
open scoped Topology

namespace QuantumZipper
namespace SWCore

lemma swcv_mem {t r : ℝ} (hr : 0 ≤ r) {u : ℂ} (hu : u ∈ closedBall (0 : ℂ) 1) :
    (t : ℂ) + r * u ∈ closedBall (t : ℂ) r := by
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_of_nonneg hr]
  rw [mem_closedBall, dist_zero_right] at hu
  nlinarith [norm_nonneg u]

/-- **Rescaling estimates for the boundary class** (SW Lemma 3.4, (3.17)–(3.19), p. 15, in the
form needed for the class `BdryClass a b ρ M m`). -/
theorem bdryClass_rescale (a b ρ M m : ℝ) (hab : a < b) (hρ : 0 < ρ) (hm : 0 < m) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ BdryClass a b ρ M m, ∀ t ∈ Icc a b,
      ∀ r ∈ Ioo 0 r₀,
      let D : ℝ := (deriv ψ t).re
      let T : ℂ → ℂ := fun u => (ψ (t + r * u) - ψ t) / (r * D)
      (deriv ψ t = (D : ℂ) ∧ m ≤ D ∧ D ≤ C) ∧
      (∀ u ∈ closedBall (0 : ℂ) 1, ‖T u - u‖ ≤ C * r) ∧
      (∀ u ∈ closedBall (0 : ℂ) 1, ∀ v ∈ closedBall (0 : ℂ) 1,
        ‖u - v‖ / 2 ≤ ‖T u - T v‖ ∧ ‖T u - T v‖ ≤ 2 * ‖u - v‖) ∧
      (∀ u ∈ closedBall (0 : ℂ) 1, 0 ≤ u.im → 0 ≤ (T u).im) ∧
      ContinuousOn T (closedBall 0 1) := by
  set K₁ := (|M| + 1) / (ρ / 4) with hK₁
  set K := (|M| + 1) / (ρ / 4) / (ρ / 4) with hK
  have hK₁0 : 0 < K₁ := by positivity
  have hK0 : 0 < K := by positivity
  refine ⟨min (ρ / 4) (m / (2 * K)), lt_min (by positivity) (by positivity), max K₁ (K / m),
    le_max_of_le_left hK₁0.le, ?_⟩
  intro ψ hψ t ht r hr D T
  obtain ⟨hr0, hr1⟩ := hr
  have hrρ : r < ρ / 4 := hr1.trans_le (min_le_left _ _)
  have hrK : r < m / (2 * K) := hr1.trans_le (min_le_right _ _)
  obtain ⟨hDeq0, hmD⟩ := swcv_deriv_real hψ hρ hab ht
  have hDeq : deriv ψ t = (D : ℂ) := hDeq0
  have hD0 : 0 < D := hm.trans_le hmD
  have hDK : D ≤ K₁ :=
    (Complex.re_le_norm _).trans (swcv_deriv_bound hψ hρ ht (mem_ball_self (by positivity)))
  set ε := K * r / D with hε
  have hε0 : 0 ≤ ε := by positivity
  have hεm : ε ≤ K * r / m := div_le_div_of_nonneg_left (by positivity) hm hmD
  have hε2 : ε ≤ 1 / 2 := by
    refine hεm.trans ?_
    rw [div_le_iff₀ hm]
    have h1 : K * r < K * (m / (2 * K)) := mul_lt_mul_of_pos_left hrK hK0
    have h3 : K * (m / (2 * K)) = m / 2 := by field_simp
    linarith
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr0.ne'
  have hD' : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hD0.ne'
  have hnrD : ‖(r : ℂ) * (D : ℂ)‖ = r * D := by
    rw [norm_mul, Complex.norm_of_nonneg hr0.le, Complex.norm_of_nonneg hD0.le]
  have hE : ∀ u ∈ closedBall (0 : ℂ) 1, ∀ v ∈ closedBall (0 : ℂ) 1,
      ‖(T u - T v) - (u - v)‖ ≤ ε * ‖u - v‖ := by
    intro u hu v hv
    have hL := swcv_lip hψ hρ ht hrρ (swcv_mem hr0.le hu) (swcv_mem hr0.le hv)
    have hid : (T u - T v) - (u - v) =
        ((ψ (t + r * u) - deriv ψ t * (t + r * u)) - (ψ (t + r * v) - deriv ψ t * (t + r * v)))
          / (r * D) := by
      simp only [T]
      rw [hDeq]
      field_simp
      ring
    rw [hid, norm_div, hnrD, div_le_iff₀ (by positivity)]
    have hzw : ‖((t : ℂ) + r * u) - (t + r * v)‖ = r * ‖u - v‖ := by
      rw [show ((t : ℂ) + r * u) - (t + r * v) = r * (u - v) by ring, norm_mul,
        Complex.norm_of_nonneg hr0.le]
    rw [hzw] at hL
    calc _ ≤ K * r * (r * ‖u - v‖) := hL
      _ = ε * ‖u - v‖ * (r * D) := by rw [hε]; field_simp
  have hT0 : T 0 = 0 := by simp [T]
  refine ⟨⟨hDeq, hmD, hDK.trans (le_max_left _ _)⟩, ?_, ?_, ?_, ?_⟩
  · intro u hu
    have h := hE u hu 0 (mem_closedBall_self zero_le_one)
    rw [hT0, sub_zero, sub_zero] at h
    have hu1 : ‖u‖ ≤ 1 := by simpa using hu
    calc ‖T u - u‖ ≤ ε * ‖u‖ := h
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hu1 hε0
      _ ≤ K * r / m := by rw [mul_one]; exact hεm
      _ = K / m * r := by ring
      _ ≤ max K₁ (K / m) * r := mul_le_mul_of_nonneg_right (le_max_right _ _) hr0.le
  · intro u hu v hv
    have h := hE u hu v hv
    have h1 := norm_sub_norm_le (T u - T v) (u - v)
    have h2 := norm_sub_norm_le (u - v) (T u - T v)
    rw [norm_sub_rev (u - v) (T u - T v)] at h2
    have hn := norm_nonneg (u - v)
    have h3 : ε * ‖u - v‖ ≤ 1 / 2 * ‖u - v‖ := mul_le_mul_of_nonneg_right hε2 hn
    constructor <;> linarith
  · intro u hu hu0
    set v : ℂ := (u.re : ℂ) with hv
    have hvmem : v ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall, dist_zero_right, hv, Complex.norm_real, Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm u).trans (by simpa using hu)
    have hpt : ((t + r * u.re : ℝ) : ℂ) = (t : ℂ) + r * v := by rw [hv]; push_cast; ring
    have hTv : (T v).im = 0 := by
      have hreal : (ψ ((t + r * u.re : ℝ) : ℂ)).im = 0 := by
        apply swcv_real hψ hρ hab
        apply swcv_ball_sub ht
        rw [hpt]
        exact ball_subset_ball (by linarith)
          (closedBall_subset_ball hrρ (swcv_mem hr0.le hvmem))
      simp only [T]
      rw [show (r : ℂ) * (D : ℂ) = ((r * D : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_im,
        Complex.sub_im, ← hpt, hreal, hψ.2.2.1 t ht]
      simp
    have h := abs_le.1 ((Complex.abs_im_le_norm _).trans (hE u hu v hvmem))
    have hn : ‖u - v‖ ≤ u.im := by
      have := Complex.norm_le_abs_re_add_abs_im (u - v)
      simpa [hv, abs_of_nonneg hu0] using this
    have key : (T u).im = (T v).im + (u - v).im + ((T u - T v) - (u - v)).im := by
      simp only [Complex.sub_im]
      ring
    have hui : (u - v).im = u.im := by simp [hv]
    rw [key, hTv, hui]
    have h4 : ε * ‖u - v‖ ≤ ε * u.im := mul_le_mul_of_nonneg_left hn hε0
    have h5 : ε * u.im ≤ 1 / 2 * u.im := mul_le_mul_of_nonneg_right hε2 hu0
    linarith
  · have hcont : ContinuousOn ψ (thickening ρ (segC a b)) := hψ.1.continuousOn
    have hmaps : MapsTo (fun u : ℂ => (t : ℂ) + r * u) (closedBall 0 1)
        (thickening ρ (segC a b)) := fun u hu =>
      swcv_ball_sub ht (ball_subset_ball (by linarith)
        (closedBall_subset_ball hrρ (swcv_mem hr0.le hu)))
    exact ((hcont.comp (by fun_prop : Continuous fun u : ℂ => (t : ℂ) + r * u).continuousOn
      hmaps).sub continuousOn_const).div_const ((r : ℂ) * D)

end SWCore
end QuantumZipper
