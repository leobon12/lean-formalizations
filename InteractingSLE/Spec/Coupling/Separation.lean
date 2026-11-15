import InteractingSLE.Spec.Ito.Loewner

/-!
# Two points stay separated under the forward Loewner flow

Packet PROVE-T11-L311 (Specification §3.3, L519–L548: the two-point identities (3.16)–(3.17) and their integration
against test functions in (3.19)). PROVE-T11-ITO's two-point martingale `exists_martingale_couplingMean_mul_add_greenH`
needs a deterministic lower bound `ε ≤ ‖f_s(y) − f_s(z)‖` on `[0, σ]`. It holds with an explicit `ε`:

* `monotoneOn_sepRatio`: for `y, z` not swallowed by time `T`, the ratio
  `‖f_s(y) − f_s(z)‖² / (Im f_s(y) · Im f_s(z))` is nondecreasing on `[0, T]` (it is `2 (cosh d − 1)` for the
  hyperbolic distance `d` of `ℍ`, and the inverse Loewner maps are holomorphic self-maps of `ℍ`). Proof: with
  `u = f_s(y)`, `v = f_s(z)`, `D = u − v`, `a = Im u`, `b = Im v`, one has `D' = −2D/(uv)`, `a' = −2a/‖u‖²`,
  `b' = −2b/‖v‖²`, so the logarithmic derivative of the ratio is
  `−4 Re(1/(uv)) + 2/‖u‖² + 2/‖v‖² ≥ 2 (1/‖u‖ − 1/‖v‖)² ≥ 0`;
* `norm_sub_sq_mul_le`: `‖y − z‖² · Im f_s(y) · Im f_s(z) ≤ ‖f_s(y) − f_s(z)‖² · Im y · Im z`;
* `le_norm_fwdMap_sub`: hence `‖y − z‖ δ / √(Im y Im z) ≤ ‖f_s(y) − f_s(z)‖` whenever `δ ≤ Im f_s(y), Im f_s(z)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology QuantumZipper

namespace InteractingSLE

namespace Coupling

variable {W : ℝ → ℝ} {y z : ℂ} {T : ℝ}

/-- The separation ratio `‖f_s(y) − f_s(z)‖² / (Im f_s(y) · Im f_s(z))`. -/
def sepRatio (W : ℝ → ℝ) (y z : ℂ) (s : ℝ) : ℝ :=
  ‖fwdMap W s y - fwdMap W s z‖ ^ 2 / ((fwdMap W s y).im * (fwdMap W s z).im)

/-- The key algebraic inequality: `−4 Re(1/(uv)) + 2/‖u‖² + 2/‖v‖² ≥ 0`. -/
theorem sep_bracket_nonneg (u v : ℂ) :
    0 ≤ -4 * (1 / (u * v)).re + 2 / ‖u‖ ^ 2 + 2 / ‖v‖ ^ 2 := by
  have h1 : (1 / (u * v)).re ≤ 1 / ‖u‖ * (1 / ‖v‖) := by
    refine (Complex.re_le_norm _).trans (le_of_eq ?_)
    rw [norm_div, norm_one, norm_mul]
    by_cases hu : ‖u‖ = 0
    · simp [hu]
    by_cases hv : ‖v‖ = 0
    · simp [hv]
    field_simp
  have h2 : 0 ≤ 2 * (1 / ‖u‖ - 1 / ‖v‖) ^ 2 := by positivity
  have e : 2 / ‖u‖ ^ 2 + 2 / ‖v‖ ^ 2 = 2 * (1 / ‖u‖ - 1 / ‖v‖) ^ 2 + 4 * (1 / ‖u‖ * (1 / ‖v‖)) := by
    ring
  linarith

theorem inner_mul_self_right (D c : ℂ) : inner ℝ D (c * D) = c.re * ‖D‖ ^ 2 := by
  rw [Complex.inner, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem im_two_div (u : ℂ) : (2 / u).im = -2 * u.im / ‖u‖ ^ 2 := by
  rw [Complex.div_im, ← Complex.normSq_eq_norm_sq]
  simp
  ring

/-- **Monotonicity of the separation ratio.** For a continuous driver and `y, z` not swallowed by time `T`,
`s ↦ ‖f_s(y) − f_s(z)‖² / (Im f_s(y) · Im f_s(z))` is nondecreasing on `[0, T]`. -/
theorem monotoneOn_sepRatio (hW : Continuous W) (hT : 0 ≤ T) (hy : y ∈ H \ fwdHull W T)
    (hz : z ∈ H \ fwdHull W T) : MonotoneOn (sepRatio W y z) (Icc 0 T) := by
  set u : ℝ → ℂ := fun s => fwdMap W s y with hu
  set v : ℝ → ℂ := fun s => fwdMap W s z with hv
  have hD : ∀ s ∈ Icc 0 T, HasDerivWithinAt (fun r => u r - v r) (2 / u s - 2 / v s) (Icc 0 T) s := by
    intro s hs
    have h := (Ito.hasDerivWithinAt_fwdMap_add hW hT hy hs).sub
      (Ito.hasDerivWithinAt_fwdMap_add hW hT hz hs)
    refine h.congr (fun r _ => ?_) ?_ <;> simp [hu, hv]
  have him : ∀ x ∈ ({y, z} : Set ℂ), x ∈ H \ fwdHull W T → ∀ s ∈ Icc 0 T,
      HasDerivWithinAt (fun r => (fwdMap W r x).im) (2 / fwdMap W s x).im (Icc 0 T) s := by
    intro x _ hx s hs
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt s
      (Ito.hasDerivWithinAt_fwdMap_add hW hT hx hs)
    refine (h.congr (fun r _ => ?_) ?_) <;> simp
  have ha := him y (by simp) hy
  have hb := him z (by simp) hz
  have hapos : ∀ s ∈ Icc 0 T, 0 < (u s).im := fun s hs => Ito.im_fwdMap_pos hW hT hy hs
  have hbpos : ∀ s ∈ Icc 0 T, 0 < (v s).im := fun s hs => Ito.im_fwdMap_pos hW hT hz hs
  have hune : ∀ s ∈ Icc 0 T, u s ≠ 0 := fun s hs => Ito.fwdMap_ne_zero hW hT hy hs
  have hvne : ∀ s ∈ Icc 0 T, v s ≠ 0 := fun s hs => Ito.fwdMap_ne_zero hW hT hz hs
  have hR : ∀ s ∈ Icc 0 T, HasDerivWithinAt (sepRatio W y z)
      ((2 * inner ℝ (u s - v s) (2 / u s - 2 / v s) * ((u s).im * (v s).im) -
        ‖u s - v s‖ ^ 2 * ((2 / u s).im * (v s).im + (u s).im * (2 / v s).im)) /
          ((u s).im * (v s).im) ^ 2) (Icc 0 T) s := fun s hs =>
    ((hD s hs).norm_sq.div ((ha s hs).mul (hb s hs))
      (mul_pos (hapos s hs) (hbpos s hs)).ne')
  have hnonneg : ∀ s ∈ Icc 0 T, 0 ≤ (2 * inner ℝ (u s - v s) (2 / u s - 2 / v s) *
      ((u s).im * (v s).im) - ‖u s - v s‖ ^ 2 * ((2 / u s).im * (v s).im + (u s).im * (2 / v s).im)) /
        ((u s).im * (v s).im) ^ 2 := by
    intro s hs
    refine div_nonneg ?_ (sq_nonneg _)
    have e1 : 2 / u s - 2 / v s = (-2 / (u s * v s)) * (u s - v s) := by
      field_simp [hune s hs, hvne s hs]
      ring
    have e2 : (-2 / (u s * v s)).re = -2 * (1 / (u s * v s)).re := by
      rw [show (-2 / (u s * v s)) = (-2 : ℝ) * (1 / (u s * v s)) by push_cast; ring,
        Complex.re_ofReal_mul]
    rw [e1, inner_mul_self_right, e2, im_two_div, im_two_div]
    have hu2 : 0 < ‖u s‖ ^ 2 := by have := norm_pos_iff.2 (hune s hs); positivity
    have hv2 : 0 < ‖v s‖ ^ 2 := by have := norm_pos_iff.2 (hvne s hs); positivity
    have key : 2 * (-2 * (1 / (u s * v s)).re * ‖u s - v s‖ ^ 2) * ((u s).im * (v s).im) -
        ‖u s - v s‖ ^ 2 * (-2 * (u s).im / ‖u s‖ ^ 2 * (v s).im +
          (u s).im * (-2 * (v s).im / ‖v s‖ ^ 2)) =
        ‖u s - v s‖ ^ 2 * ((u s).im * (v s).im) *
          (-4 * (1 / (u s * v s)).re + 2 / ‖u s‖ ^ 2 + 2 / ‖v s‖ ^ 2) := by
      field_simp
      ring
    rw [key]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (mul_pos (hapos s hs) (hbpos s hs)).le)
      (sep_bracket_nonneg _ _)
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T)
    (fun s hs => (hR s hs).continuousWithinAt)
    (fun s hs => (hR s (interior_subset hs)).mono interior_subset)
    (fun s hs => hnonneg s (interior_subset hs))

theorem fwdMap_zero_of_mem (hW : Continuous W) (hT : 0 ≤ T) (hz : z ∈ H \ fwdHull W T) :
    fwdMap W 0 z = z - W 0 := by
  have h := Ito.fwdMap_eq_sub_add_integral hW hT hz (s := 0) ⟨le_rfl, hT⟩
  rw [intervalIntegral.integral_same, add_zero] at h
  exact h

/-- **Separation of two points**: `‖y − z‖² · Im f_s(y) · Im f_s(z) ≤ ‖f_s(y) − f_s(z)‖² · Im y · Im z`. -/
theorem norm_sub_sq_mul_le (hW : Continuous W) (hT : 0 ≤ T) (hy : y ∈ H \ fwdHull W T)
    (hz : z ∈ H \ fwdHull W T) {s : ℝ} (hs : s ∈ Icc 0 T) :
    ‖y - z‖ ^ 2 * ((fwdMap W s y).im * (fwdMap W s z).im) ≤
      ‖fwdMap W s y - fwdMap W s z‖ ^ 2 * (y.im * z.im) := by
  have h := monotoneOn_sepRatio hW hT hy hz ⟨le_rfl, hT⟩ hs hs.1
  have hpos : ∀ x : ℂ, x ∈ H \ fwdHull W T → 0 < (fwdMap W s x).im := fun x hx =>
    Ito.im_fwdMap_pos hW hT hx hs
  have hy0 : 0 < y.im := hy.1
  have hz0 : 0 < z.im := hz.1
  simp only [sepRatio, fwdMap_zero_of_mem hW hT hy, fwdMap_zero_of_mem hW hT hz,
    sub_sub_sub_cancel_right, Complex.sub_im, Complex.ofReal_im, sub_zero] at h
  rwa [div_le_div_iff₀ (mul_pos hy0 hz0) (mul_pos (hpos y hy) (hpos z hz))] at h

/-- The same for a driver that is only continuous on `[0, T]`, with solutions on `[0, T]`. -/
theorem norm_sub_sq_mul_le_of_continuousOn (hT : 0 ≤ T) (hW : ContinuousOn W (Icc 0 T))
    (hy : 0 < y.im) (hz : 0 < z.im) (hsy : ∃ u, IsForwardSol W y T u)
    (hsz : ∃ u, IsForwardSol W z T u) {s : ℝ} (hs : s ∈ Icc 0 T) :
    ‖y - z‖ ^ 2 * ((fwdMap W s y).im * (fwdMap W s z).im) ≤
      ‖fwdMap W s y - fwdMap W s z‖ ^ 2 * (y.im * z.im) := by
  have h := norm_sub_sq_mul_le (Ito.continuous_clampDrv hT hW) hT
    (Ito.mem_diff_fwdHull_clampDrv hT hW hy hsy) (Ito.mem_diff_fwdHull_clampDrv hT hW hz hsz) hs
  rwa [Ito.fwdMap_clampDrv_of_le hs.2, Ito.fwdMap_clampDrv_of_le hs.2] at h

/-- **Explicit separation.** If `δ ≤ Im f_s(y)` and `δ ≤ Im f_s(z)`, then
`‖y − z‖ δ / √(Im y Im z) ≤ ‖f_s(y) − f_s(z)‖`. -/
theorem le_norm_fwdMap_sub_of_continuousOn (hT : 0 ≤ T) (hW : ContinuousOn W (Icc 0 T))
    (hy : 0 < y.im) (hz : 0 < z.im) (hsy : ∃ u, IsForwardSol W y T u)
    (hsz : ∃ u, IsForwardSol W z T u) {s : ℝ} (hs : s ∈ Icc 0 T) {δ : ℝ} (hδ : 0 ≤ δ)
    (hδy : δ ≤ (fwdMap W s y).im) (hδz : δ ≤ (fwdMap W s z).im) :
    ‖y - z‖ * δ / Real.sqrt (y.im * z.im) ≤ ‖fwdMap W s y - fwdMap W s z‖ := by
  have h := norm_sub_sq_mul_le_of_continuousOn hT hW hy hz hsy hsz hs
  have hyz : 0 < y.im * z.im := mul_pos hy hz
  have hsq : 0 < Real.sqrt (y.im * z.im) := Real.sqrt_pos.2 hyz
  rw [div_le_iff₀ hsq]
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
  have hδ2 : δ ^ 2 ≤ (fwdMap W s y).im * (fwdMap W s z).im := by
    rw [sq]; exact mul_le_mul hδy hδz hδ (hδ.trans hδy)
  calc (‖y - z‖ * δ) ^ 2 = ‖y - z‖ ^ 2 * δ ^ 2 := by ring
    _ ≤ ‖y - z‖ ^ 2 * ((fwdMap W s y).im * (fwdMap W s z).im) :=
        mul_le_mul_of_nonneg_left hδ2 (sq_nonneg _)
    _ ≤ ‖fwdMap W s y - fwdMap W s z‖ ^ 2 * (y.im * z.im) := h
    _ = (‖fwdMap W s y - fwdMap W s z‖ * Real.sqrt (y.im * z.im)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hyz.le]

end Coupling

end InteractingSLE
