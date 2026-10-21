import SmallGammaGeodesics.Upper.TaylorBasic
import SmallGammaGeodesics.Upper.Defs

/-!
# Lemma T (5.6)–(5.7) (blueprint `lem:taylor`; BP2 detail D8; packet P-U2)

`taylor_probe`: for `|θ| ≤ c_T ℓ`, `p ∈ [1/2, 2]`, `Δ, M ≤ ℓ`, and a path `η` with
`|Re η(t) − t| ≤ Δ`, `|Im η(t)| ≤ M`,
`log ∫₀¹ exp(p log|ϕ'(η(t))|) dt ≤ −p (θ/ℓ) B_{j,a}(y_η) + C₁ θ²/ℓ
  + C₂ (|θ|MΔ/ℓ² + (|θ|M³ + θ²M² + |θ|³M + θ⁴)/ℓ³)`,
with `C_H = max(C, 1)` (`C` from P-B1's `norm_iteratedDeriv_probeH_le` at `K = 1`),
`c_T = 1/(8 C_H)`, `C₁ = (73/9)·48π C_H²` and `C₂ = 48π·20 C_H⁴`.

Proof (blueprint, Steps 1–4), organized as:
* `taylor_vertical`: the third-order expansion of `s ↦ H'(x + is)` (`norm_taylor3_le`);
* `taylor_log_point`: at one point `z = x + iy`, `w = ϕ'(z) − 1` has `|w| ≤ 1/4` and
  `log|ϕ'(z)| ≤ −θ y H''(x) + θ² H'(x)²/2 + C_A(|θ||y|³ + θ²y² + |θ|³|y| + θ⁴) ℓ⁻⁴ E(x)`
  (`log_norm_one_add_le`, `taylor_alg`);
* `taylor_pointwise`: for one time `t`, with `U = p log|ϕ'(η(t))|`, `|U| ≤ 1` and
  `U + U² ≤ −pθ y H''(t) + K E(t)`, where
  `K = 8C_H|θ|MΔℓ⁻³ + (584/9) C_H²θ²ℓ⁻² + 160 C_H⁴(|θ|M³ + θ²M² + |θ|³M + θ⁴)ℓ⁻⁴`
  (mean value theorem for `H''` on `[t, x]`, shift stability `E(x) ≤ 4E(t)`, `|log|1+w|| ≤ (4/3)|w|`);
* `taylor_probe`: `e^U ≤ 1 + U + U²`, `log J ≤ J − 1`, the band identity
  `ℓ ∫₀¹ y H'' = B_{j,a}(y)` (`bandProbe_eq_band`) and `∫₀¹ E ≤ 6πℓ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped Real

namespace SmallGammaGeodesics

/-- **Step 2, vertical Taylor expansion**: `H'(x + iy) = H'(x) + iyH''(x) − (y²/2)H⁽³⁾(x) + R`
with `|R| ≤ C_H ℓ⁻⁴ E(x) |y|³/6`, written with the real values `H^{(k)}(x)`. -/
theorem taylor_vertical {CH : ℝ}
    (hbd : ∀ (j : ℕ) (a : ℝ), ∀ k ≤ 4, ∀ z : ℂ, |z.im| ≤ ell j →
      ‖iteratedDeriv k (probeH j a) z‖ ≤ CH * (ell j)⁻¹ ^ k * envelope j a z.re)
    (j : ℕ) (a x y : ℝ) (hy : |y| ≤ ell j) :
    ‖iteratedDeriv 1 (probeH j a) ((x : ℂ) + (y : ℂ) * Complex.I) -
        (((iteratedDeriv 1 (probeH j a) x).re - y ^ 2 / 2 *
          (iteratedDeriv 3 (probeH j a) x).re : ℝ) : ℂ) -
        ((y * (iteratedDeriv 2 (probeH j a) x).re : ℝ) : ℂ) * Complex.I‖ ≤
      CH * (ell j)⁻¹ ^ 4 * envelope j a x * |y| ^ 3 / 6 := by
  set ι : ℝ → ℂ := fun s => (x : ℂ) + (s : ℂ) * Complex.I with hιdef
  have hι : ∀ s : ℝ, HasDerivAt ι Complex.I s := fun s =>
    (((hasDerivAt_id s).ofReal_comp.mul_const Complex.I).const_add (x : ℂ)).congr_deriv
      (by simp)
  have hgk : ∀ (k : ℕ) (s : ℝ), HasDerivAt (fun s : ℝ => iteratedDeriv k (probeH j a) (ι s))
      (iteratedDeriv (k + 1) (probeH j a) (ι s) * Complex.I) s := fun k s =>
    (hasDerivAt_iteratedDeriv_probeH j a k (ι s)).comp s (hι s)
  have hιre : ∀ s : ℝ, (ι s).re = x := fun s => by simp [hιdef]
  have hιim : ∀ s : ℝ, (ι s).im = s := fun s => by simp [hιdef]
  have hT := norm_taylor3_le (g := fun s => iteratedDeriv 1 (probeH j a) (ι s))
    (g₁ := fun s => iteratedDeriv 2 (probeH j a) (ι s) * Complex.I)
    (g₂ := fun s => iteratedDeriv 3 (probeH j a) (ι s) * Complex.I * Complex.I)
    (g₃ := fun s => iteratedDeriv 4 (probeH j a) (ι s) * Complex.I * Complex.I * Complex.I)
    (hgk 1) (fun s => (hgk 2 s).mul_const Complex.I)
    (fun s => ((hgk 3 s).mul_const Complex.I).mul_const Complex.I)
    (K := CH * (ell j)⁻¹ ^ 4 * envelope j a x) (y := y)
    (fun s hs => by
      have h := hbd j a 4 le_rfl (ι s) (by rw [hιim]; exact hs.trans hy)
      rw [hιre] at h
      calc ‖iteratedDeriv 4 (probeH j a) (ι s) * Complex.I * Complex.I * Complex.I‖
          = ‖iteratedDeriv 4 (probeH j a) (ι s)‖ := by
            simp only [norm_mul, Complex.norm_I, mul_one]
        _ ≤ CH * (ell j)⁻¹ ^ 4 * envelope j a x := h)
  have hι0 : ι 0 = (x : ℂ) := by simp [hιdef]
  simp only [hι0] at hT
  rw [← ofReal_re_iteratedDeriv_probeH j a 1 x, ← ofReal_re_iteratedDeriv_probeH j a 2 x,
    ← ofReal_re_iteratedDeriv_probeH j a 3 x] at hT
  have hR : ∀ (h₁ : ℂ) (A₁ A₂ A₃ : ℝ), h₁ - (A₁ : ℂ) - (y : ℂ) * ((A₂ : ℂ) * Complex.I) -
      ((y ^ 2 / 2 : ℝ) : ℂ) * ((A₃ : ℂ) * Complex.I * Complex.I) =
      h₁ - ((A₁ - y ^ 2 / 2 * A₃ : ℝ) : ℂ) - ((y * A₂ : ℝ) : ℂ) * Complex.I := by
    intro h₁ A₁ A₂ A₃
    rw [mul_assoc (A₃ : ℂ), Complex.I_mul_I]
    push_cast
    ring
  rw [hR] at hT
  exact hT

/-- **Steps 1–2 at one point** `z = x + iy`, `|y| ≤ ℓ`: with `w = ϕ'(z) − 1 = iθH'(z)`,
`|w| ≤ 1/4`, `|w|² ≤ θ²(C_H ℓ⁻¹ E(x))²` and
`log|ϕ'(z)| ≤ −θ y H''(x) + θ² H'(x)²/2 + C_A (|θ||y|³ + θ²y² + |θ|³|y| + θ⁴) ℓ⁻⁴ E(x)`. -/
theorem taylor_log_point {CH : ℝ} (hCH : 1 ≤ CH)
    (hbd : ∀ (j : ℕ) (a : ℝ), ∀ k ≤ 4, ∀ z : ℂ, |z.im| ≤ ell j →
      ‖iteratedDeriv k (probeH j a) z‖ ≤ CH * (ell j)⁻¹ ^ k * envelope j a z.re)
    {j : ℕ} {a θ : ℝ} {z : ℂ} (hθ : |θ| ≤ 1 / (8 * CH) * ell j) (hz : |z.im| ≤ ell j) :
    ‖deriv (probeMap j a θ) z - 1‖ ≤ 1 / 4 ∧
    ‖deriv (probeMap j a θ) z - 1‖ ^ 2 ≤ θ ^ 2 * (CH * (ell j)⁻¹ * envelope j a z.re) ^ 2 ∧
    Real.log ‖deriv (probeMap j a θ) z‖ ≤
      -θ * z.im * (iteratedDeriv 2 (probeH j a) ((z.re : ℝ) : ℂ)).re +
        θ ^ 2 * (iteratedDeriv 1 (probeH j a) ((z.re : ℝ) : ℂ)).re ^ 2 / 2 +
        20 * CH ^ 4 * (|θ| * |z.im| ^ 3 + θ ^ 2 * z.im ^ 2 + |θ| ^ 3 * |z.im| + θ ^ 4) *
          (ell j)⁻¹ ^ 4 * envelope j a z.re := by
  have hℓ : 0 < ell j := ell_pos j
  have hm : 0 < (ell j)⁻¹ := inv_pos.2 hℓ
  have hmℓ : (ell j)⁻¹ * ell j = 1 := inv_mul_cancel₀ hℓ.ne'
  have he0 : 0 ≤ envelope j a z.re := envelope_nonneg j a z.re
  have he2 : envelope j a z.re ≤ 2 := envelope_le_two j a z.re
  have hCH0 : 0 ≤ CH := by linarith
  have hym : |z.im| * (ell j)⁻¹ ≤ 1 := by
    calc |z.im| * (ell j)⁻¹ ≤ ell j * (ell j)⁻¹ := mul_le_mul_of_nonneg_right hz hm.le
      _ = 1 := by rw [mul_comm]; exact hmℓ
  have hθm : |θ| * (ell j)⁻¹ ≤ 1 / (8 * CH) := by
    calc |θ| * (ell j)⁻¹ ≤ 1 / (8 * CH) * ell j * (ell j)⁻¹ :=
          mul_le_mul_of_nonneg_right hθ hm.le
      _ = 1 / (8 * CH) := by rw [mul_assoc, mul_comm (ell j), hmℓ, mul_one]
  have hA : ∀ k ≤ 4, |(iteratedDeriv k (probeH j a) ((z.re : ℝ) : ℂ)).re| ≤
      CH * (ell j)⁻¹ ^ k * envelope j a z.re := by
    intro k hk
    have h := hbd j a k hk ((z.re : ℝ) : ℂ) (by rw [Complex.ofReal_im, abs_zero]; exact hℓ.le)
    rw [Complex.ofReal_re] at h
    exact (Complex.abs_re_le_norm _).trans h
  have hA₁ := hA 1 (by norm_num)
  rw [pow_one] at hA₁
  -- the vertical expansion
  have hT := taylor_vertical hbd j a z.re z.im hz
  rw [Complex.re_add_im z] at hT
  have hu : |(iteratedDeriv 1 (probeH j a) z).re -
      (iteratedDeriv 1 (probeH j a) ((z.re : ℝ) : ℂ)).re +
      z.im ^ 2 / 2 * (iteratedDeriv 3 (probeH j a) ((z.re : ℝ) : ℂ)).re| ≤
      CH * (ell j)⁻¹ ^ 4 * envelope j a z.re * |z.im| ^ 3 / 6 := by
    refine le_trans (le_of_eq ?_) ((Complex.abs_re_le_norm _).trans hT)
    congr 1
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hv : |(iteratedDeriv 1 (probeH j a) z).im -
      z.im * (iteratedDeriv 2 (probeH j a) ((z.re : ℝ) : ℂ)).re| ≤
      CH * (ell j)⁻¹ ^ 4 * envelope j a z.re * |z.im| ^ 3 / 6 := by
    refine le_trans (le_of_eq ?_) ((Complex.abs_im_le_norm _).trans hT)
    congr 1
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im]
    ring
  have hh₁ : ‖iteratedDeriv 1 (probeH j a) z‖ ≤ CH * (ell j)⁻¹ * envelope j a z.re := by
    have h := hbd j a 1 (by norm_num) z hz
    rw [pow_one] at h
    exact h
  have hh : (iteratedDeriv 1 (probeH j a) z).re ^ 2 + (iteratedDeriv 1 (probeH j a) z).im ^ 2 ≤
      (CH * (ell j)⁻¹ * envelope j a z.re) ^ 2 := by
    have h1 : (iteratedDeriv 1 (probeH j a) z).re ^ 2 + (iteratedDeriv 1 (probeH j a) z).im ^ 2 =
        ‖iteratedDeriv 1 (probeH j a) z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [h1]
    exact pow_le_pow_left₀ (norm_nonneg _) hh₁ 2
  -- the logarithm
  have hderiv : deriv (probeMap j a θ) z =
      1 + Complex.I * θ * iteratedDeriv 1 (probeH j a) z := by
    rw [(hasDerivAt_probeMap j a θ z).deriv, iteratedDeriv_one]
  set h₁ := iteratedDeriv 1 (probeH j a) z with hh₁def
  set w : ℂ := Complex.I * θ * h₁ with hwdef
  have hwre : w.re = -θ * h₁.im := by simp [hwdef, Complex.mul_re, Complex.mul_im]
  have hwim : w.im = θ * h₁.re := by simp [hwdef, Complex.mul_re, Complex.mul_im]
  have hwn : ‖w‖ = |θ| * ‖h₁‖ := by
    rw [hwdef, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hwsq : ‖w‖ ^ 2 = θ ^ 2 * (h₁.re ^ 2 + h₁.im ^ 2) := by
    rw [hwn, mul_pow, sq_abs, Complex.sq_norm, Complex.normSq_apply]; ring
  have hw2 : ‖w‖ ^ 2 ≤ θ ^ 2 * (CH * (ell j)⁻¹ * envelope j a z.re) ^ 2 := by
    rw [hwsq]; exact mul_le_mul_of_nonneg_left hh (sq_nonneg θ)
  have hw14 : ‖w‖ ≤ 1 / 4 := by
    have h1 : ‖w‖ ≤ |θ| * (CH * (ell j)⁻¹ * envelope j a z.re) := by
      rw [hwn]; exact mul_le_mul_of_nonneg_left hh₁ (abs_nonneg θ)
    have h3 : |θ| * (CH * (ell j)⁻¹ * envelope j a z.re) =
        (|θ| * (ell j)⁻¹) * (CH * envelope j a z.re) := by ring
    have h4 : (|θ| * (ell j)⁻¹) * (CH * envelope j a z.re) ≤ 1 / (8 * CH) * (CH * 2) :=
      mul_le_mul hθm (mul_le_mul_of_nonneg_left he2 hCH0) (by positivity) (by positivity)
    have h5 : 1 / (8 * CH) * (CH * 2) = 1 / 4 := by field_simp; ring
    linarith
  have hsub : deriv (probeMap j a θ) z - 1 = w := by rw [hderiv]; ring
  refine ⟨by rw [hsub]; exact hw14, by rw [hsub]; exact hw2, ?_⟩
  rw [hderiv]
  have h1 := log_norm_one_add_le hw14
  rw [hwre, hwim, show ‖w‖ ^ 4 = (‖w‖ ^ 2) ^ 2 by ring, hwsq] at h1
  exact h1.trans (taylor_alg hm he0 he2 hCH hym hA₁ (hA 2 (by norm_num)) (hA 3 (by norm_num))
    hu hv hh)

/-- **Lemma T, pointwise algebra**: the four contributions at one time. -/
theorem taylor_combine {p θ y M Δ m e Et A₁ A₂ A₂t L wn CH Err ErrM : ℝ}
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2) (he0 : 0 ≤ e) (he2 : e ≤ 2) (he4 : e ≤ 4 * Et) (him : |y| ≤ M)
    (hErr0 : 0 ≤ Err) (hErr : Err ≤ ErrM)
    (hL : L ≤ -θ * y * A₂ + θ ^ 2 * A₁ ^ 2 / 2 + 20 * CH ^ 4 * Err * m ^ 4 * e)
    (hL1 : |L| ≤ 4 / 3 * wn) (hw2 : wn ^ 2 ≤ θ ^ 2 * (CH * m * e) ^ 2)
    (hA₂t : |A₂ - A₂t| ≤ 4 * CH * m ^ 3 * Et * Δ) (hA₁ : |A₁| ≤ CH * m * e) :
    p * L + (p * L) ^ 2 ≤ -p * θ * y * A₂t +
      (8 * CH * (|θ| * M * Δ) * m ^ 3 + 584 / 9 * CH ^ 2 * θ ^ 2 * m ^ 2 +
        160 * CH ^ 4 * ErrM * m ^ 4) * Et := by
  have hee : e * e ≤ 8 * Et := by
    calc e * e ≤ 2 * (4 * Et) := mul_le_mul he2 he4 he0 (by norm_num)
      _ = 8 * Et := by ring
  have hM0 : 0 ≤ M := (abs_nonneg y).trans him
  -- (a) the main term
  have Ha : p * (-θ * y * A₂) ≤ -p * θ * y * A₂t + 8 * CH * (|θ| * M * Δ) * m ^ 3 * Et := by
    have h1 : p * (-θ * y * A₂) = -p * θ * y * A₂t + (-(p * θ * y)) * (A₂ - A₂t) := by ring
    have h2 : (-(p * θ * y)) * (A₂ - A₂t) ≤ 8 * CH * (|θ| * M * Δ) * m ^ 3 * Et := by
      calc (-(p * θ * y)) * (A₂ - A₂t) ≤ |(-(p * θ * y)) * (A₂ - A₂t)| := le_abs_self _
        _ = p * (|θ| * |y|) * |A₂ - A₂t| := by
            rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_of_nonneg hp0, mul_assoc p]
        _ ≤ 2 * (|θ| * M) * (4 * CH * m ^ 3 * Et * Δ) := by
            gcongr
        _ = 8 * CH * (|θ| * M * Δ) * m ^ 3 * Et := by ring
    linarith only [h1, h2]
  -- (b) the quadratic term
  have Hb : p * (θ ^ 2 * A₁ ^ 2 / 2) ≤ 8 * CH ^ 2 * θ ^ 2 * m ^ 2 * Et := by
    have h1 : A₁ ^ 2 ≤ (CH * m * e) ^ 2 := by
      rw [← sq_abs A₁]
      exact pow_le_pow_left₀ (abs_nonneg _) hA₁ 2
    have h2 : (CH * m * e) ^ 2 ≤ 8 * (CH ^ 2 * m ^ 2) * Et := by
      calc (CH * m * e) ^ 2 = (CH ^ 2 * m ^ 2) * (e * e) := by ring
        _ ≤ (CH ^ 2 * m ^ 2) * (8 * Et) := mul_le_mul_of_nonneg_left hee (by positivity)
        _ = 8 * (CH ^ 2 * m ^ 2) * Et := by ring
    calc p * (θ ^ 2 * A₁ ^ 2 / 2) ≤ 2 * (θ ^ 2 * A₁ ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right hp2 (by positivity)
      _ = θ ^ 2 * A₁ ^ 2 := by ring
      _ ≤ θ ^ 2 * (8 * (CH ^ 2 * m ^ 2) * Et) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (sq_nonneg θ)
      _ = 8 * CH ^ 2 * θ ^ 2 * m ^ 2 * Et := by ring
  -- (c) the error term
  have hErrM0 : 0 ≤ ErrM := hErr0.trans hErr
  have Hc : p * (20 * CH ^ 4 * Err * m ^ 4 * e) ≤ 160 * CH ^ 4 * ErrM * m ^ 4 * Et := by
    have h0 : 0 ≤ 20 * CH ^ 4 := by positivity
    have h1 : 20 * CH ^ 4 * Err * m ^ 4 ≤ 20 * CH ^ 4 * ErrM * m ^ 4 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hErr h0) (by positivity)
    have h2 : 20 * CH ^ 4 * Err * m ^ 4 * e ≤ 20 * CH ^ 4 * ErrM * m ^ 4 * (4 * Et) :=
      mul_le_mul h1 he4 he0 (mul_nonneg (mul_nonneg h0 hErrM0) (by positivity))
    have h3 : 0 ≤ 20 * CH ^ 4 * Err * m ^ 4 * e :=
      mul_nonneg (mul_nonneg (mul_nonneg h0 hErr0) (by positivity)) he0
    calc p * (20 * CH ^ 4 * Err * m ^ 4 * e) ≤ 2 * (20 * CH ^ 4 * ErrM * m ^ 4 * (4 * Et)) :=
          mul_le_mul hp2 h2 h3 (by norm_num)
      _ = 160 * CH ^ 4 * ErrM * m ^ 4 * Et := by ring
  -- (d) the square
  have Hd : (p * L) ^ 2 ≤ 512 / 9 * CH ^ 2 * θ ^ 2 * m ^ 2 * Et := by
    have hp4 : p ^ 2 ≤ 4 := by
      calc p ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ hp0 hp2 2
        _ = 4 := by norm_num
    have hL2 : L ^ 2 ≤ 16 / 9 * wn ^ 2 := by
      rw [← sq_abs L]
      calc |L| ^ 2 ≤ (4 / 3 * wn) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hL1 2
        _ = 16 / 9 * wn ^ 2 := by ring
    have h2 : wn ^ 2 ≤ θ ^ 2 * (8 * (CH ^ 2 * m ^ 2) * Et) := by
      refine hw2.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg θ))
      calc (CH * m * e) ^ 2 = (CH ^ 2 * m ^ 2) * (e * e) := by ring
        _ ≤ (CH ^ 2 * m ^ 2) * (8 * Et) := mul_le_mul_of_nonneg_left hee (by positivity)
        _ = 8 * (CH ^ 2 * m ^ 2) * Et := by ring
    calc (p * L) ^ 2 = p ^ 2 * L ^ 2 := by ring
      _ ≤ 4 * (16 / 9 * wn ^ 2) := mul_le_mul hp4 hL2 (sq_nonneg _) (by norm_num)
      _ ≤ 4 * (16 / 9 * (θ ^ 2 * (8 * (CH ^ 2 * m ^ 2) * Et))) := by gcongr
      _ = 512 / 9 * CH ^ 2 * θ ^ 2 * m ^ 2 * Et := by ring
  have hpL : p * L ≤ p * (-θ * y * A₂) + p * (θ ^ 2 * A₁ ^ 2 / 2) +
      p * (20 * CH ^ 4 * Err * m ^ 4 * e) := by
    have h := mul_le_mul_of_nonneg_left hL hp0
    have e1 : p * (-θ * y * A₂ + θ ^ 2 * A₁ ^ 2 / 2 + 20 * CH ^ 4 * Err * m ^ 4 * e) =
        p * (-θ * y * A₂) + p * (θ ^ 2 * A₁ ^ 2 / 2) + p * (20 * CH ^ 4 * Err * m ^ 4 * e) := by
      ring
    rw [e1] at h
    exact h
  have hfin : (8 * CH * (|θ| * M * Δ) * m ^ 3 + 584 / 9 * CH ^ 2 * θ ^ 2 * m ^ 2 +
      160 * CH ^ 4 * ErrM * m ^ 4) * Et =
      8 * CH * (|θ| * M * Δ) * m ^ 3 * Et + 8 * CH ^ 2 * θ ^ 2 * m ^ 2 * Et +
        160 * CH ^ 4 * ErrM * m ^ 4 * Et + 512 / 9 * CH ^ 2 * θ ^ 2 * m ^ 2 * Et := by ring
  rw [hfin]
  linarith only [hpL, Ha, Hb, Hc, Hd]

/-- **Lemma T, pointwise part** (Steps 1–2 at one time `t`, with the shift from `x = Re η(t)` to
`t`): `|U| ≤ 1` and `U + U² ≤ −pθ y H''(t) + K E(t)`. -/
theorem taylor_pointwise {CH : ℝ} (hCH : 1 ≤ CH)
    (hbd : ∀ (j : ℕ) (a : ℝ), ∀ k ≤ 4, ∀ z : ℂ, |z.im| ≤ ell j →
      ‖iteratedDeriv k (probeH j a) z‖ ≤ CH * (ell j)⁻¹ ^ k * envelope j a z.re)
    {j : ℕ} {a p θ Δ M t : ℝ} {z : ℂ} (hp1 : 1 / 2 ≤ p) (hp2 : p ≤ 2)
    (hθ : |θ| ≤ 1 / (8 * CH) * ell j) (hΔ : Δ ≤ ell j) (hM : M ≤ ell j)
    (hre : |z.re - t| ≤ Δ) (him : |z.im| ≤ M) :
    |p * Real.log ‖deriv (probeMap j a θ) z‖| ≤ 1 ∧
    p * Real.log ‖deriv (probeMap j a θ) z‖ + (p * Real.log ‖deriv (probeMap j a θ) z‖) ^ 2 ≤
      -p * θ * z.im * (iteratedDeriv 2 (probeH j a) t).re +
        (8 * CH * (|θ| * M * Δ) * (ell j)⁻¹ ^ 3 + 584 / 9 * CH ^ 2 * θ ^ 2 * (ell j)⁻¹ ^ 2 +
          160 * CH ^ 4 * (|θ| * M ^ 3 + θ ^ 2 * M ^ 2 + |θ| ^ 3 * M + θ ^ 4) * (ell j)⁻¹ ^ 4) *
          envelope j a t := by
  have hℓ : 0 < ell j := ell_pos j
  have hm : 0 < (ell j)⁻¹ := inv_pos.2 hℓ
  have hp0 : 0 ≤ p := by linarith
  have hCH0 : 0 ≤ CH := by linarith
  have hyℓ : |z.im| ≤ ell j := him.trans hM
  have hxt : |z.re - t| ≤ ell j := hre.trans hΔ
  have hEt0 : 0 ≤ envelope j a t := envelope_nonneg j a t
  obtain ⟨hw14, hw2, hL⟩ := taylor_log_point hCH hbd hθ hyℓ
  have hL1 : |Real.log ‖deriv (probeMap j a θ) z‖| ≤ 4 / 3 * ‖deriv (probeMap j a θ) z - 1‖ := by
    have h := abs_log_norm_one_add_le hw14
    have e : (1 : ℂ) + (deriv (probeMap j a θ) z - 1) = deriv (probeMap j a θ) z := by ring
    rwa [e] at h
  -- `|U| ≤ 1`
  have hU1 : |p * Real.log ‖deriv (probeMap j a θ) z‖| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hp0]
    have h1 : |Real.log ‖deriv (probeMap j a θ) z‖| ≤ 1 / 3 := by linarith
    calc p * |Real.log ‖deriv (probeMap j a θ) z‖| ≤ 2 * (1 / 3) :=
          mul_le_mul hp2 h1 (abs_nonneg _) (by norm_num)
      _ ≤ 1 := by norm_num
  refine ⟨hU1, ?_⟩
  -- the mean value theorem for `H''` on `[t, x]`
  have hA₂t : |(iteratedDeriv 2 (probeH j a) ((z.re : ℝ) : ℂ)).re -
      (iteratedDeriv 2 (probeH j a) t).re| ≤
      4 * CH * (ell j)⁻¹ ^ 3 * envelope j a t * Δ := by
    have hF : ∀ r ∈ uIcc t z.re, HasDerivWithinAt
        (fun r : ℝ => iteratedDeriv 2 (probeH j a) r)
        (iteratedDeriv 3 (probeH j a) r) (uIcc t z.re) r := fun r _ =>
      ((hasDerivAt_iteratedDeriv_probeH j a 2 r).comp_ofReal).hasDerivWithinAt
    have hb : ∀ r ∈ uIcc t z.re, ‖iteratedDeriv 3 (probeH j a) r‖ ≤
        4 * CH * (ell j)⁻¹ ^ 3 * envelope j a t := by
      intro r hr
      have h1 := hbd j a 3 (by norm_num) (r : ℂ)
        (by rw [Complex.ofReal_im, abs_zero]; exact hℓ.le)
      rw [Complex.ofReal_re] at h1
      have h2 : |r - t| ≤ ell j := (abs_sub_left_of_mem_uIcc hr).trans hxt
      have h3 := envelope_le_four_mul j a h2
      calc ‖iteratedDeriv 3 (probeH j a) r‖ ≤ CH * (ell j)⁻¹ ^ 3 * envelope j a r := h1
        _ ≤ CH * (ell j)⁻¹ ^ 3 * (4 * envelope j a t) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = 4 * CH * (ell j)⁻¹ ^ 3 * envelope j a t := by ring
    have hmvt := (convex_uIcc t z.re).norm_image_sub_le_of_norm_hasDerivWithin_le hF hb
      left_mem_uIcc right_mem_uIcc
    rw [Real.norm_eq_abs] at hmvt
    calc |(iteratedDeriv 2 (probeH j a) ((z.re : ℝ) : ℂ)).re -
          (iteratedDeriv 2 (probeH j a) t).re|
        = |(iteratedDeriv 2 (probeH j a) ((z.re : ℝ) : ℂ) -
            iteratedDeriv 2 (probeH j a) t).re| := by
          rw [Complex.sub_re]
      _ ≤ ‖iteratedDeriv 2 (probeH j a) ((z.re : ℝ) : ℂ) - iteratedDeriv 2 (probeH j a) t‖ :=
          Complex.abs_re_le_norm _
      _ ≤ 4 * CH * (ell j)⁻¹ ^ 3 * envelope j a t * |z.re - t| := hmvt
      _ ≤ 4 * CH * (ell j)⁻¹ ^ 3 * envelope j a t * Δ :=
          mul_le_mul_of_nonneg_left hre (by positivity)
  have hA₁ : |(iteratedDeriv 1 (probeH j a) ((z.re : ℝ) : ℂ)).re| ≤
      CH * (ell j)⁻¹ * envelope j a z.re := by
    have h := hbd j a 1 (by norm_num) ((z.re : ℝ) : ℂ)
      (by rw [Complex.ofReal_im, abs_zero]; exact hℓ.le)
    rw [Complex.ofReal_re, pow_one] at h
    exact (Complex.abs_re_le_norm _).trans h
  have hErr : |θ| * |z.im| ^ 3 + θ ^ 2 * z.im ^ 2 + |θ| ^ 3 * |z.im| + θ ^ 4 ≤
      |θ| * M ^ 3 + θ ^ 2 * M ^ 2 + |θ| ^ 3 * M + θ ^ 4 := by
    have h1 : |z.im| ^ 3 ≤ M ^ 3 := pow_le_pow_left₀ (abs_nonneg _) him 3
    have h2 : z.im ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs z.im]; exact pow_le_pow_left₀ (abs_nonneg _) him 2
    have h1' := mul_le_mul_of_nonneg_left h1 (abs_nonneg θ)
    have h2' := mul_le_mul_of_nonneg_left h2 (sq_nonneg θ)
    have h3' := mul_le_mul_of_nonneg_left him (pow_nonneg (abs_nonneg θ) 3)
    linarith only [h1', h2', h3']
  have hErr0 : 0 ≤ |θ| * |z.im| ^ 3 + θ ^ 2 * z.im ^ 2 + |θ| ^ 3 * |z.im| + θ ^ 4 := by positivity
  exact taylor_combine hp0 hp2 (envelope_nonneg j a z.re) (envelope_le_two j a z.re)
    (envelope_le_four_mul j a hxt) him hErr0 hErr hL hL1 hw2 hA₂t hA₁

private theorem continuous_deriv_probeMap_aux (j : ℕ) (a θ : ℝ) :
    Continuous (deriv (probeMap j a θ)) := by
  have h : deriv (probeMap j a θ) = fun z => 1 + Complex.I * θ * iteratedDeriv 1 (probeH j a) z := by
    funext z
    rw [(hasDerivAt_probeMap j a θ z).deriv, iteratedDeriv_one]
  rw [h]
  exact continuous_const.add (continuous_const.mul (continuous_iteratedDeriv_probeH j a 1))

/-- **Lemma T** ((5.6)–(5.7); blueprint `lem:taylor`, BP2 D8). -/
theorem taylor_probe : ∃ C₁ C₂ cT, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 < cT ∧ cT ≤ 1 ∧ ∀ (j : ℕ) (a : ℝ),
    a ∈ Icc (0:ℝ) 1 →
    ∀ (p θ Δ M : ℝ) (η : C(unitInterval, ℂ)), 1/2 ≤ p → p ≤ 2 → |θ| ≤ cT * ell j → 0 ≤ Δ →
    Δ ≤ ell j → 0 ≤ M → M ≤ ell j → (∀ t : unitInterval, |(η t).re - t| ≤ Δ) →
    (∀ t : unitInterval, |(η t).im| ≤ M) →
    Real.log (∫ t in (0:ℝ)..1, Real.exp (p * Real.log ‖deriv (probeMap j a θ)
        (η (Set.projIcc 0 1 zero_le_one t))‖)) ≤
      -p * (θ / ell j) * band (yPath η) j a + C₁ * θ ^ 2 / ell j +
      C₂ * (|θ| * M * Δ / ell j ^ 2 + (|θ| * M ^ 3 + θ ^ 2 * M ^ 2 + |θ| ^ 3 * M + θ ^ 4) /
        ell j ^ 3) := by
  obtain ⟨C, _, hC⟩ := norm_iteratedDeriv_probeH_le 1 one_pos
  set CH := max C 1 with hCHdef
  have hCH : 1 ≤ CH := le_max_right _ _
  have hCH0 : 0 ≤ CH := by linarith
  have hbd : ∀ (j : ℕ) (a : ℝ), ∀ k ≤ 4, ∀ z : ℂ, |z.im| ≤ ell j →
      ‖iteratedDeriv k (probeH j a) z‖ ≤ CH * (ell j)⁻¹ ^ k * envelope j a z.re := by
    intro j a k hk z hz
    have h := hC j a k hk z (by rw [one_mul]; exact hz)
    refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (pow_nonneg (inv_nonneg.2 (ell_pos j).le) k)) (envelope_nonneg j a z.re))
  refine ⟨73 / 9 * (48 * π) * CH ^ 2, 48 * π * (20 * CH ^ 4), 1 / (8 * CH), by positivity,
    by positivity, by positivity, ?_, ?_⟩
  · rw [div_le_one (by positivity)]; linarith
  intro j a ha p θ Δ M η hp1 hp2 hθ hΔ0 hΔ hM0 hM hre him
  have hℓ := ell_pos j
  set m := (ell j)⁻¹ with hmdef
  have hm : 0 < m := inv_pos.2 hℓ
  have hmℓ : m * ell j = 1 := inv_mul_cancel₀ hℓ.ne'
  set ErrM := |θ| * M ^ 3 + θ ^ 2 * M ^ 2 + |θ| ^ 3 * M + θ ^ 4 with hErrMdef
  have hErrM0 : 0 ≤ ErrM := by positivity
  set K := 8 * CH * (|θ| * M * Δ) * m ^ 3 + 584 / 9 * CH ^ 2 * θ ^ 2 * m ^ 2 +
    160 * CH ^ 4 * ErrM * m ^ 4 with hKdef
  have hK0 : 0 ≤ K := by positivity
  set U : ℝ → ℝ := fun t =>
    p * Real.log ‖deriv (probeMap j a θ) (η (Set.projIcc 0 1 zero_le_one t))‖ with hUdef
  -- the pointwise bound on `[0,1]`
  have hpt : ∀ t ∈ Icc (0:ℝ) 1, |U t| ≤ 1 ∧ U t + U t ^ 2 ≤
      -p * θ * (yPath η t * (iteratedDeriv 2 (probeH j a) t).re) + K * envelope j a t := by
    intro t ht
    have hτ : ((Set.projIcc 0 1 zero_le_one t : unitInterval) : ℝ) = t := by
      rw [Set.projIcc_of_mem _ ht]
    have h1 := hre (Set.projIcc 0 1 zero_le_one t)
    rw [hτ] at h1
    obtain ⟨hA, hB⟩ := taylor_pointwise hCH hbd hp1 hp2 hθ hΔ hM h1 (him _)
    refine ⟨hA, hB.trans (le_of_eq ?_)⟩
    simp only [yPath, hKdef, hErrMdef, hmdef]
    ring
  -- continuity
  have hpath : Continuous fun t : ℝ => η (Set.projIcc 0 1 zero_le_one t) :=
    η.continuous.comp continuous_projIcc
  have hderc : Continuous fun t : ℝ =>
      deriv (probeMap j a θ) (η (Set.projIcc 0 1 zero_le_one t)) :=
    (continuous_deriv_probeMap_aux j a θ).comp hpath
  have hne : ∀ t : ℝ, ‖deriv (probeMap j a θ) (η (Set.projIcc 0 1 zero_le_one t))‖ ≠ 0 := by
    intro t
    have h := (taylor_log_point (a := a) (z := η (Set.projIcc 0 1 zero_le_one t)) hCH hbd hθ
      ((him _).trans hM)).1
    have h2 : ‖(1 : ℂ)‖ ≤ ‖deriv (probeMap j a θ) (η (Set.projIcc 0 1 zero_le_one t))‖ +
        ‖deriv (probeMap j a θ) (η (Set.projIcc 0 1 zero_le_one t)) - 1‖ := by
      have := norm_sub_le (deriv (probeMap j a θ) (η (Set.projIcc 0 1 zero_le_one t)))
        (deriv (probeMap j a θ) (η (Set.projIcc 0 1 zero_le_one t)) - 1)
      rwa [sub_sub_cancel] at this
    rw [norm_one] at h2
    have : (0 : ℝ) < ‖deriv (probeMap j a θ) (η (Set.projIcc 0 1 zero_le_one t))‖ := by linarith
    exact this.ne'
  have hUc : Continuous U := continuous_const.mul (hderc.norm.log hne)
  have hEc : Continuous (envelope j a) := continuous_envelope j a
  have hyc : Continuous (yPath η) := Complex.continuous_im.comp hpath
  have hA2c : Continuous fun t : ℝ => (iteratedDeriv 2 (probeH j a) t).re :=
    Complex.continuous_re.comp ((continuous_iteratedDeriv_probeH j a 2).comp
      Complex.continuous_ofReal)
  have hUU : Continuous fun t => U t + U t ^ 2 := hUc.add (hUc.pow 2)
  -- `J ≤ 1 + ∫ (U + U²)`
  set J := ∫ t in (0:ℝ)..1, Real.exp (U t) with hJdef
  have hJ0 : 0 < J := intervalIntegral.intervalIntegral_pos_of_pos_on
    ((Real.continuous_exp.comp hUc).intervalIntegrable 0 1) (fun t _ => Real.exp_pos _)
    zero_lt_one
  have hJ1 : J ≤ 1 + ∫ t in (0:ℝ)..1, (U t + U t ^ 2) := by
    have h1 : ∫ t in (0:ℝ)..1, Real.exp (U t) ≤ ∫ t in (0:ℝ)..1, (1 + (U t + U t ^ 2)) :=
      intervalIntegral.integral_mono_on zero_le_one
        ((Real.continuous_exp.comp hUc).intervalIntegrable 0 1)
        ((continuous_const.add hUU).intervalIntegrable 0 1) fun t ht => by
          have h := Real.abs_exp_sub_one_sub_id_le (hpt t ht).1
          have := (abs_le.1 h).2
          linarith
    rw [intervalIntegral.integral_add intervalIntegrable_const (hUU.intervalIntegrable 0 1),
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] at h1
    exact h1
  -- `∫ (U + U²) ≤ −pθ ∫ y H'' + K ∫ E`
  have hint : ∫ t in (0:ℝ)..1, (U t + U t ^ 2) ≤
      -p * θ * (∫ t in (0:ℝ)..1, yPath η t * (iteratedDeriv 2 (probeH j a) t).re) +
        K * ∫ t in (0:ℝ)..1, envelope j a t := by
    have h1 : ∫ t in (0:ℝ)..1, (U t + U t ^ 2) ≤ ∫ t in (0:ℝ)..1,
        (-p * θ * (yPath η t * (iteratedDeriv 2 (probeH j a) t).re) + K * envelope j a t) :=
      intervalIntegral.integral_mono_on zero_le_one (hUU.intervalIntegrable 0 1)
        (((continuous_const.mul (hyc.mul hA2c)).add (continuous_const.mul hEc)).intervalIntegrable
          0 1) fun t ht => (hpt t ht).2
    have hi1 : IntervalIntegrable
        (fun t => -p * θ * (yPath η t * (iteratedDeriv 2 (probeH j a) t).re)) volume 0 1 :=
      (continuous_const.mul (hyc.mul hA2c)).intervalIntegrable 0 1
    have hi2 : IntervalIntegrable (fun t => K * envelope j a t) volume 0 1 :=
      (continuous_const.mul hEc).intervalIntegrable 0 1
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at h1
    exact h1
  -- the band identity (4.4)
  have hband : ell j * ∫ t in (0:ℝ)..1, yPath η t * (iteratedDeriv 2 (probeH j a) t).re =
      band (yPath η) j a := by
    rw [← bandProbe_eq_band (yPath η) hyc.continuousOn j a]
    unfold bandProbe
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [iteratedDeriv_two_re_probeH]
  have hIb : ∫ t in (0:ℝ)..1, yPath η t * (iteratedDeriv 2 (probeH j a) t).re =
      band (yPath η) j a * m := by
    rw [← hband, mul_comm (ell j), mul_assoc, mul_comm (ell j) m, hmℓ, mul_one]
  have hEint : ∫ t in (0:ℝ)..1, envelope j a t ≤ 6 * π * ell j := integral_envelope_le j ha
  -- `log J ≤ J − 1`
  have hlogJ : Real.log J ≤ J - 1 := Real.log_le_sub_one_of_pos hJ0
  have hKE : K * ∫ t in (0:ℝ)..1, envelope j a t ≤ K * (6 * π * ell j) :=
    mul_le_mul_of_nonneg_left hEint hK0
  have hK6 : K * (6 * π * ell j) = 48 * π * CH * (|θ| * M * Δ) * m ^ 2 +
      73 / 9 * (48 * π) * CH ^ 2 * θ ^ 2 * m + 48 * π * (20 * CH ^ 4) * ErrM * m ^ 3 := by
    have e1 : K * (6 * π * ell j) = 6 * π * (8 * CH * (|θ| * M * Δ) * m ^ 2 +
        584 / 9 * CH ^ 2 * θ ^ 2 * m + 160 * CH ^ 4 * ErrM * m ^ 3) * (m * ell j) := by
      rw [hKdef]; ring
    rw [e1, hmℓ]
    ring
  have hRHS : -p * (θ / ell j) * band (yPath η) j a + 73 / 9 * (48 * π) * CH ^ 2 * θ ^ 2 / ell j +
      48 * π * (20 * CH ^ 4) * (|θ| * M * Δ / ell j ^ 2 + ErrM / ell j ^ 3) =
      -p * θ * (band (yPath η) j a * m) + 73 / 9 * (48 * π) * CH ^ 2 * θ ^ 2 * m +
        48 * π * (20 * CH ^ 4) * (|θ| * M * Δ) * m ^ 2 +
        48 * π * (20 * CH ^ 4) * ErrM * m ^ 3 := by
    simp only [hmdef, div_eq_mul_inv, inv_pow]
    ring
  rw [hRHS]
  have hCH4 : 48 * π * CH * (|θ| * M * Δ) * m ^ 2 ≤
      48 * π * (20 * CH ^ 4) * (|θ| * M * Δ) * m ^ 2 := by
    have h1 : CH ≤ 20 * CH ^ 4 := by
      have := le_self_pow₀ hCH (show 4 ≠ 0 by norm_num)
      linarith
    have h2 : 0 ≤ 48 * π * (|θ| * M * Δ) * m ^ 2 := by positivity
    nlinarith
  rw [hIb] at hint
  linarith

end SmallGammaGeodesics
