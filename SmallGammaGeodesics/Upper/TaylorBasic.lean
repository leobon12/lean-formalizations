import SmallGammaGeodesics.Probes.Bounds
import SmallGammaGeodesics.Probes.Bands
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Ingredients of Lemma T (blueprint `lem:taylor`; BP2 detail D8; packet P-U2)

* `hasDerivAt_iteratedDeriv_probeH`: `(H^{(d)})' = H^{(d+1)}` everywhere;
  `im_iteratedDeriv_probeH_ofReal`: every `H^{(d)}` is real on `ℝ` (input (I5));
  `iteratedDeriv_two_re_probeH`: the real second derivative of `x ↦ Re H(x)` is `Re H''(x)`, the
  kernel of the band identity (4.4).
* `norm_taylor3_le`: third-order Taylor bound for a complex-valued function of a real variable,
  `‖g(y) − g(0) − y g'(0) − (y²/2) g''(0)‖ ≤ K|y|³/6` if `‖g'''‖ ≤ K` on `[−|y|, |y|]`.
* `log_norm_one_add_le`: for `‖w‖ ≤ 1/4`,
  `log|1+w| ≤ Re w − Re(w²)/2 + Re(w³)/3 + |w|⁴/3` (Mathlib's `Complex.norm_log_sub_logTaylor_le`);
  `abs_log_norm_one_add_le`: `|log|1+w|| ≤ (4/3)|w|`.
* `taylor_alg`: the real algebra of Step 2 of Lemma T, with `C_A = 20 C_H⁴`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped Real

namespace SmallGammaGeodesics

/-! ## Derivatives of the probe -/

theorem hasDerivAt_iteratedDeriv_probeH (j : ℕ) (a : ℝ) (d : ℕ) (z : ℂ) :
    HasDerivAt (iteratedDeriv d (probeH j a)) (iteratedDeriv (d + 1) (probeH j a) z) z := by
  have hfun : iteratedDeriv d (probeH j a) =
      fun z => probeG j d (z - a) - probeG j d (z + a) :=
    funext (iteratedDeriv_probeH j a d)
  rw [hfun, iteratedDeriv_probeH]
  exact ((hasDerivAt_probeG j d (z - a)).comp_sub_const z a).sub
    ((hasDerivAt_probeG j d (z + a)).comp_add_const z a)

theorem continuous_iteratedDeriv_probeH (j : ℕ) (a : ℝ) (d : ℕ) :
    Continuous (iteratedDeriv d (probeH j a)) :=
  continuous_iff_continuousAt.2 fun z => (hasDerivAt_iteratedDeriv_probeH j a d z).continuousAt

/-- **(I5)**: every derivative `H^{(d)}_{j,a}` is real on the real axis. -/
theorem im_iteratedDeriv_probeH_ofReal (j : ℕ) (a : ℝ) (d : ℕ) (x : ℝ) :
    (iteratedDeriv d (probeH j a) x).im = 0 := by
  induction d generalizing x with
  | zero => rw [iteratedDeriv_zero, probeH_ofReal, Complex.ofReal_im]
  | succ d ih =>
    have h1 : HasDerivAt (fun z => -Complex.I * iteratedDeriv d (probeH j a) z)
        (-Complex.I * iteratedDeriv (d + 1) (probeH j a) x) x :=
      (hasDerivAt_iteratedDeriv_probeH j a d x).const_mul _
    have h2 := h1.real_of_complex
    have h3 : (fun r : ℝ => (-Complex.I * iteratedDeriv d (probeH j a) r).re) = fun _ => 0 := by
      funext r
      simp [ih r]
    rw [h3] at h2
    have h4 := h2.unique (hasDerivAt_const x 0)
    simpa using h4

theorem ofReal_re_iteratedDeriv_probeH (j : ℕ) (a : ℝ) (d : ℕ) (x : ℝ) :
    ((iteratedDeriv d (probeH j a) x).re : ℂ) = iteratedDeriv d (probeH j a) x :=
  Complex.ext (by simp) (by simp [im_iteratedDeriv_probeH_ofReal])

/-- The kernel `H''` of the band identity (4.4) is the real part of the complex `H''`. -/
theorem iteratedDeriv_two_re_probeH (j : ℕ) (a t : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => (probeH j a x).re) t = (iteratedDeriv 2 (probeH j a) t).re := by
  have h1 : deriv (fun x : ℝ => (probeH j a x).re) =
      fun x : ℝ => (iteratedDeriv 1 (probeH j a) (x : ℂ)).re := by
    funext x
    have := hasDerivAt_iteratedDeriv_probeH j a 0 x
    rw [iteratedDeriv_zero] at this
    exact this.real_of_complex.deriv
  have h2 : deriv (fun x : ℝ => (iteratedDeriv 1 (probeH j a) (x : ℂ)).re) =
      fun x : ℝ => (iteratedDeriv 2 (probeH j a) (x : ℂ)).re := by
    funext x
    exact (hasDerivAt_iteratedDeriv_probeH j a 1 x).real_of_complex.deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1, h2]

/-! ## A third-order Taylor bound -/

theorem norm_taylor3_le_of_nonneg {g g₁ g₂ g₃ : ℝ → ℂ} (h₀ : ∀ s, HasDerivAt g (g₁ s) s)
    (h₁ : ∀ s, HasDerivAt g₁ (g₂ s) s) (h₂ : ∀ s, HasDerivAt g₂ (g₃ s) s) {K y : ℝ}
    (hy : 0 ≤ y) (hK : ∀ s ∈ Icc 0 y, ‖g₃ s‖ ≤ K) :
    ‖g y - g 0 - (y : ℂ) * g₁ 0 - ((y ^ 2 / 2 : ℝ) : ℂ) * g₂ 0‖ ≤ K * y ^ 3 / 6 := by
  have hc₀ : Continuous g := continuous_iff_continuousAt.2 fun s => (h₀ s).continuousAt
  have hc₁ : Continuous g₁ := continuous_iff_continuousAt.2 fun s => (h₁ s).continuousAt
  have hc₂ : Continuous g₂ := continuous_iff_continuousAt.2 fun s => (h₂ s).continuousAt
  -- `‖g₂ s − g₂ 0‖ ≤ K s`
  have s1 : ∀ s ∈ Icc 0 y, ‖g₂ s - g₂ 0‖ ≤ K * s := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := fun s => g₂ s - g₂ 0)
      (f' := g₃) (B := fun s => K * s) (B' := fun _ => K) (hc₂.sub continuous_const).continuousOn
      (fun s _ => ((h₂ s).sub_const (g₂ 0)).hasDerivWithinAt) (by simp) (fun s => ?_)
      (fun s hs => hK s (Ico_subset_Icc_self hs))
    exact ((hasDerivAt_id s).const_mul K).congr_deriv (by simp)
  -- `‖g₁ s − g₁ 0 − s g₂ 0‖ ≤ K s²/2`
  have s2 : ∀ s ∈ Icc 0 y, ‖g₁ s - g₁ 0 - (s : ℂ) * g₂ 0‖ ≤ K * s ^ 2 / 2 := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun s => g₁ s - g₁ 0 - (s : ℂ) * g₂ 0) (f' := fun s => g₂ s - g₂ 0)
      (B := fun s => K * s ^ 2 / 2) (B' := fun s => K * s) ?_ (fun s _ => ?_) (by simp)
      (fun s => ?_) (fun s hs => s1 s (Ico_subset_Icc_self hs))
    · exact ((hc₁.sub continuous_const).sub
        (Complex.continuous_ofReal.mul continuous_const)).continuousOn
    · have h := ((h₁ s).sub_const (g₁ 0)).sub ((hasDerivAt_id s).ofReal_comp.mul_const (g₂ 0))
      exact h.hasDerivWithinAt.congr_deriv (by simp)
    · exact (((hasDerivAt_pow 2 s).const_mul K).div_const 2).congr_deriv (by ring)
  -- `‖g s − g 0 − s g₁ 0 − (s²/2) g₂ 0‖ ≤ K s³/6`
  have s3 : ∀ s ∈ Icc 0 y,
      ‖g s - g 0 - (s : ℂ) * g₁ 0 - ((s ^ 2 / 2 : ℝ) : ℂ) * g₂ 0‖ ≤ K * s ^ 3 / 6 := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun s => g s - g 0 - (s : ℂ) * g₁ 0 - ((s ^ 2 / 2 : ℝ) : ℂ) * g₂ 0)
      (f' := fun s => g₁ s - g₁ 0 - (s : ℂ) * g₂ 0)
      (B := fun s => K * s ^ 3 / 6) (B' := fun s => K * s ^ 2 / 2) ?_ (fun s _ => ?_)
      (by simp) (fun s => ?_) (fun s hs => s2 s (Ico_subset_Icc_self hs))
    · exact (((hc₀.sub continuous_const).sub
        (Complex.continuous_ofReal.mul continuous_const)).sub
        ((Complex.continuous_ofReal.comp ((continuous_pow 2).div_const 2)).mul
          continuous_const)).continuousOn
    · have h := (((h₀ s).sub_const (g 0)).sub ((hasDerivAt_id s).ofReal_comp.mul_const (g₁ 0))).sub
        (((hasDerivAt_pow 2 s).div_const 2).ofReal_comp.mul_const (g₂ 0))
      refine h.hasDerivWithinAt.congr_deriv ?_
      push_cast
      ring
    · exact (((hasDerivAt_pow 3 s).const_mul K).div_const 6).congr_deriv (by ring)
  exact s3 y ⟨hy, le_rfl⟩

/-- **Third-order Taylor bound** for `g : ℝ → ℂ` with `g' = g₁`, `g₁' = g₂`, `g₂' = g₃` and
`‖g₃‖ ≤ K` on `[−|y|, |y|]`. -/
theorem norm_taylor3_le {g g₁ g₂ g₃ : ℝ → ℂ} (h₀ : ∀ s, HasDerivAt g (g₁ s) s)
    (h₁ : ∀ s, HasDerivAt g₁ (g₂ s) s) (h₂ : ∀ s, HasDerivAt g₂ (g₃ s) s) {K y : ℝ}
    (hK : ∀ s, |s| ≤ |y| → ‖g₃ s‖ ≤ K) :
    ‖g y - g 0 - (y : ℂ) * g₁ 0 - ((y ^ 2 / 2 : ℝ) : ℂ) * g₂ 0‖ ≤ K * |y| ^ 3 / 6 := by
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy]
    exact norm_taylor3_le_of_nonneg h₀ h₁ h₂ hy fun s hs => hK s (by
      rw [abs_of_nonneg hs.1, abs_of_nonneg hy]; exact hs.2)
  · have hd : ∀ (f f' : ℝ → ℂ), (∀ s, HasDerivAt f (f' s) s) →
        ∀ s, HasDerivAt (fun s => f (-s)) (-f' (-s)) s := by
      intro f f' hf s
      have := (hf (-s)).scomp s (hasDerivAt_neg s)
      simpa [Function.comp_def] using this
    have h := norm_taylor3_le_of_nonneg (g := fun s => g (-s)) (g₁ := fun s => -g₁ (-s))
      (g₂ := fun s => g₂ (-s)) (g₃ := fun s => -g₃ (-s)) (hd g g₁ h₀)
      (by
        intro s
        have := hd g₁ g₂ h₁ s
        exact this.neg.congr_deriv (by simp))
      (hd g₂ g₃ h₂) (y := -y) (by linarith)
      (fun s hs => by
        rw [norm_neg]
        exact hK (-s) (by rw [abs_neg, abs_of_nonneg hs.1, abs_of_nonpos hy]; exact hs.2))
    rw [abs_of_nonpos hy]
    have e : g (-(-y)) - g (-0) - ((-y : ℝ) : ℂ) * -g₁ (-0) - ((((-y) ^ 2 / 2 : ℝ)) : ℂ) * g₂ (-0) =
        g y - g 0 - (y : ℂ) * g₁ 0 - ((y ^ 2 / 2 : ℝ) : ℂ) * g₂ 0 := by
      simp only [neg_neg, neg_zero, even_two, Even.neg_pow]
      push_cast
      ring
    rw [← e]
    exact h

/-! ## The logarithm -/

/-- For `‖w‖ ≤ 1/4`: `log|1 + w| ≤ Re w − Re(w²)/2 + Re(w³)/3 + |w|⁴/3`. -/
theorem log_norm_one_add_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 4) :
    Real.log ‖1 + w‖ ≤ w.re - (w.re ^ 2 - w.im ^ 2) / 2 +
      (w.re ^ 3 - 3 * w.re * w.im ^ 2) / 3 + ‖w‖ ^ 4 / 3 := by
  have hw1 : ‖w‖ < 1 := by linarith
  have hT := Complex.norm_log_sub_logTaylor_le 3 hw1
  have hlt : Complex.logTaylor (3 + 1) w = w - w ^ 2 / 2 + w ^ 3 / 3 := by
    simp only [Complex.logTaylor, Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    ring
  rw [hlt] at hT
  have hpoly : (w - w ^ 2 / 2 + w ^ 3 / 3).re =
      w.re - (w.re ^ 2 - w.im ^ 2) / 2 + (w.re ^ 3 - 3 * w.re * w.im ^ 2) / 3 := by
    have h2 : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by
      rw [pow_two, Complex.mul_re]; ring
    have h3 : (w ^ 3).re = w.re ^ 3 - 3 * w.re * w.im ^ 2 := by
      rw [pow_three, Complex.mul_re, Complex.mul_re, Complex.mul_im]; ring
    rw [Complex.add_re, Complex.sub_re, Complex.div_ofNat_re, Complex.div_ofNat_re, h2, h3]
  have hn0 : 0 ≤ ‖w‖ := norm_nonneg w
  have hrem : ‖w‖ ^ (3 + 1) * (1 - ‖w‖)⁻¹ / ((3 : ℕ) + 1 : ℝ) ≤ ‖w‖ ^ 4 / 3 := by
    have h1 : (1 - ‖w‖)⁻¹ ≤ 4 / 3 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have h4 : 0 ≤ ‖w‖ ^ 4 := by positivity
    norm_num
    calc ‖w‖ ^ 4 * (1 - ‖w‖)⁻¹ / 4 ≤ ‖w‖ ^ 4 * (4 / 3) / 4 := by gcongr
      _ = ‖w‖ ^ 4 / 3 := by ring
  have hre : (Complex.log (1 + w) - (w - w ^ 2 / 2 + w ^ 3 / 3)).re ≤ ‖w‖ ^ 4 / 3 :=
    (Complex.re_le_norm _).trans (hT.trans (by exact_mod_cast hrem))
  rw [Complex.sub_re, Complex.log_re, hpoly] at hre
  linarith

/-- For `‖w‖ ≤ 1/4`: `|log|1 + w|| ≤ (4/3)|w|`. -/
theorem abs_log_norm_one_add_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 4) :
    |Real.log ‖1 + w‖| ≤ 4 / 3 * ‖w‖ := by
  have hn0 : 0 ≤ ‖w‖ := norm_nonneg w
  have hlow : 1 - ‖w‖ ≤ ‖1 + w‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-w)
    rw [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  have hup : ‖1 + w‖ ≤ 1 + ‖w‖ := by
    have := norm_add_le (1 : ℂ) w
    rwa [norm_one] at this
  have hpos : 0 < ‖1 + w‖ := by linarith
  rw [abs_le]
  constructor
  · have h1 := Real.one_sub_inv_le_log_of_pos hpos
    have h2 : ‖1 + w‖⁻¹ ≤ (1 - ‖w‖)⁻¹ := inv_anti₀ (by linarith) hlow
    have h3 : (1 - ‖w‖)⁻¹ ≤ 1 + 4 / 3 * ‖w‖ := by
      rw [inv_le_iff_one_le_mul₀ (by linarith)]
      nlinarith
    linarith
  · have h1 := Real.log_le_sub_one_of_pos hpos
    linarith

/-! ## The algebra of Step 2 -/

/-- **Step 2 of Lemma T, algebra** (`C_A = 20 C_H⁴`): with `w = iθ(u + iv)`, so that
`Re w = −θv` and `Im w = θu`, the cubic expansion of `log|1+w|` is bounded by the main terms
`−θ y H''(x) + θ² H'(x)²/2` plus `C_A (|θ||y|³ + θ²y² + |θ|³|y| + θ⁴) ℓ⁻⁴ E(x)`. Here
`m = ℓ⁻¹`, `e = E(x)`, `A_k = H^{(k)}(x)` and `u + iv = H'(x + iy)`. -/
theorem taylor_alg {θ y m e CH A₁ A₂ A₃ u v : ℝ} (hm : 0 < m) (he : 0 ≤ e) (he2 : e ≤ 2)
    (hCH : 1 ≤ CH) (hy : |y| * m ≤ 1) (hA₁ : |A₁| ≤ CH * m * e) (hA₂ : |A₂| ≤ CH * m ^ 2 * e)
    (hA₃ : |A₃| ≤ CH * m ^ 3 * e)
    (hu : |u - A₁ + y ^ 2 / 2 * A₃| ≤ CH * m ^ 4 * e * |y| ^ 3 / 6)
    (hv : |v - y * A₂| ≤ CH * m ^ 4 * e * |y| ^ 3 / 6)
    (hh : u ^ 2 + v ^ 2 ≤ (CH * m * e) ^ 2) :
    (-θ * v) - ((-θ * v) ^ 2 - (θ * u) ^ 2) / 2 + ((-θ * v) ^ 3 - 3 * (-θ * v) * (θ * u) ^ 2) / 3 +
        (θ ^ 2 * (u ^ 2 + v ^ 2)) ^ 2 / 3 ≤
      -θ * y * A₂ + θ ^ 2 * A₁ ^ 2 / 2 +
        20 * CH ^ 4 * (|θ| * |y| ^ 3 + θ ^ 2 * y ^ 2 + |θ| ^ 3 * |y| + θ ^ 4) * m ^ 4 * e := by
  have hy0 : 0 ≤ |y| := abs_nonneg y
  have hθ0 : 0 ≤ |θ| := abs_nonneg θ
  have hCH0 : 0 ≤ CH := by linarith
  have hm0 : 0 ≤ m := hm.le
  have hym1 : 0 ≤ |y| * m := mul_nonneg hy0 hm0
  have hy2' : |y| ^ 2 * m ^ 2 ≤ 1 := by
    have h := pow_le_one₀ (n := 2) hym1 hy
    rwa [mul_pow] at h
  have hy2 : y ^ 2 * m ^ 2 ≤ 1 := by rwa [sq_abs] at hy2'
  have hym : |y| ^ 3 * m ^ 4 ≤ y ^ 2 * m ^ 3 := by
    have e1 : |y| ^ 3 * m ^ 4 = (y ^ 2 * m ^ 3) * (|y| * m) := by rw [← sq_abs y]; ring
    rw [e1]
    exact mul_le_of_le_one_right (by positivity) hy
  have hym' : |y| ^ 3 * m ^ 4 ≤ |y| * m ^ 2 := by
    have e1 : |y| ^ 3 * m ^ 4 = (|y| * m ^ 2) * (|y| ^ 2 * m ^ 2) := by ring
    rw [e1]
    exact mul_le_of_le_one_right (by positivity) hy2'
  have hee : e * e ≤ 2 * e := mul_le_mul_of_nonneg_right he2 he
  have he4 : e * e ≤ 4 := by nlinarith
  -- (i) the linear term
  have P1 : -θ * v ≤ -θ * y * A₂ + |θ| * (CH * m ^ 4 * e * |y| ^ 3 / 6) := by
    have h1 : -θ * v = -θ * y * A₂ + (-θ) * (v - y * A₂) := by ring
    have h2 : (-θ) * (v - y * A₂) ≤ |θ| * (CH * m ^ 4 * e * |y| ^ 3 / 6) := by
      calc (-θ) * (v - y * A₂) ≤ |(-θ) * (v - y * A₂)| := le_abs_self _
        _ = |θ| * |v - y * A₂| := by rw [abs_mul, abs_neg]
        _ ≤ |θ| * (CH * m ^ 4 * e * |y| ^ 3 / 6) := mul_le_mul_of_nonneg_left hv hθ0
    linarith
  -- (ii) the quadratic term
  have hδ : |u - A₁| ≤ CH * y ^ 2 * m ^ 3 * e := by
    have h1 : |u - A₁| ≤ |u - A₁ + y ^ 2 / 2 * A₃| + |y ^ 2 / 2 * A₃| := by
      have := abs_sub (u - A₁ + y ^ 2 / 2 * A₃) (y ^ 2 / 2 * A₃)
      rwa [add_sub_cancel_right] at this
    have h2 : |y ^ 2 / 2 * A₃| ≤ CH * y ^ 2 * m ^ 3 * e / 2 := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      calc y ^ 2 / 2 * |A₃| ≤ y ^ 2 / 2 * (CH * m ^ 3 * e) :=
            mul_le_mul_of_nonneg_left hA₃ (by positivity)
        _ = CH * y ^ 2 * m ^ 3 * e / 2 := by ring
    have h3 : CH * m ^ 4 * e * |y| ^ 3 / 6 ≤ CH * y ^ 2 * m ^ 3 * e / 6 := by
      have e1 : CH * m ^ 4 * e * |y| ^ 3 / 6 = CH * e / 6 * (|y| ^ 3 * m ^ 4) := by ring
      have e2 : CH * y ^ 2 * m ^ 3 * e / 6 = CH * e / 6 * (y ^ 2 * m ^ 3) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left hym (by positivity)
    have h4 : 0 ≤ CH * y ^ 2 * m ^ 3 * e := by positivity
    linarith
  have hu2 : u ^ 2 ≤ A₁ ^ 2 + 6 * (CH ^ 2 * y ^ 2 * m ^ 4 * e) := by
    have hAδ : |A₁| * |u - A₁| ≤ 2 * (CH ^ 2 * y ^ 2 * m ^ 4 * e) := by
      calc |A₁| * |u - A₁| ≤ (CH * m * e) * (CH * y ^ 2 * m ^ 3 * e) :=
            mul_le_mul hA₁ hδ (abs_nonneg _) (by positivity)
        _ = (CH ^ 2 * y ^ 2 * m ^ 4) * (e * e) := by ring
        _ ≤ (CH ^ 2 * y ^ 2 * m ^ 4) * (2 * e) := mul_le_mul_of_nonneg_left hee (by positivity)
        _ = 2 * (CH ^ 2 * y ^ 2 * m ^ 4 * e) := by ring
    have hδ2 : |u - A₁| ^ 2 ≤ 2 * (CH ^ 2 * y ^ 2 * m ^ 4 * e) := by
      calc |u - A₁| ^ 2 ≤ (CH * y ^ 2 * m ^ 3 * e) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hδ 2
        _ = (CH ^ 2 * y ^ 2 * m ^ 4) * ((y ^ 2 * m ^ 2) * (e * e)) := by ring
        _ ≤ (CH ^ 2 * y ^ 2 * m ^ 4) * (1 * (2 * e)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul hy2 hee (by positivity) zero_le_one
        _ = 2 * (CH ^ 2 * y ^ 2 * m ^ 4 * e) := by ring
    have hsq : u ^ 2 ≤ A₁ ^ 2 + 2 * (|A₁| * |u - A₁|) + |u - A₁| ^ 2 := by
      have e1 : u ^ 2 = A₁ ^ 2 + 2 * (A₁ * (u - A₁)) + (u - A₁) ^ 2 := by ring
      have e2 : A₁ * (u - A₁) ≤ |A₁| * |u - A₁| := by rw [← abs_mul]; exact le_abs_self _
      rw [e1, ← sq_abs (u - A₁)]
      linarith
    linarith
  have P2 : -((-θ * v) ^ 2 - (θ * u) ^ 2) / 2 ≤
      θ ^ 2 * A₁ ^ 2 / 2 + 3 * (CH ^ 2 * (θ ^ 2 * y ^ 2) * m ^ 4 * e) := by
    have h1 : θ ^ 2 * u ^ 2 ≤ θ ^ 2 * (A₁ ^ 2 + 6 * (CH ^ 2 * y ^ 2 * m ^ 4 * e)) :=
      mul_le_mul_of_nonneg_left hu2 (sq_nonneg θ)
    have h2 : 0 ≤ (θ * v) ^ 2 := sq_nonneg _
    have e1 : -((-θ * v) ^ 2 - (θ * u) ^ 2) / 2 = (θ ^ 2 * u ^ 2 - (θ * v) ^ 2) / 2 := by ring
    have e2 : θ ^ 2 * (A₁ ^ 2 + 6 * (CH ^ 2 * y ^ 2 * m ^ 4 * e)) =
        θ ^ 2 * A₁ ^ 2 + 6 * (CH ^ 2 * (θ ^ 2 * y ^ 2) * m ^ 4 * e) := by ring
    rw [e1]
    linarith
  -- (iii) the cubic term
  have hvb : |v| ≤ 2 * (CH * |y| * m ^ 2 * e) := by
    have h1 : |v| ≤ |v - y * A₂| + |y * A₂| := by
      have := abs_add_le (v - y * A₂) (y * A₂)
      rwa [sub_add_cancel] at this
    have h2 : |y * A₂| ≤ CH * |y| * m ^ 2 * e := by
      rw [abs_mul]
      calc |y| * |A₂| ≤ |y| * (CH * m ^ 2 * e) := mul_le_mul_of_nonneg_left hA₂ hy0
        _ = CH * |y| * m ^ 2 * e := by ring
    have h3 : CH * m ^ 4 * e * |y| ^ 3 / 6 ≤ CH * |y| * m ^ 2 * e / 6 := by
      have e1 : CH * m ^ 4 * e * |y| ^ 3 / 6 = CH * e / 6 * (|y| ^ 3 * m ^ 4) := by ring
      have e2 : CH * |y| * m ^ 2 * e / 6 = CH * e / 6 * (|y| * m ^ 2) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left hym' (by positivity)
    have h4 : 0 ≤ CH * |y| * m ^ 2 * e := by positivity
    linarith
  have hu2' : u ^ 2 ≤ 4 * (CH ^ 2 * m ^ 2) := by
    have h1 : u ^ 2 ≤ (CH * m * e) ^ 2 := by have := sq_nonneg v; linarith
    have h2 : (CH * m * e) ^ 2 ≤ 4 * (CH ^ 2 * m ^ 2) := by
      calc (CH * m * e) ^ 2 = (CH ^ 2 * m ^ 2) * (e * e) := by ring
        _ ≤ (CH ^ 2 * m ^ 2) * 4 := mul_le_mul_of_nonneg_left he4 (by positivity)
        _ = 4 * (CH ^ 2 * m ^ 2) := by ring
    linarith
  have P3 : ((-θ * v) ^ 3 - 3 * (-θ * v) * (θ * u) ^ 2) / 3 ≤
      19 * (CH ^ 3 * (|θ| ^ 3 * |y|) * m ^ 4 * e) := by
    have hv3 : |v| ^ 3 ≤ 32 * (CH ^ 3 * |y| * m ^ 4 * e) := by
      calc |v| ^ 3 ≤ (2 * (CH * |y| * m ^ 2 * e)) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hvb 3
        _ = 8 * (CH ^ 3 * |y| * m ^ 4) * ((|y| ^ 2 * m ^ 2) * (e * e) * e) := by ring
        _ ≤ 8 * (CH ^ 3 * |y| * m ^ 4) * (1 * 4 * e) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right (mul_le_mul hy2' he4 (by positivity) zero_le_one) he
        _ = 32 * (CH ^ 3 * |y| * m ^ 4 * e) := by ring
    have hvu : |v| * u ^ 2 ≤ 8 * (CH ^ 3 * |y| * m ^ 4 * e) := by
      calc |v| * u ^ 2 ≤ (2 * (CH * |y| * m ^ 2 * e)) * (4 * (CH ^ 2 * m ^ 2)) :=
            mul_le_mul hvb hu2' (sq_nonneg _) (by positivity)
        _ = 8 * (CH ^ 3 * |y| * m ^ 4 * e) := by ring
    have e1 : (-θ * v) ^ 3 - 3 * (-θ * v) * (θ * u) ^ 2 =
        -(θ * v) ^ 3 + 3 * ((θ * v) * (θ ^ 2 * u ^ 2)) := by ring
    have b1 : -(θ * v) ^ 3 ≤ |θ| ^ 3 * |v| ^ 3 := by
      have h := neg_le_abs ((θ * v) ^ 3)
      have e : |(θ * v) ^ 3| = |θ| ^ 3 * |v| ^ 3 := by rw [abs_pow, abs_mul, mul_pow]
      linarith
    have b2 : (θ * v) * (θ ^ 2 * u ^ 2) ≤ |θ| ^ 3 * (|v| * u ^ 2) := by
      have h0 : 0 ≤ θ ^ 2 * u ^ 2 := by positivity
      calc (θ * v) * (θ ^ 2 * u ^ 2) ≤ |θ * v| * (θ ^ 2 * u ^ 2) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) h0
        _ = |θ| ^ 3 * (|v| * u ^ 2) := by rw [abs_mul, ← sq_abs θ]; ring
    have b3 : |θ| ^ 3 * |v| ^ 3 ≤ |θ| ^ 3 * (32 * (CH ^ 3 * |y| * m ^ 4 * e)) :=
      mul_le_mul_of_nonneg_left hv3 (by positivity)
    have b4 : |θ| ^ 3 * (|v| * u ^ 2) ≤ |θ| ^ 3 * (8 * (CH ^ 3 * |y| * m ^ 4 * e)) :=
      mul_le_mul_of_nonneg_left hvu (by positivity)
    have e2 : |θ| ^ 3 * (32 * (CH ^ 3 * |y| * m ^ 4 * e)) =
        32 * (CH ^ 3 * (|θ| ^ 3 * |y|) * m ^ 4 * e) := by ring
    have e3 : |θ| ^ 3 * (8 * (CH ^ 3 * |y| * m ^ 4 * e)) =
        8 * (CH ^ 3 * (|θ| ^ 3 * |y|) * m ^ 4 * e) := by ring
    have h0 : 0 ≤ CH ^ 3 * (|θ| ^ 3 * |y|) * m ^ 4 * e := by positivity
    rw [e1]
    linarith
  -- (iv) the quartic remainder
  have P4 : (θ ^ 2 * (u ^ 2 + v ^ 2)) ^ 2 / 3 ≤ 3 * (CH ^ 4 * θ ^ 4 * m ^ 4 * e) := by
    have h1 : θ ^ 2 * (u ^ 2 + v ^ 2) ≤ θ ^ 2 * (CH * m * e) ^ 2 :=
      mul_le_mul_of_nonneg_left hh (sq_nonneg θ)
    have h0 : 0 ≤ θ ^ 2 * (u ^ 2 + v ^ 2) := by positivity
    have h2 : (θ ^ 2 * (u ^ 2 + v ^ 2)) ^ 2 ≤ (θ ^ 2 * (CH * m * e) ^ 2) ^ 2 :=
      pow_le_pow_left₀ h0 h1 2
    have he3 : e ^ 3 ≤ 8 := by
      calc e ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ he he2 3
        _ = 8 := by norm_num
    have h3 : (θ ^ 2 * (CH * m * e) ^ 2) ^ 2 = (CH ^ 4 * θ ^ 4 * m ^ 4) * (e ^ 3 * e) := by ring
    have h4 : (CH ^ 4 * θ ^ 4 * m ^ 4) * (e ^ 3 * e) ≤ (CH ^ 4 * θ ^ 4 * m ^ 4) * (8 * e) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he3 he) (by positivity)
    have h5 : 0 ≤ CH ^ 4 * θ ^ 4 * m ^ 4 * e := by positivity
    have e6 : (CH ^ 4 * θ ^ 4 * m ^ 4) * (8 * e) = 8 * (CH ^ 4 * θ ^ 4 * m ^ 4 * e) := by ring
    linarith
  -- collecting the error terms
  have hC1 : CH ≤ CH ^ 4 := le_self_pow₀ hCH (by norm_num)
  have hC2 : CH ^ 2 ≤ CH ^ 4 := pow_le_pow_right₀ hCH (by norm_num)
  have hC3 : CH ^ 3 ≤ CH ^ 4 := pow_le_pow_right₀ hCH (by norm_num)
  have ht1 : 0 ≤ |θ| * |y| ^ 3 * m ^ 4 * e := by positivity
  have ht2 : 0 ≤ θ ^ 2 * y ^ 2 * m ^ 4 * e := by positivity
  have ht3 : 0 ≤ |θ| ^ 3 * |y| * m ^ 4 * e := by positivity
  have ht4 : 0 ≤ θ ^ 4 * m ^ 4 * e := by positivity
  have E1 : |θ| * (CH * m ^ 4 * e * |y| ^ 3 / 6) ≤ 20 * CH ^ 4 * (|θ| * |y| ^ 3 * m ^ 4 * e) := by
    have e1 : |θ| * (CH * m ^ 4 * e * |y| ^ 3 / 6) = CH / 6 * (|θ| * |y| ^ 3 * m ^ 4 * e) := by ring
    rw [e1]
    exact mul_le_mul_of_nonneg_right (by linarith) ht1
  have E2 : 3 * (CH ^ 2 * (θ ^ 2 * y ^ 2) * m ^ 4 * e) ≤
      20 * CH ^ 4 * (θ ^ 2 * y ^ 2 * m ^ 4 * e) := by
    have e1 : 3 * (CH ^ 2 * (θ ^ 2 * y ^ 2) * m ^ 4 * e) = 3 * CH ^ 2 * (θ ^ 2 * y ^ 2 * m ^ 4 * e) := by
      ring
    rw [e1]
    exact mul_le_mul_of_nonneg_right (by linarith) ht2
  have E3 : 19 * (CH ^ 3 * (|θ| ^ 3 * |y|) * m ^ 4 * e) ≤
      20 * CH ^ 4 * (|θ| ^ 3 * |y| * m ^ 4 * e) := by
    have e1 : 19 * (CH ^ 3 * (|θ| ^ 3 * |y|) * m ^ 4 * e) =
        19 * CH ^ 3 * (|θ| ^ 3 * |y| * m ^ 4 * e) := by ring
    rw [e1]
    exact mul_le_mul_of_nonneg_right (by linarith) ht3
  have E4 : 3 * (CH ^ 4 * θ ^ 4 * m ^ 4 * e) ≤ 20 * CH ^ 4 * (θ ^ 4 * m ^ 4 * e) := by
    have e1 : 3 * (CH ^ 4 * θ ^ 4 * m ^ 4 * e) = 3 * CH ^ 4 * (θ ^ 4 * m ^ 4 * e) := by ring
    rw [e1]
    have : 0 ≤ CH ^ 4 := by positivity
    exact mul_le_mul_of_nonneg_right (by linarith) ht4
  have hsum : 20 * CH ^ 4 * (|θ| * |y| ^ 3 + θ ^ 2 * y ^ 2 + |θ| ^ 3 * |y| + θ ^ 4) * m ^ 4 * e =
      20 * CH ^ 4 * (|θ| * |y| ^ 3 * m ^ 4 * e) + 20 * CH ^ 4 * (θ ^ 2 * y ^ 2 * m ^ 4 * e) +
        20 * CH ^ 4 * (|θ| ^ 3 * |y| * m ^ 4 * e) + 20 * CH ^ 4 * (θ ^ 4 * m ^ 4 * e) := by ring
  rw [hsum]
  linarith

end SmallGammaGeodesics
