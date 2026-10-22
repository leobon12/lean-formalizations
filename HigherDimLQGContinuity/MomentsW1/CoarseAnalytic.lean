import HigherDimLQGContinuity.MomentsW1.Coarse

/-!
# Elementary exponential estimates for the coarse envelope

These estimates separate the dyadic scale, spatial radius and tail parameter in the Gaussian
one-scale bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory HigherDimLFPP

namespace HigherDimLQGContinuity

/-- Expansion of the point Gaussian exponent. -/
theorem wnZR_point_exp_bound {v L u q c : ℝ}
    (hv : 0 < v) :
    Real.exp (-((q * v + c * L + u / 2) ^ 2 / (2 * v))) ≤
      Real.exp (-(q ^ 2 / 2 * v + q * c * L + q * u / 2)) := by
  apply Real.exp_le_exp.mpr
  have hcross : 0 ≤ (c * L + u / 2) ^ 2 := sq_nonneg _
  have hv2 : 0 < 2 * v := by positivity
  rw [neg_le_neg_iff]
  apply (le_div_iff₀ hv2).mpr
  nlinarith only [hcross]

/-- Expansion of the cell-oscillation Gaussian exponent. -/
theorem wnZR_osc_exp_bound {v L u g c C : ℝ}
    (hv : 0 ≤ v) (hL : 0 ≤ L) (hu : 0 ≤ u) (hg : 0 ≤ g) (hc : 0 ≤ c)
    (hC : 0 < C) :
    Real.exp (-((g * v + c * L + u / 2) ^ 2 / C)) ≤
      Real.exp (-(g ^ 2 * v ^ 2 / C + c ^ 2 * L ^ 2 / C + u ^ 2 / (4 * C))) := by
  apply Real.exp_le_exp.mpr
  rw [neg_le_neg_iff]
  have hu2 : 0 ≤ u / 2 := by positivity
  have hnum : g ^ 2 * v ^ 2 + c ^ 2 * L ^ 2 + u ^ 2 / 4 ≤
      (g * v + c * L + u / 2) ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg hg hv) (mul_nonneg hc hL),
      mul_nonneg (mul_nonneg hg hv) hu2,
      mul_nonneg (mul_nonneg hc hL) hu2]
  calc
    g ^ 2 * v ^ 2 / C + c ^ 2 * L ^ 2 / C + u ^ 2 / (4 * C)
        = (g ^ 2 * v ^ 2 + c ^ 2 * L ^ 2 + u ^ 2 / 4) / C := by ring
    _ ≤ (g * v + c * L + u / 2) ^ 2 / C :=
      div_le_div_of_nonneg_right hnum hC.le

/-- A quadratic Gaussian scale decay dominates any positive exponential scale count. -/
theorem wnZR_quadratic_linear_bound {a b x : ℝ} (ha : 0 < a)
    (hb : 0 ≤ b) (hx : 0 ≤ x) : b * x - a * x ^ 2 ≤ b ^ 2 / a := by
  apply (le_div_iff₀ ha).mpr
  nlinarith only [sq_nonneg (a * x - b), mul_nonneg (mul_nonneg ha.le hb) hx]

/-- A logarithmic penalty with coefficient at least `d` absorbs the box-count factor. -/
theorem wnZR_spatial_cancel (d : ℕ) {R a : ℝ} (hR : 1 ≤ R) (ha : (d : ℝ) ≤ a) :
    (1 + R) ^ d * Real.exp (-a * Real.log (2 + R)) ≤ 1 := by
  have h1 : 0 < 1 + R := by linarith
  have h2 : 0 < 2 + R := by linarith
  have hlog : Real.log (1 + R) ≤ Real.log (2 + R) :=
    Real.log_le_log h1 (by linarith)
  have hlog0 : 0 ≤ Real.log (2 + R) := Real.log_nonneg (by linarith)
  have hexp : (1 + R) ^ d = Real.exp ((d : ℝ) * Real.log (1 + R)) := by
    rw [Real.exp_nat_mul, Real.exp_log h1]
  rw [hexp, ← Real.exp_add]
  have hle : (d : ℝ) * Real.log (1 + R) + -a * Real.log (2 + R) ≤ 0 := by
    have hfirst := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg d)
    have hsecond := mul_le_mul_of_nonneg_right ha hlog0
    linarith
  exact (Real.exp_le_exp.mpr hle).trans_eq (Real.exp_zero)

/-- The Gaussian cell tail also absorbs the spatial box count. -/
theorem wnZR_osc_spatial_cancel (d : ℕ) {R c C : ℝ} (hR : 1 ≤ R)
    (hC : 0 < C) (hc : 2 * C * d ≤ c ^ 2) :
    (1 + R) ^ d * Real.exp (-(c ^ 2 * Real.log (2 + R) ^ 2 / C)) ≤ 1 := by
  have hlog : 1 / 2 ≤ Real.log (2 + R) := by
    have hlt : Real.log 2 ≤ Real.log (2 + R) :=
      Real.log_le_log (by norm_num) (by linarith)
    have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    exact htwo.trans hlt
  have hc0 : 0 ≤ c ^ 2 := sq_nonneg c
  have hcoeff : (d : ℝ) ≤ c ^ 2 * Real.log (2 + R) / C := by
    apply (le_div_iff₀ hC).mpr
    nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hlog)]
  have h := wnZR_spatial_cancel d hR hcoeff
  have he : -(c ^ 2 * Real.log (2 + R) ^ 2 / C) =
      -(c ^ 2 * Real.log (2 + R) / C) * Real.log (2 + R) := by ring
  rw [he]
  exact h

/-- A Gaussian tail controls any prescribed exponential tail. -/
theorem wnZR_gaussian_to_exponential {C r u : ℝ} (hC : 0 < C) :
    Real.exp (-(u ^ 2 / (4 * C))) ≤
      Real.exp (C * r ^ 2) * Real.exp (-r * u) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsq : 0 ≤ (u - 2 * C * r) ^ 2 := sq_nonneg _
  have hC4 : 0 < 4 * C := by positivity
  have hineq : r * u - C * r ^ 2 ≤ u ^ 2 / (4 * C) := by
    apply (le_div_iff₀ hC4).mpr
    nlinarith only [hsq]
  linarith

theorem wnZR_two_pow_exp (d m : ℕ) :
    (2 : ℝ) ^ (d * m) = Real.exp ((d : ℝ) * m * Real.log 2) := by
  rw [show (d : ℝ) * m = ((d * m : ℕ) : ℝ) by push_cast; ring]
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

theorem wnZR_point_scale_bound (d : ℕ) {m : ℕ} (hm : 1 ≤ m) {R u q c : ℝ}
    (hR : 1 ≤ R) (hqc : (d : ℝ) ≤ q * c) :
    (1 + R) ^ d * (2 : ℝ) ^ (d * m) *
        Real.exp (-((q * (m * Real.log 2) + c * Real.log (2 + R) + u / 2) ^ 2 /
          (2 * (m * Real.log 2)))) ≤
      Real.exp (-(q ^ 2 / 2 - d) * (m * Real.log 2)) * Real.exp (-q * u / 2) := by
  have hv : 0 < (m : ℝ) * Real.log 2 := by
    exact mul_pos (by exact_mod_cast hm) (Real.log_pos (by norm_num))
  have hsp := wnZR_spatial_cancel d hR hqc
  calc
    (1 + R) ^ d * (2 : ℝ) ^ (d * m) *
        Real.exp (-((q * (m * Real.log 2) + c * Real.log (2 + R) + u / 2) ^ 2 /
          (2 * (m * Real.log 2))))
        ≤ (1 + R) ^ d * (2 : ℝ) ^ (d * m) *
          Real.exp (-(q ^ 2 / 2 * (m * Real.log 2) +
            q * c * Real.log (2 + R) + q * u / 2)) := by
              exact mul_le_mul_of_nonneg_left (wnZR_point_exp_bound hv) (by positivity)
    _ = ((1 + R) ^ d * Real.exp (-(q * c) * Real.log (2 + R))) *
          (Real.exp (-(q ^ 2 / 2 - d) * (m * Real.log 2)) *
            Real.exp (-q * u / 2)) := by
              have he : (d : ℝ) * m * Real.log 2 -
                  (q ^ 2 / 2 * (m * Real.log 2) + q * c * Real.log (2 + R) + q * u / 2) =
                  -(q * c) * Real.log (2 + R) +
                    (-(q ^ 2 / 2 - d) * (m * Real.log 2) + -q * u / 2) := by ring
              rw [wnZR_two_pow_exp]
              calc
                (1 + R) ^ d * Real.exp ((d : ℝ) * m * Real.log 2) *
                    Real.exp (-(q ^ 2 / 2 * (m * Real.log 2) +
                      q * c * Real.log (2 + R) + q * u / 2))
                    = (1 + R) ^ d * Real.exp ((d : ℝ) * m * Real.log 2 -
                        (q ^ 2 / 2 * (m * Real.log 2) +
                          q * c * Real.log (2 + R) + q * u / 2)) := by
                            rw [mul_assoc, ← Real.exp_add]
                            simp only [sub_eq_add_neg]
                _ = (1 + R) ^ d * Real.exp (-(q * c) * Real.log (2 + R) +
                      (-(q ^ 2 / 2 - d) * (m * Real.log 2) + -q * u / 2)) := by rw [he]
                _ = _ := by rw [Real.exp_add, Real.exp_add]; ring
    _ ≤ 1 * (Real.exp (-(q ^ 2 / 2 - d) * (m * Real.log 2)) *
          Real.exp (-q * u / 2)) :=
            mul_le_mul_of_nonneg_right hsp (by positivity)
    _ = _ := one_mul _

/-- The cell Gaussian exponent absorbs the spatial grid and its dyadic growth. -/
theorem wnZR_osc_exponent_bound (d : ℕ) (m : ℕ)
    {R u g c C r : ℝ} (hR : 1 ≤ R) (hu : 0 ≤ u) (hg : 0 < g)
    (hc0 : 0 ≤ c) (hC : 0 < C) (hc : 2 * C * d ≤ c ^ 2) :
    (d : ℝ) * Real.log (1 + R) + d * m * Real.log 2 -
      (g * (m * Real.log 2) + c * Real.log (2 + R) + u / 2) ^ 2 / C ≤
      (d * Real.log 2 + 1) ^ 2 / (g ^ 2 * Real.log 2 ^ 2 / C) - m + C * r ^ 2 - r * u := by
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hL2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1 : 0 < 1 + R := by linarith
  have hlog2 : 0 < 2 + R := by linarith
  have hlog0 : 0 ≤ Real.log (2 + R) := Real.log_nonneg (by linarith)
  have hloghalf : (1 / 2 : ℝ) ≤ Real.log (2 + R) := by
    have hloglt := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ 2 + R)
    have := Real.log_two_gt_d9
    linarith
  have hspcoeff : (d : ℝ) ≤ c ^ 2 * Real.log (2 + R) / C := by
    apply (le_div_iff₀ hC).mpr
    nlinarith [mul_nonneg (sq_nonneg c) (sub_nonneg.mpr hloghalf)]
  have hsp : (d : ℝ) * Real.log (1 + R) ≤
      c ^ 2 * Real.log (2 + R) ^ 2 / C := by
    have h1 := mul_le_mul_of_nonneg_left
      (Real.log_le_log hlog1 (by linarith : 1 + R ≤ 2 + R)) (Nat.cast_nonneg d)
    have h2 := mul_le_mul_of_nonneg_right hspcoeff hlog0
    have he : c ^ 2 * Real.log (2 + R) / C * Real.log (2 + R) =
        c ^ 2 * Real.log (2 + R) ^ 2 / C := by ring
    rw [he] at h2
    linarith
  set a : ℝ := g ^ 2 * Real.log 2 ^ 2 / C with ha_def
  have ha : 0 < a := by dsimp [a]; positivity
  set b : ℝ := d * Real.log 2 + 1 with hb_def
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hquad := wnZR_quadratic_linear_bound ha hb hm0
  have hquad' : (d : ℝ) * m * Real.log 2 -
      g ^ 2 * (m * Real.log 2) ^ 2 / C ≤ b ^ 2 / a - m := by
    calc
      (d : ℝ) * m * Real.log 2 - g ^ 2 * (m * Real.log 2) ^ 2 / C
          = b * m - a * m ^ 2 - m := by dsimp [a, b]; ring
      _ ≤ b ^ 2 / a - m := sub_le_sub_right hquad m
  have hgauss : -(u ^ 2 / (4 * C)) ≤ C * r ^ 2 - r * u := by
    have hsq := sq_nonneg (u - 2 * C * r)
    have hC4 : 0 < 4 * C := by positivity
    have hineq : r * u - C * r ^ 2 ≤ u ^ 2 / (4 * C) := by
      apply (le_div_iff₀ hC4).mpr
      nlinarith only [hsq]
    linarith
  have hosc : g ^ 2 * (m * Real.log 2) ^ 2 / C +
      c ^ 2 * Real.log (2 + R) ^ 2 / C + u ^ 2 / (4 * C) ≤
      (g * (m * Real.log 2) + c * Real.log (2 + R) + u / 2) ^ 2 / C := by
    have hv : 0 ≤ (m : ℝ) * Real.log 2 := mul_nonneg hm0 hL2.le
    have hexp := wnZR_osc_exp_bound hv hlog0 hu hg.le hc0 hC
    have hneg := Real.exp_le_exp.mp hexp
    linarith
  dsimp [a, b] at hquad' ⊢
  linarith only [hsp, hquad', hgauss, hosc]

theorem wnZR_osc_scale_bound (d m : ℕ) {R u g c C r : ℝ}
    (hR : 1 ≤ R) (hu : 0 ≤ u) (hg : 0 < g) (hc0 : 0 ≤ c)
    (hC : 0 < C) (hc : 2 * C * d ≤ c ^ 2) :
    (1 + R) ^ d * (2 : ℝ) ^ (d * m) *
        Real.exp (-((g * (m * Real.log 2) + c * Real.log (2 + R) + u / 2) ^ 2 / C)) ≤
      Real.exp ((d * Real.log 2 + 1) ^ 2 / (g ^ 2 * Real.log 2 ^ 2 / C) +
        C * r ^ 2) * Real.exp (-(m : ℝ)) * Real.exp (-r * u) := by
  have h1 : 0 < 1 + R := by linarith
  have hpowR : (1 + R) ^ d = Real.exp ((d : ℝ) * Real.log (1 + R)) := by
    rw [Real.exp_nat_mul, Real.exp_log h1]
  have hexp := wnZR_osc_exponent_bound d m (r := r) hR hu hg hc0 hC hc
  calc
    (1 + R) ^ d * (2 : ℝ) ^ (d * m) *
        Real.exp (-((g * (m * Real.log 2) + c * Real.log (2 + R) + u / 2) ^ 2 / C))
        = Real.exp ((d : ℝ) * Real.log (1 + R) + d * m * Real.log 2 -
            (g * (m * Real.log 2) + c * Real.log (2 + R) + u / 2) ^ 2 / C) := by
              rw [hpowR, wnZR_two_pow_exp]
              rw [mul_assoc, ← Real.exp_add, ← Real.exp_add]
              congr 1
              ring
    _ ≤ Real.exp ((d * Real.log 2 + 1) ^ 2 /
          (g ^ 2 * Real.log 2 ^ 2 / C) - m + C * r ^ 2 - r * u) :=
            Real.exp_le_exp.mpr hexp
    _ = Real.exp ((d * Real.log 2 + 1) ^ 2 /
          (g ^ 2 * Real.log 2 ^ 2 / C) + C * r ^ 2) *
          Real.exp (-(m : ℝ)) * Real.exp (-r * u) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            ring

/-- The two Gaussian contributions on one dyadic scale share one exponential tail. -/
theorem wnZR_one_scale_analytic (d m : ℕ) (hm : 1 ≤ m)
    {R u q c₁ g c₂ C r α : ℝ} (hR : 1 ≤ R) (hu : 0 ≤ u)
    (hqc : (d : ℝ) ≤ q * c₁) (hqr : r ≤ q / 2)
    (hg : 0 < g) (hc₂ : 0 ≤ c₂) (hC : 0 < C)
    (hc₂sq : 2 * C * d ≤ c₂ ^ 2)
    (hαpoint : α ≤ (q ^ 2 / 2 - d) * Real.log 2) (hαone : α ≤ 1) :
    ((Osc.grid (0 : HigherDimLFPP.Rd d) (R + 5) ((2 : ℝ)⁻¹ ^ m)).card : ℝ) *
      (2 * Real.exp (-((q * (m * Real.log 2) + c₁ * Real.log (2 + R) + u / 2) ^ 2 /
        (2 * (m * Real.log 2)))) +
       2 * Real.exp (-((g * (m * Real.log 2) + c₂ * Real.log (2 + R) + u / 2) ^ 2 / C))) ≤
      (16 : ℝ) ^ d * 2 *
        (1 + Real.exp ((d * Real.log 2 + 1) ^ 2 /
          (g ^ 2 * Real.log 2 ^ 2 / C) + C * r ^ 2)) *
        Real.exp (-α * m) * Real.exp (-r * u) := by
  have hgrid : ((Osc.grid (0 : HigherDimLFPP.Rd d) (R + 5) ((2 : ℝ)⁻¹ ^ m)).card : ℝ) ≤
      (16 : ℝ) ^ d * ((1 + R) ^ d * (2 : ℝ) ^ (d * m)) := by
    calc
      ((Osc.grid (0 : HigherDimLFPP.Rd d) (R + 5) ((2 : ℝ)⁻¹ ^ m)).card : ℝ)
          ≤ (16 * (1 + R) * (2 : ℝ) ^ m) ^ d := wnZR_grid_card_le R hR m
      _ = (16 : ℝ) ^ d * ((1 + R) ^ d * (2 : ℝ) ^ (d * m)) := by
        rw [mul_pow, mul_pow, ← pow_mul, Nat.mul_comm m d]
        ring
  have hpoint := wnZR_point_scale_bound d hm hR hqc (u := u)
  have hpoint' : (1 + R) ^ d * (2 : ℝ) ^ (d * m) *
      Real.exp (-((q * (m * Real.log 2) + c₁ * Real.log (2 + R) + u / 2) ^ 2 /
        (2 * (m * Real.log 2)))) ≤ Real.exp (-α * m) * Real.exp (-r * u) := by
    refine hpoint.trans ?_
    have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
    have hscale : α * m ≤ (q ^ 2 / 2 - d) * (m * Real.log 2) := by
      calc
        α * m ≤ ((q ^ 2 / 2 - d) * Real.log 2) * m :=
          mul_le_mul_of_nonneg_right hαpoint hm0
        _ = (q ^ 2 / 2 - d) * (m * Real.log 2) := by ring
    have hu' : r * u ≤ q * u / 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hqr) hu]
    have h1 : Real.exp (-(q ^ 2 / 2 - d) * (m * Real.log 2)) ≤
        Real.exp (-α * m) :=
      Real.exp_le_exp.mpr (by simpa only [neg_mul] using (neg_le_neg hscale))
    have h2 : Real.exp (-q * u / 2) ≤ Real.exp (-r * u) :=
      Real.exp_le_exp.mpr (by simpa only [neg_mul, neg_div] using (neg_le_neg hu'))
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hosc := wnZR_osc_scale_bound d m hR hu hg hc₂ hC hc₂sq (r := r)
  have hosc' : (1 + R) ^ d * (2 : ℝ) ^ (d * m) *
      Real.exp (-((g * (m * Real.log 2) + c₂ * Real.log (2 + R) + u / 2) ^ 2 / C)) ≤
      Real.exp ((d * Real.log 2 + 1) ^ 2 /
          (g ^ 2 * Real.log 2 ^ 2 / C) + C * r ^ 2) *
          Real.exp (-α * m) * Real.exp (-r * u) := by
    refine hosc.trans ?_
    have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
    have hm' : α * m ≤ m := by nlinarith [mul_nonneg (sub_nonneg.mpr hαone) hm0]
    have hexp : Real.exp (-(m : ℝ)) ≤ Real.exp (-α * m) :=
      Real.exp_le_exp.mpr (by simpa only [neg_mul] using (neg_le_neg hm'))
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le) (Real.exp_pos _).le
  have hsum : 0 ≤ 2 * Real.exp (-((q * (m * Real.log 2) +
      c₁ * Real.log (2 + R) + u / 2) ^ 2 / (2 * (m * Real.log 2)))) +
      2 * Real.exp (-((g * (m * Real.log 2) + c₂ * Real.log (2 + R) + u / 2) ^ 2 / C)) := by positivity
  calc
    ((Osc.grid (0 : HigherDimLFPP.Rd d) (R + 5) ((2 : ℝ)⁻¹ ^ m)).card : ℝ) * _
        ≤ ((16 : ℝ) ^ d * ((1 + R) ^ d * (2 : ℝ) ^ (d * m))) * _ :=
          mul_le_mul_of_nonneg_right hgrid hsum
    _ = (16 : ℝ) ^ d * 2 *
        (((1 + R) ^ d * (2 : ℝ) ^ (d * m) *
            Real.exp (-((q * (m * Real.log 2) + c₁ * Real.log (2 + R) + u / 2) ^ 2 /
              (2 * (m * Real.log 2))))) +
          ((1 + R) ^ d * (2 : ℝ) ^ (d * m) *
            Real.exp (-((g * (m * Real.log 2) + c₂ * Real.log (2 + R) + u / 2) ^ 2 / C)))) := by ring
    _ ≤ (16 : ℝ) ^ d * 2 *
        (Real.exp (-α * m) * Real.exp (-r * u) +
          Real.exp ((d * Real.log 2 + 1) ^ 2 /
            (g ^ 2 * Real.log 2 ^ 2 / C) + C * r ^ 2) *
            Real.exp (-α * m) * Real.exp (-r * u)) := by
              gcongr
    _ = _ := by ring

/-- Parameters for the coarse one-scale estimate. `CZ` depends only on `d` and the small-box
constant `C`, while `K` and the scale-decay rate may depend on the slope `Q`. -/
theorem wnZR_exists_coarse_parameters (d : ℕ) (hd : 2 ≤ d) {C : ℝ} (hC : 0 < C) :
    ∃ CZ : ℝ, 0 < CZ ∧ ∀ Q : ℝ, Real.sqrt (2 * d) < Q →
      ∃ K α : ℝ, 0 < K ∧ 0 < α ∧
      ∀ m : ℕ, 1 ≤ m → ∀ R u : ℝ, 1 ≤ R → 0 ≤ u →
        let q := (Q + Real.sqrt (2 * d)) / 2
        let g := (Q - Real.sqrt (2 * d)) / 2
        let c₂ := 2 * (C + d + 1)
        (q * (m * Real.log 2) + Real.sqrt (2 * d) * Real.log (2 + R) + u / 2) + C +
          (g * (m * Real.log 2) + c₂ * Real.log (2 + R) + u / 2) ≤
          Q * m * Real.log 2 + CZ * Real.log (2 + R) + u ∧
        ((Osc.grid (0 : Rd d) (R + 5) ((2 : ℝ)⁻¹ ^ m)).card : ℝ) *
          (2 * Real.exp (-((q * (m * Real.log 2) + Real.sqrt (2 * d) *
              Real.log (2 + R) + u / 2) ^ 2 / (2 * (m * Real.log 2)))) +
           2 * Real.exp (-((g * (m * Real.log 2) + c₂ * Real.log (2 + R) + u / 2) ^ 2 / C))) ≤
          K * Real.exp (-α * m) *
            Real.exp (-(Real.sqrt (2 * d) / 2) * u) := by
  let c₁ : ℝ := Real.sqrt (2 * d)
  let c₂ : ℝ := 2 * (C + d + 1)
  let CZ : ℝ := c₁ + c₂ + 2 * C
  have hc₁0 : 0 < c₁ := by dsimp [c₁]; positivity
  have hc₂0 : 0 ≤ c₂ := by dsimp [c₂]; positivity
  have hc₂sq : 2 * C * d ≤ c₂ ^ 2 := by
    dsimp [c₂]
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    nlinarith [sq_nonneg (C - (d : ℝ)), mul_nonneg hC.le hd0]
  have hCZ : 0 < CZ := by dsimp [CZ]; positivity
  refine ⟨CZ, hCZ, ?_⟩
  intro Q hQ
  let q : ℝ := (Q + c₁) / 2
  let g : ℝ := (Q - c₁) / 2
  let r : ℝ := c₁ / 2
  have hq : c₁ < q := by dsimp [q, c₁] at *; linarith
  have hg : 0 < g := by dsimp [g, c₁] at *; linarith
  have hr : 0 < r := by dsimp [r]; positivity
  have hc₁sq : c₁ ^ 2 = 2 * d := by
    dsimp [c₁]
    exact Real.sq_sqrt (by positivity)
  have hqc : (d : ℝ) ≤ q * c₁ := by
    have hmul := mul_le_mul_of_nonneg_right hq.le hc₁0.le
    nlinarith only [hmul, hc₁sq]
  have hδ : 0 < q ^ 2 / 2 - d := by
    have hsum : 0 < q + c₁ := by linarith
    have hmul := mul_pos (sub_pos.mpr hq) hsum
    nlinarith only [hmul, hc₁sq]
  let α : ℝ := min ((q ^ 2 / 2 - d) * Real.log 2) 1
  have hα : 0 < α := by
    dsimp [α]
    exact lt_min (mul_pos hδ (Real.log_pos (by norm_num))) one_pos
  let K : ℝ := (16 : ℝ) ^ d * 2 *
    (1 + Real.exp ((d * Real.log 2 + 1) ^ 2 /
      (g ^ 2 * Real.log 2 ^ 2 / C) + C * r ^ 2))
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, α, hK, hα, ?_⟩
  intro m hm R u hR hu
  dsimp only
  have hloghalf : (1 / 2 : ℝ) ≤ Real.log (2 + R) := by
    have hloglt := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (by linarith : 2 ≤ 2 + R)
    have := Real.log_two_gt_d9
    linarith
  constructor
  · dsimp [q, g, c₁, c₂, CZ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hloghalf) hC.le]
  · dsimp [c₁, c₂, q, g, K]
    exact wnZR_one_scale_analytic d m hm hR hu hqc (by dsimp [r]; linarith [hq])
      hg hc₂0 hC hc₂sq (min_le_left _ _) (min_le_right _ _)

end HigherDimLQGContinuity
