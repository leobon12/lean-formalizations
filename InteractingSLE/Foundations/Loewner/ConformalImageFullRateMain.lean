import InteractingSLE.Foundations.Loewner.ConformalImageFullRate

/-!
# The capacity rate `ȧ = R_t'(W_t)²`: assembly

Packet PROVE-GEO-LOC2, step (2). From the pair estimates of `ConformalImageFullRate.lean`:

* `IsRefl.deriv_pos`: `R_t'(W_t)` is real and positive;
* `ImageHyp.le_norm_sub_of_annulus`: a uniform lower bound for `|R_{t}(w) − R_t(W_t)|` on the
  circle `|w − W_t| = ρ/32` for `t` slightly before a fixed time `s` (comparison with `R_s`);
* `ImageHyp.hasDerivWithinAt_cap`: `a(t) = ½ hcap(φ(K_t))` has derivative `R_s'(W_s)²` at
  every `s ∈ [0, T]` (within `[0, T]`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace ConformalImageFull

open ConformalImage

/-! ### The derivative at the driver is real and positive -/

theorem IsRefl.hasDerivAt {R G : ℂ → ℂ} {x ρ : ℝ} (hρ : 0 < ρ) (hG : IsRefl R x ρ G) :
    HasDerivAt G (deriv G x) x :=
  (hG.diff.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))).hasDerivAt

theorem IsRefl.deriv_im_eq_zero {R G : ℂ → ℂ} {x ρ : ℝ} (hρ : 0 < ρ) (hG : IsRefl R x ρ G) :
    (deriv G x).im = 0 := by
  have hd' : HasDerivAt (fun t : ℝ => G t) (deriv G x) x := (hG.hasDerivAt hρ).comp_ofReal
  have hT := (Complex.continuous_im.tendsto _).comp (hasDerivAt_iff_tendsto_slope.1 hd')
  have hev : (fun t : ℝ => (slope (fun t : ℝ => G t) x t).im) =ᶠ[𝓝[≠] x] fun _ => 0 := by
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds x (show 0 < ρ / 2 by positivity))]
      with t ht
    rw [slope_def_module, Complex.smul_im, sub_im]
    have h1 : ((t : ℂ)) ∈ ball (x : ℂ) (ρ / 2) := by
      rw [mem_ball, dist_eq_norm, ← ofReal_sub, Complex.norm_real, ← dist_eq_norm]; exact ht
    have h2 : ((x : ℂ)) ∈ ball (x : ℂ) (ρ / 2) := mem_ball_self (by positivity)
    rw [hG.real _ h1 (by simp), hG.real _ h2 (by simp)]
    simp
  exact tendsto_nhds_unique (hT.congr' hev) tendsto_const_nhds

theorem IsRefl.deriv_re_nonneg {R G : ℂ → ℂ} {x ρ : ℝ} (hρ : 0 < ρ) (hG : IsRefl R x ρ G)
    (hup : ∀ z ∈ ball (x : ℂ) (ρ / 2) ∩ H, 0 < (G z).im) : 0 ≤ (deriv G x).re := by
  have hp : HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * I) I 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const I).const_add (x : ℂ)
    simpa using this
  have hG0 : HasDerivAt G (deriv G x) ((x : ℂ) + ((0 : ℝ) : ℂ) * I) := by
    simpa using hG.hasDerivAt hρ
  have hd := HasDerivAt.comp (0 : ℝ) hG0 hp
  have hT := (Complex.continuous_im.tendsto _).comp (hasDerivAt_iff_tendsto_slope.1 hd)
  have hT' := hT.mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
  rw [show (deriv G x * I).im = (deriv G x).re by simp] at hT'
  refine ge_of_tendsto hT' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ρ / 2 by positivity)] with t ht
  simp only [Function.comp_apply]
  rw [slope_def_module, Complex.smul_im, sub_im]
  have hz : (x : ℂ) + (t : ℂ) * I ∈ ball (x : ℂ) (ρ / 2) ∩ H := mem_ball_inter_H ht.1 ht.2
  have h0 : (G ((x : ℂ) + ((0 : ℝ) : ℂ) * I)).im = 0 :=
    hG.real _ (by simpa using mem_ball_self (x := (x : ℂ)) (show 0 < ρ / 2 by positivity))
      (by simp)
  simp only [Function.comp_apply, h0, sub_zero, sub_zero]
  exact (mul_pos (inv_pos.2 ht.1) (hup _ hz)).le

/-- `R'(x)` is real and positive. -/
theorem IsRefl.deriv_pos {R G : ℂ → ℂ} {x ρ : ℝ} (hρ : 0 < ρ) (hG : IsRefl R x ρ G)
    (hup : ∀ z ∈ ball (x : ℂ) (ρ / 2) ∩ H, 0 < (G z).im) :
    0 < (deriv G x).re ∧ deriv G x = ((deriv G x).re : ℂ) := by
  have him := hG.deriv_im_eq_zero hρ
  have hne := QuantumZipper.CA.deriv_ne_zero_of_injOn isOpen_ball hG.diff hG.injOn
    (mem_ball_self (show 0 < ρ / 2 by positivity))
  have heq : deriv G x = ((deriv G x).re : ℂ) := Complex.ext (by simp) (by simp [him])
  refine ⟨lt_of_le_of_ne (hG.deriv_re_nonneg hρ hup) fun h0 => hne ?_, heq⟩
  rw [heq, ← h0, ofReal_zero]
/-- A positive lower bound for `|G z − G x|` on the closed annulus `ρ/64 ≤ |z − x| ≤ ρ/16`. -/
theorem IsRefl.exists_annulus_min {R G : ℂ → ℂ} {x ρ : ℝ} (hρ : 0 < ρ) (hG : IsRefl R x ρ G) :
    ∃ m > 0, ∀ z : ℂ, ρ / 64 ≤ ‖z - x‖ → ‖z - x‖ ≤ ρ / 16 → m ≤ ‖G z - G x‖ := by
  set K := closedBall (x : ℂ) (ρ / 16) ∩ {z : ℂ | ρ / 64 ≤ ‖z - x‖} with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
  have hKB : K ⊆ ball (x : ℂ) (ρ / 2) := fun z hz => by
    have := hz.1
    rw [mem_closedBall] at this
    rw [mem_ball]
    linarith
  have hn : ‖((x : ℂ) + ((ρ / 32 : ℝ) : ℂ)) - x‖ = ρ / 32 := by
    rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hz0 : ((x : ℂ) + ((ρ / 32 : ℝ) : ℂ)) ∈ K :=
    ⟨by rw [mem_closedBall, dist_eq_norm, hn]; linarith, by
      show ρ / 64 ≤ ‖((x : ℂ) + ((ρ / 32 : ℝ) : ℂ)) - x‖; rw [hn]; linarith⟩
  obtain ⟨z₀, hz₀, hmin⟩ := hKc.exists_isMinOn ⟨_, hz0⟩
    ((hG.diff.continuousOn.mono hKB).sub continuousOn_const).norm
  refine ⟨‖G z₀ - G x‖, norm_pos_iff.2 (sub_ne_zero.2 fun he => ?_), fun z hz1 hz2 =>
    hmin ⟨by rw [mem_closedBall, dist_eq_norm]; exact hz2, hz1⟩⟩
  have := hG.injOn (hKB hz₀) (mem_ball_self (by positivity)) he
  have h2 : ρ / 64 ≤ ‖z₀ - x‖ := hz₀.2
  rw [this, sub_self, norm_zero] at h2
  linarith

/-- **Arithmetic of the rate estimate.** -/
theorem norm_sub_sq_le {F₁ G₁ c : ℂ} {q r α β : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r) (hα : 0 ≤ α)
    (hF₁ : ‖F₁‖ ≤ 96) (hG₁ : ‖G₁‖ ≤ 96) (hc : ‖c‖ ≤ 96) (hF0 : F₁ ≠ 0)
    (h1 : ‖(q : ℂ) / F₁ - G₁‖ ≤ r * (α * q + β)) (hsmall : 96 * r * α ≤ 1 / 2) :
    ‖(q : ℂ) - c ^ 2‖ ≤
      96 * r * (α * (2 * (96 ^ 2 + 96 * r * β)) + β) + 96 * (‖F₁ - c‖ + ‖G₁ - c‖) := by
  have h2 : ‖(q : ℂ) - F₁ * G₁‖ ≤ 96 * (r * (α * q + β)) := by
    have e : (q : ℂ) - F₁ * G₁ = F₁ * ((q : ℂ) / F₁ - G₁) := by field_simp
    rw [e, norm_mul]
    exact mul_le_mul hF₁ h1 (norm_nonneg _) (by norm_num)
  have hFG : ‖F₁ * G₁‖ ≤ 96 * 96 := by
    rw [norm_mul]; exact mul_le_mul hF₁ hG₁ (norm_nonneg _) (by norm_num)
  have hqn : ‖(q : ℂ)‖ = q := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
  have hq' : q ≤ 2 * (96 ^ 2 + 96 * r * β) := by
    have h3 : ‖(q : ℂ)‖ ≤ ‖F₁ * G₁‖ + ‖(q : ℂ) - F₁ * G₁‖ := by
      have := norm_add_le (F₁ * G₁) ((q : ℂ) - F₁ * G₁)
      rwa [add_sub_cancel] at this
    rw [hqn] at h3
    have h4 : 96 * r * α * q ≤ 1 / 2 * q := mul_le_mul_of_nonneg_right hsmall hq
    nlinarith
  have h3 : ‖F₁ * G₁ - c ^ 2‖ ≤ 96 * (‖F₁ - c‖ + ‖G₁ - c‖) := by
    have e : F₁ * G₁ - c ^ 2 = (F₁ - c) * G₁ + c * (G₁ - c) := by ring
    rw [e]
    calc ‖(F₁ - c) * G₁ + c * (G₁ - c)‖ ≤ ‖F₁ - c‖ * ‖G₁‖ + ‖c‖ * ‖G₁ - c‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ ‖F₁ - c‖ * 96 + 96 * ‖G₁ - c‖ := by gcongr
      _ = 96 * (‖F₁ - c‖ + ‖G₁ - c‖) := by ring
  have h5 : α * q ≤ α * (2 * (96 ^ 2 + 96 * r * β)) := mul_le_mul_of_nonneg_left hq' hα
  calc ‖(q : ℂ) - c ^ 2‖ ≤ ‖(q : ℂ) - F₁ * G₁‖ + ‖F₁ * G₁ - c ^ 2‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 96 * (r * (α * q + β)) + 96 * (‖F₁ - c‖ + ‖G₁ - c‖) := add_le_add h2 h3
    _ ≤ 96 * r * (α * (2 * (96 ^ 2 + 96 * r * β)) + β) + 96 * (‖F₁ - c‖ + ‖G₁ - c‖) := by
        have : 96 * (r * (α * q + β)) ≤ 96 * r * (α * (2 * (96 ^ 2 + 96 * r * β)) + β) := by
          have := mul_le_mul_of_nonneg_left h5 (show (0 : ℝ) ≤ 96 * r by positivity)
          nlinarith
        linarith

/-- From the circle estimate to the slope: divide by `h = 2(s₂ − s₁) > 0`, `h' = q h`. -/
theorem norm_div_sub_le_of_pair {F₁ G₁ : ℂ} {q hh hh' r ε ε' d ρ : ℝ} (hhpos : 0 < hh)
    (hr : 0 < r) (hd : 0 < d) (hρ : 0 < ρ) (hq : hh' = q * hh)
    (P1 : ‖(hh' : ℂ) / F₁ - (hh : ℂ) * G₁‖ ≤
      r * (12 * ε' * hh' / d ^ 2 + 96 * (12 * ε * hh / r ^ 2) + 768 / ρ * (2 * hh / r) ^ 2)) :
    ‖(q : ℂ) / F₁ - G₁‖ ≤
      r * (12 * ε' / d ^ 2 * q + (1152 * ε / r ^ 2 + 3072 * hh / (ρ * r ^ 2))) := by
  have e1 : (hh' : ℂ) / F₁ - (hh : ℂ) * G₁ = (hh : ℂ) * ((q : ℂ) / F₁ - G₁) := by
    rw [hq]; push_cast; ring
  have e2 : r * (12 * ε' * hh' / d ^ 2 + 96 * (12 * ε * hh / r ^ 2) + 768 / ρ * (2 * hh / r) ^ 2) =
      hh * (r * (12 * ε' / d ^ 2 * q + (1152 * ε / r ^ 2 + 3072 * hh / (ρ * r ^ 2)))) := by
    rw [hq]; field_simp; ring
  rw [e1, e2, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hhpos] at P1
  exact le_of_mul_le_mul_left P1 hhpos

/-- The derivative-difference bound of the pair estimates is `O(κ)`. -/
theorem pair_two_le {u hh hh' r ε ε' d ρ κ : ℝ} (hr : 0 < r) (hd : 0 < d) (hρ : 0 < ρ)
    (hκ1 : κ ≤ 1) (hh0 : 0 ≤ hh) (hhκ : hh ≤ κ) (hh'0 : 0 ≤ hh') (hh'κ : hh' ≤ κ ^ 2)
    (hεκ : ε ≤ κ) (hε'κ : ε' ≤ κ)
    (P2 : u ≤ (hh' / d + 96 * hh / r + (12 * ε' * hh' / d ^ 2 + 96 * (12 * ε * hh / r ^ 2) +
      768 / ρ * (2 * hh / r) ^ 2)) / r) :
    u ≤ (1 / d + 96 / r + 12 / d ^ 2 + 1152 / r ^ 2 + 3072 / (ρ * r ^ 2)) / r * κ := by
  have hκ0 : 0 ≤ κ := hh0.trans hhκ
  have hκ2 : κ ^ 2 ≤ κ := by nlinarith
  have hκ3 : κ ^ 3 ≤ κ := by nlinarith
  have t1 : hh' / d ≤ κ / d := div_le_div_of_nonneg_right (hh'κ.trans hκ2) hd.le
  have t2 : 96 * hh / r ≤ 96 * κ / r := div_le_div_of_nonneg_right (by linarith) hr.le
  have t3 : 12 * ε' * hh' / d ^ 2 ≤ 12 * κ / d ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : ε' * hh' ≤ κ * κ ^ 2 := mul_le_mul hε'κ hh'κ hh'0 hκ0
    nlinarith
  have t4 : 96 * (12 * ε * hh / r ^ 2) ≤ 1152 * κ / r ^ 2 := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : ε * hh ≤ κ * κ := mul_le_mul hεκ hhκ hh0 hκ0
    nlinarith
  have t5 : 768 / ρ * (2 * hh / r) ^ 2 ≤ 3072 * κ / (ρ * r ^ 2) := by
    have e : 768 / ρ * (2 * hh / r) ^ 2 = 3072 * hh ^ 2 / (ρ * r ^ 2) := by field_simp; ring
    rw [e]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : hh ^ 2 ≤ κ ^ 2 := pow_le_pow_left₀ hh0 hhκ 2
    nlinarith
  have hsum : hh' / d + 96 * hh / r + (12 * ε' * hh' / d ^ 2 + 96 * (12 * ε * hh / r ^ 2) +
      768 / ρ * (2 * hh / r) ^ 2) ≤
      (1 / d + 96 / r + 12 / d ^ 2 + 1152 / r ^ 2 + 3072 / (ρ * r ^ 2)) * κ := by
    have e : (1 / d + 96 / r + 12 / d ^ 2 + 1152 / r ^ 2 + 3072 / (ρ * r ^ 2)) * κ =
        κ / d + 96 * κ / r + 12 * κ / d ^ 2 + 1152 * κ / r ^ 2 + 3072 * κ / (ρ * r ^ 2) := by
      ring
    rw [e]
    linarith
  calc u ≤ _ := P2
    _ ≤ (1 / d + 96 / r + 12 / d ^ 2 + 1152 / r ^ 2 + 3072 / (ρ * r ^ 2)) * κ / r :=
        div_le_div_of_nonneg_right hsum hr.le
    _ = _ := by ring

/-- The final bound of the rate estimate is `O(κ)`. -/
theorem rate_final_le {r d ρ κ hh X BX : ℝ} (hr : 0 < r) (hd : 0 < d) (hρ : 0 < ρ)
    (hκ1 : κ ≤ 1) (hh0 : 0 ≤ hh) (hhκ : hh ≤ κ) (hX : X ≤ BX * κ) :
    96 * r * (12 * κ / d ^ 2 * (2 * (96 ^ 2 + 96 * r * (1152 * κ / r ^ 2 +
        3072 * hh / (ρ * r ^ 2)))) + (1152 * κ / r ^ 2 + 3072 * hh / (ρ * r ^ 2))) + 96 * X ≤
      (96 * r * (12 / d ^ 2 * (2 * (96 ^ 2 + 96 * r * (1152 / r ^ 2 + 3072 / (ρ * r ^ 2)))) +
        (1152 / r ^ 2 + 3072 / (ρ * r ^ 2))) + 96 * BX) * κ := by
  have hκ0 : 0 ≤ κ := hh0.trans hhκ
  set Bβ := 1152 / r ^ 2 + 3072 / (ρ * r ^ 2) with hBβ
  have hBβ0 : 0 ≤ Bβ := by positivity
  have hβ : 1152 * κ / r ^ 2 + 3072 * hh / (ρ * r ^ 2) ≤ Bβ * κ := by
    have e : Bβ * κ = 1152 * κ / r ^ 2 + 3072 * κ / (ρ * r ^ 2) := by rw [hBβ]; ring
    rw [e]
    have : 3072 * hh / (ρ * r ^ 2) ≤ 3072 * κ / (ρ * r ^ 2) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hβ1 : 1152 * κ / r ^ 2 + 3072 * hh / (ρ * r ^ 2) ≤ Bβ :=
    hβ.trans (by nlinarith)
  have hβ0 : 0 ≤ 1152 * κ / r ^ 2 + 3072 * hh / (ρ * r ^ 2) := by positivity
  have h1 : 12 * κ / d ^ 2 * (2 * (96 ^ 2 + 96 * r * (1152 * κ / r ^ 2 +
      3072 * hh / (ρ * r ^ 2)))) ≤ 12 / d ^ 2 * (2 * (96 ^ 2 + 96 * r * Bβ)) * κ := by
    have e : 12 * κ / d ^ 2 = 12 / d ^ 2 * κ := by ring
    rw [e]
    have : 2 * (96 ^ 2 + 96 * r * (1152 * κ / r ^ 2 + 3072 * hh / (ρ * r ^ 2))) ≤
        2 * (96 ^ 2 + 96 * r * Bβ) := by
      have := mul_le_mul_of_nonneg_left hβ1 (show (0 : ℝ) ≤ 96 * r by positivity)
      linarith
    have h12 : (0 : ℝ) ≤ 12 / d ^ 2 * κ := by positivity
    calc 12 / d ^ 2 * κ * (2 * (96 ^ 2 + 96 * r * (1152 * κ / r ^ 2 + 3072 * hh / (ρ * r ^ 2))))
        ≤ 12 / d ^ 2 * κ * (2 * (96 ^ 2 + 96 * r * Bβ)) := mul_le_mul_of_nonneg_left this h12
      _ = 12 / d ^ 2 * (2 * (96 ^ 2 + 96 * r * Bβ)) * κ := by ring
  have h2 : 96 * r * (12 * κ / d ^ 2 * (2 * (96 ^ 2 + 96 * r * (1152 * κ / r ^ 2 +
      3072 * hh / (ρ * r ^ 2)))) + (1152 * κ / r ^ 2 + 3072 * hh / (ρ * r ^ 2))) ≤
      96 * r * (12 / d ^ 2 * (2 * (96 ^ 2 + 96 * r * Bβ)) + Bβ) * κ := by
    have := mul_le_mul_of_nonneg_left (add_le_add h1 hβ) (show (0 : ℝ) ≤ 96 * r by positivity)
    calc _ ≤ 96 * r * (12 / d ^ 2 * (2 * (96 ^ 2 + 96 * r * Bβ)) * κ + Bβ * κ) := this
      _ = _ := by ring
  have h3 : 96 * X ≤ 96 * BX * κ := by nlinarith
  calc _ ≤ 96 * r * (12 / d ^ 2 * (2 * (96 ^ 2 + 96 * r * Bβ)) + Bβ) * κ + 96 * BX * κ :=
        add_le_add h2 h3
    _ = _ := by ring

namespace ImageHyp

variable {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T ρ : ℝ}

/-- **A uniform lower bound on the circle for earlier times**: comparing `R_{s₁}` with the
later `R_{s₂}` through `R_{s₂} ∘ g_L = g_inc ∘ R_{s₁}`. -/
theorem le_norm_sub_of_annulus (h : ImageHyp W A φ T ρ) {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Icc 0 T)
    (hs₂ : s₂ ∈ Icc 0 T) (hss : s₁ ≤ s₂) {F G : ℂ → ℂ}
    (hF : IsRefl (mapOut (obstacle W A s₁)) (W s₁) ρ F)
    (hG : IsRefl (mapOut (obstacle W A s₂)) (W s₂) ρ G) (hGx : G (W s₂) = bdryDriver W A s₂)
    {ε ε' m : ℝ} (hε : 0 < ε) (hερ : ε ≤ ρ / 384) (hx : |W s₂ - W s₁| ≤ ρ / 128)
    (hL : gmap W s₁ '' (QuantumZipper.fwdHull W s₂ \ QuantumZipper.fwdHull W s₁) ⊆
      closedBall (W s₁ : ℂ) ε)
    (hε' : 0 < ε') (hinc : inc (imageHull W φ) s₁ s₂ ⊆ closedBall (bdryDriver W A s₁ : ℂ) ε')
    (hm : ∀ z : ℂ, ρ / 64 ≤ ‖z - W s₂‖ → ‖z - W s₂‖ ≤ ρ / 16 → m ≤ ‖G z - G (W s₂)‖)
    (hsmall : 9 * ε' + |bdryDriver W A s₁ - bdryDriver W A s₂| < m)
    {w : ℂ} (hw : w ∈ sphere (W s₁ : ℂ) (ρ / 32)) (hwH : 0 < w.im) :
    m - |bdryDriver W A s₁ - bdryDriver W A s₂| - ε' ≤ ‖F w - bdryDriver W A s₁‖ := by
  have hρ := h.pos
  set Ls := gmap W s₁ '' (QuantumZipper.fwdHull W s₂ \ QuantumZipper.fwdHull W s₁) with hLs
  have hLh : IsHPHull Ls := isHPHull_L h hs₁ hs₂ hss
  set I := inc (imageHull W φ) s₁ s₂ with hI
  have hIh : IsHPHull I := h.isHPHull_inc hs₁ hs₂ hss
  have hgL := isMapOut_mapOut hLh
  have hgI := isMapOut_mapOut hIh
  have hwx : ‖w - W s₁‖ = ρ / 32 := by rw [← dist_eq_norm]; exact hw
  have h4ε : 4 * ε ≤ ‖w - W s₁‖ := by rw [hwx]; linarith
  have hmove := hgL.norm_sub_le_of_four_mul_le hLh hε hL hwH h4ε
  have hx12 : ‖(W s₁ : ℂ) - W s₂‖ ≤ ρ / 128 := by
    rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]; exact hx
  set w₁ := mapOut Ls w with hw₁
  have hlow : ρ / 64 ≤ ‖w₁ - W s₂‖ := by
    have : ‖w - W s₁‖ ≤ ‖w - w₁‖ + ‖w₁ - W s₂‖ + ‖(W s₂ : ℂ) - W s₁‖ := by
      calc ‖w - W s₁‖ ≤ ‖w - w₁‖ + ‖w₁ - W s₁‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ‖w - w₁‖ + (‖w₁ - W s₂‖ + ‖(W s₂ : ℂ) - W s₁‖) := by
          gcongr; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ = _ := by ring
    have e1 : ‖w - w₁‖ = ‖w₁ - w‖ := norm_sub_rev _ _
    have e2 : ‖(W s₂ : ℂ) - W s₁‖ = ‖(W s₁ : ℂ) - W s₂‖ := norm_sub_rev _ _
    linarith
  have hup : ‖w₁ - W s₂‖ ≤ ρ / 16 := by
    calc ‖w₁ - W s₂‖ ≤ ‖w₁ - w‖ + ‖w - W s₂‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖w₁ - w‖ + (‖w - W s₁‖ + ‖(W s₁ : ℂ) - W s₂‖) := by
          gcongr; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ρ / 16 := by linarith
  have hwLs : w ∉ Ls := fun hwL => by
    have := hL hwL
    rw [mem_closedBall, dist_eq_norm, hwx] at this
    linarith
  have hw₁H : w₁ ∈ H := hgL.1.2.mapsTo ⟨hwH, hwLs⟩
  have hwB₁ : w ∈ ball (W s₁ : ℂ) (ρ / 2) := by rw [mem_ball, dist_eq_norm, hwx]; linarith
  have hwE : w ∉ obstacle W A s₁ := fun hwE =>
    Set.disjoint_left.1 (h.disjoint_ball_obstacle hs₁) (ball_subset_ball (by linarith) hwB₁) hwE
  have hid : G w₁ = mapOut I (F w) := by
    rw [hG.eqOn ⟨by rw [mem_ball, dist_eq_norm]; linarith, hw₁H⟩, hF.eqOn ⟨hwB₁, hwH⟩]
    exact mapOut_comp_eq h hs₁ hs₂ hss ⟨hwH, fun h' => h'.elim hwE hwLs⟩
  have hm' : m ≤ ‖mapOut I (F w) - bdryDriver W A s₂‖ := by
    rw [← hid, ← hGx]; exact hm w₁ hlow hup
  set v := F w with hv
  have hR₁ := isMapOut_mapOut (h.isHPHull_obstacle hs₁)
  have hvH : v ∈ H := by
    rw [hv, hF.eqOn ⟨hwB₁, hwH⟩]; exact hR₁.1.2.mapsTo ⟨hwH, hwE⟩
  have hvI : v ∉ I := by
    rw [hI, inc_eq h hs₁ hs₂]
    rintro ⟨l, hl, hlv⟩
    have hlH : l ∈ H := hLh.1 hl
    have hlE : l ∉ obstacle W A s₁ := fun hlE => by
      have := hL hl
      rw [mem_closedBall] at this
      exact Set.disjoint_left.1 (h.disjoint_ball_obstacle hs₁)
        (by rw [mem_ball]; linarith) hlE
    rw [hv, hF.eqOn ⟨hwB₁, hwH⟩] at hlv
    have := hR₁.1.2.injOn ⟨hlH, hlE⟩ ⟨hwH, hwE⟩ hlv
    exact hwLs (this ▸ hl)
  have hy12 : ‖(bdryDriver W A s₁ : ℂ) - bdryDriver W A s₂‖ =
      |bdryDriver W A s₁ - bdryDriver W A s₂| := by
    rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have htri : ‖mapOut I v - bdryDriver W A s₂‖ ≤
      ‖mapOut I v - bdryDriver W A s₁‖ + |bdryDriver W A s₁ - bdryDriver W A s₂| := by
    rw [← hy12]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  by_cases hv4 : 4 * ε' ≤ ‖v - bdryDriver W A s₁‖
  · have hfar := hgI.norm_sub_le_of_four_mul_le hIh hε' hinc hvH hv4
    have : ‖mapOut I v - bdryDriver W A s₁‖ ≤ ‖mapOut I v - v‖ + ‖v - bdryDriver W A s₁‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    linarith
  · exfalso
    have hnear := hgI.norm_sub_center_le hIh hε' hinc ⟨hvH, hvI⟩
    rw [not_le] at hv4
    linarith
theorem abs_sub_re_lt {q η B Cst κ : ℝ} {c : ℂ} (hB : ‖(q : ℂ) - c ^ 2‖ ≤ B)
    (hBC : B ≤ Cst * κ) (hCst : 0 < Cst) (hη : 0 < η) (hκη : κ ≤ η / (2 * Cst)) :
    |q - (c ^ 2).re| < η := by
  have h1 : |q - (c ^ 2).re| ≤ ‖(q : ℂ) - c ^ 2‖ := by
    have := Complex.abs_re_le_norm ((q : ℂ) - c ^ 2)
    simpa using this
  have h2 : Cst * κ ≤ η / 2 := by
    calc Cst * κ ≤ Cst * (η / (2 * Cst)) := mul_le_mul_of_nonneg_left hκη hCst.le
      _ = η / 2 := by field_simp
  linarith

/-- **The capacity rate** ([Law05] §4.6.1, `ḃ = 2 Φ_t'(U_t)²`): the clock
`a(t) = ½ hcap(φ(K_t))` has derivative `R_s'(W_s)²` at every `s ∈ [0, T]` (within `[0, T]`),
where `R_s'(W_s)` is the derivative at the driver of the reflection of `R_s = g_{E_s}`. -/
theorem hasDerivWithinAt_cap (h : ImageHyp W A φ T ρ) {s : ℝ} (hs : s ∈ Icc 0 T) {G : ℂ → ℂ}
    (hG : IsRefl (mapOut (obstacle W A s)) (W s) ρ G) (hGx : G (W s) = bdryDriver W A s) :
    HasDerivWithinAt (cap (imageHull W φ)) ((deriv G (W s) ^ 2).re) (Icc 0 T) s := by
  have hρ := h.pos
  have hg := h.isContinuouslyGrowing
  have hfam : ∀ t ∈ Icc (0 : ℝ) T, ∃ Gt : ℂ → ℂ,
      IsRefl (mapOut (obstacle W A t)) (W t) ρ Gt ∧ Gt (W t) = bdryDriver W A t := by
    intro t ht
    obtain ⟨Gt, hGt, hGtx⟩ := IsMapOut.exists_isRefl (h.isHPHull_obstacle ht)
      (isMapOut_mapOut (h.isHPHull_obstacle ht)) hρ (h.disjoint_ball_obstacle ht)
    exact ⟨Gt, hGt, by rw [hGtx, h.bdryDriver_eq ht]⟩
  choose! Gf hGf hGfx using hfam
  set c := deriv G (W s) with hc
  have hsB : ((W s : ℝ) : ℂ) ∈ ball ((W s : ℝ) : ℂ) (ρ / 4) := mem_ball_self (by positivity)
  have hc96 : ‖c‖ ≤ 96 := norm_deriv_le_96 hρ hG.diff hG.lip hsB
  obtain ⟨m, hm0, hm⟩ := hG.exists_annulus_min hρ
  set d := m / 2 with hd
  have hd0 : 0 < d := by positivity
  set r : ℝ := ρ / 32 with hr
  have hr0 : 0 < r := by positivity
  set BP := (1 / d + 96 / r + 12 / d ^ 2 + 1152 / r ^ 2 + 3072 / (ρ * r ^ 2)) / r with hBP
  set BX := BP + 2 * (768 / ρ) with hBX
  set Cst := 96 * r * (12 / d ^ 2 * (2 * (96 ^ 2 + 96 * r * (1152 / r ^ 2 +
    3072 / (ρ * r ^ 2)))) + (1152 / r ^ 2 + 3072 / (ρ * r ^ 2))) + 96 * BX with hCst
  have hCst0 : 0 < Cst := by positivity
  rw [hasDerivWithinAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
  intro η hη
  set κ := min (min (min 1 (ρ / 384)) (min (d / 4) (m / 12)))
    (min (d ^ 2 / (2304 * r)) (η / (2 * Cst))) with hκ
  have hκ0 : 0 < κ := lt_min (lt_min (lt_min one_pos (by positivity))
    (lt_min (by positivity) (by positivity))) (lt_min (by positivity) (by positivity))
  have hκ1 : κ ≤ 1 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hκρ : κ ≤ ρ / 384 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hκd : κ ≤ d / 4 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hκm : κ ≤ m / 12 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hκα : κ ≤ d ^ 2 / (2304 * r) := (min_le_right _ _).trans (min_le_left _ _)
  have hκη : κ ≤ η / (2 * Cst) := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : 96 * r * (12 * κ / d ^ 2) ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity)] at hκα
    rw [show 96 * r * (12 * κ / d ^ 2) = 1152 * r * κ / d ^ 2 by ring,
      div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨δ₁, hδ₁, hL⟩ := h.exists_gmap_diff_subset hκ0
  obtain ⟨δ₂, hδ₂, hI⟩ := h.growth_image hκ0
  obtain ⟨δ₃, hδ₃, hWu⟩ := h.exists_uniform hκ0
  obtain ⟨δ₄, hδ₄, hY⟩ := h.abs_bdryDriver_sub_le hκ0
  refine ⟨min (min δ₁ δ₂) (min (min δ₃ δ₄) (κ / 2)), by positivity, fun t ht htd => ?_⟩
  have ht1 : t ∈ Icc 0 T := ht.1
  have hts : t ≠ s := ht.2
  rw [Real.dist_eq] at htd
  have hd1 : |t - s| < δ₁ := lt_of_lt_of_le htd ((min_le_left _ _).trans (min_le_left _ _))
  have hd2 : |t - s| < δ₂ := lt_of_lt_of_le htd ((min_le_left _ _).trans (min_le_right _ _))
  have hd3 : |t - s| < δ₃ := lt_of_lt_of_le htd
    ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hd4 : |t - s| < δ₄ := lt_of_lt_of_le htd
    ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hd5 : |t - s| < κ / 2 := lt_of_lt_of_le htd ((min_le_right _ _).trans (min_le_right _ _))
  have hWts : |W t - W s| ≤ κ := hWu t ht1 s hs hd3.le
  have hx64 : |W t - W s| ≤ ρ / 64 := by linarith
  have hx64' : |W s - W t| ≤ ρ / 64 := by rw [abs_sub_comm]; exact hx64
  have hx128' : |W s - W t| ≤ ρ / 128 := by rw [abs_sub_comm]; linarith
  have hBXP : BP ≤ BX := by rw [hBX]; linarith [show (0 : ℝ) ≤ 2 * (768 / ρ) by positivity]
  rw [Real.dist_eq, slope_def_field]
  rcases lt_or_gt_of_ne hts with hlt | hgt
  · -- left case: the pair `(t, s)`
    have hst : s - t = |t - s| := by rw [abs_sub_comm, abs_of_pos (sub_pos.2 hlt)]
    have hLt := hL t ht1 s hs hlt.le (by rw [hst]; exact hd1.le)
    have hIt := hI t ht1 s hs hlt.le (by rw [hst]; exact hd2.le)
    have hYts : |bdryDriver W A t - bdryDriver W A s| ≤ κ := by
      rw [abs_sub_comm]; exact hY t ht1 s hs hlt.le (by rw [hst]; exact hd4.le)
    have hdw : ∀ w ∈ sphere (W t : ℂ) (ρ / 32), 0 < w.im →
        d ≤ ‖Gf t w - bdryDriver W A t‖ := fun w hw hwH => by
      have := le_norm_sub_of_annulus h ht1 hs hlt.le (hGf t ht1) hG hGx hκ0 hκρ hx128' hLt hκ0
        hIt hm (by linarith) hw hwH
      linarith
    obtain ⟨P1, P2⟩ := pair_estimates h ht1 hs hlt.le (hGf t ht1) (hGfx t ht1) hG hκ0 hκρ hx64'
      hLt hκ0 hIt hd0 (by linarith) hdw
    set hh := 2 * (s - t) with hhh
    have hhpos : 0 < hh := by rw [hhh]; linarith
    have hhκ : hh ≤ κ := by rw [hhh, hst]; linarith
    have hcap := hg.cap_sub_eq ht1 hs hlt.le
    set q := (cap (imageHull W φ) s - cap (imageHull W φ) t) / (s - t) with hq
    have hq' : hcapSet (inc (imageHull W φ) t s) = q * hh := by
      rw [hq, hhh]; field_simp; linarith
    have hI0 : 0 ≤ hcapSet (inc (imageHull W φ) t s) := by
      rw [hcapSet_eq (h.isHPHull_inc ht1 hs hlt.le)]; exact HPHull.hcap_nonneg _
    have hq0 : 0 ≤ q := by
      rw [hq]; apply div_nonneg _ (by linarith)
      rw [hcap]; exact div_nonneg hI0 two_pos.le
    have h1 := norm_div_sub_le_of_pair hhpos hr0 hd0 hρ hq' P1
    have hxt : ((W t : ℝ) : ℂ) ∈ ball ((W s : ℝ) : ℂ) (ρ / 8) := by
      rw [mem_ball, dist_eq_norm, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; linarith
    have hF₁ : ‖deriv (Gf t) (W t)‖ ≤ 96 :=
      norm_deriv_le_96 hρ (hGf t ht1).diff (hGf t ht1).lip (mem_ball_self (by positivity))
    have hG₁ : ‖deriv G (W t)‖ ≤ 96 :=
      norm_deriv_le_96 hρ hG.diff hG.lip (ball_subset_ball (by linarith) hxt)
    have hF0 := QuantumZipper.CA.deriv_ne_zero_of_injOn isOpen_ball (hGf t ht1).diff
      (hGf t ht1).injOn (mem_ball_self (show 0 < ρ / 2 by positivity))
    have hB := norm_sub_sq_le (c := c) hq0 hr0.le (by positivity) hF₁ hG₁ hc96
      hF0 h1 hsmall
    -- the derivative differences
    have hGc : ‖deriv G (W t) - c‖ ≤ 768 / ρ * κ := by
      have hG' : DifferentiableOn ℂ (deriv G) (ball ((W s : ℝ) : ℂ) (ρ / 2)) :=
        (hG.diff.analyticOnNhd isOpen_ball).deriv.differentiableOn
      have := (convex_ball ((W s : ℝ) : ℂ) (ρ / 8)).norm_image_sub_le_of_norm_deriv_le
        (fun z hz => hG'.differentiableAt (isOpen_ball.mem_nhds
          (ball_subset_ball (by linarith) hz)))
        (fun z hz => norm_deriv_deriv_le hρ hG.diff hG.lip hz)
        (mem_ball_self (by positivity)) hxt
      rw [hc]
      refine this.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hWts
    have hP2 : ‖deriv G (W t) - deriv (Gf t) (W t)‖ ≤ BP * κ := pair_two_le hr0 hd0 hρ hκ1
      hhpos.le hhκ
      (by rw [hcapSet_eq (h.isHPHull_inc ht1 hs hlt.le)]; exact HPHull.hcap_nonneg _)
      (hg.hcapSet_inc_le ht1 hs hlt.le hIt) le_rfl le_rfl P2
    have hX : ‖deriv (Gf t) (W t) - c‖ + ‖deriv G (W t) - c‖ ≤ BX * κ := by
      have e1 : ‖deriv (Gf t) (W t) - c‖ ≤ ‖deriv G (W t) - deriv (Gf t) (W t)‖ +
          ‖deriv G (W t) - c‖ := by
        rw [norm_sub_rev (deriv G (W t))]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      have e2 : BX * κ = BP * κ + 2 * (768 / ρ * κ) := by rw [hBX]; ring
      rw [e2]
      linarith
    have hfin := rate_final_le hr0 hd0 hρ hκ1 hhpos.le hhκ hX
    have e : (cap (imageHull W φ) t - cap (imageHull W φ) s) / (t - s) = q := by
      rw [hq]; rw [← neg_sub, ← neg_sub s t, neg_div_neg_eq]
    rw [e]
    exact abs_sub_re_lt hB (hfin.trans_eq' rfl) hCst0 hη hκη
  · -- right case: the pair `(s, t)`
    have hst : t - s = |t - s| := (abs_of_pos (sub_pos.2 hgt)).symm
    have hLt := hL s hs t ht1 hgt.le (by rw [hst]; exact hd1.le)
    have hIt := hI s hs t ht1 hgt.le (by rw [hst]; exact hd2.le)
    have hdw : ∀ w ∈ sphere (W s : ℂ) (ρ / 32), 0 < w.im →
        d ≤ ‖G w - bdryDriver W A s‖ := fun w hw hwH => by
      have hwn : ‖w - W s‖ = ρ / 32 := by rw [← dist_eq_norm]; exact hw
      have := hm w (by rw [hwn]; linarith) (by rw [hwn]; linarith)
      rw [hGx] at this
      linarith
    obtain ⟨P1, P2⟩ := pair_estimates h hs ht1 hgt.le hG hGx (hGf t ht1) hκ0 hκρ hx64
      hLt hκ0 hIt hd0 (by linarith) hdw
    set hh := 2 * (t - s) with hhh
    have hhpos : 0 < hh := by rw [hhh]; linarith
    have hhκ : hh ≤ κ := by rw [hhh, hst]; linarith
    have hcap := hg.cap_sub_eq hs ht1 hgt.le
    set q := (cap (imageHull W φ) t - cap (imageHull W φ) s) / (t - s) with hq
    have hq' : hcapSet (inc (imageHull W φ) s t) = q * hh := by
      rw [hq, hhh]; field_simp; linarith
    have hI0 : 0 ≤ hcapSet (inc (imageHull W φ) s t) := by
      rw [hcapSet_eq (h.isHPHull_inc hs ht1 hgt.le)]; exact HPHull.hcap_nonneg _
    have hq0 : 0 ≤ q := by
      rw [hq]; apply div_nonneg _ (by linarith)
      rw [hcap]; exact div_nonneg hI0 two_pos.le
    have h1 := norm_div_sub_le_of_pair hhpos hr0 hd0 hρ hq' P1
    have hxt : ((W s : ℝ) : ℂ) ∈ ball ((W t : ℝ) : ℂ) (ρ / 4) := by
      rw [mem_ball, dist_eq_norm, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; linarith
    have hG₁ : ‖deriv (Gf t) (W s)‖ ≤ 96 :=
      norm_deriv_le_96 hρ (hGf t ht1).diff (hGf t ht1).lip hxt
    have hF0 := QuantumZipper.CA.deriv_ne_zero_of_injOn isOpen_ball hG.diff hG.injOn
      (mem_ball_self (show 0 < ρ / 2 by positivity))
    have hB := norm_sub_sq_le (c := c) hq0 hr0.le (by positivity) hc96 hG₁ hc96
      hF0 h1 hsmall
    have hP2 : ‖deriv (Gf t) (W s) - deriv G (W s)‖ ≤ BP * κ := pair_two_le hr0 hd0 hρ hκ1
      hhpos.le hhκ
      (by rw [hcapSet_eq (h.isHPHull_inc hs ht1 hgt.le)]; exact HPHull.hcap_nonneg _)
      (hg.hcapSet_inc_le hs ht1 hgt.le hIt) le_rfl le_rfl P2
    have hX : ‖deriv G (W s) - c‖ + ‖deriv (Gf t) (W s) - c‖ ≤ BX * κ := by
      rw [← hc, sub_self, norm_zero, zero_add]
      have : 0 ≤ 2 * (768 / ρ) * κ := by positivity
      have e2 : BX * κ = BP * κ + 2 * (768 / ρ) * κ := by rw [hBX]; ring
      rw [e2]
      linarith
    have hfin := rate_final_le hr0 hd0 hρ hκ1 hhpos.le hhκ hX
    exact abs_sub_re_lt hB (hfin.trans_eq' rfl) hCst0 hη hκη

end ImageHyp

end ConformalImageFull

end InteractingSLE
