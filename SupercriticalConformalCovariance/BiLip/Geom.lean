import SupercriticalConformalCovariance.Univalent.KoebeCore

/-!
# Lemma 2.1: the normalized univalent maps at one centre, quantitatively

Paper l. 112–117: `F(w) = (φ(z + r w) − φ(z)) / (r φ′(z))` is a normalized univalent map on `B_{s/r}(0)`
whenever `φ` is univalent on `B_s(z)`; by the Koebe distortion theorem it is close to the identity on fixed
disks once `r/s` is small. The Koebe estimates' quantitative bounds (`normalized_map_bound`,
`normalized_deriv_bound`) and the Koebe covering theorem give this **uniformly in the centre**:

`geomGood_of_ball`: for every `ε > 0` there is an absolute `c₀ > 0` such that `r ≤ c₀ s` implies
`GeomGood φ U z r ε`, i.e. in the original coordinates (`ρ = r |φ′(z)|`):
* `φ` is `ε ρ`-close to its linearization `φ(z) + φ′(z)(x − z)` on `B̄_{3r}(z)`;
* every `y ∈ B̄_{3ρ}(φ(z))` is `φ(x)` for some `x ∈ B̄_{4r}(z)` which is `ε r`-close to the linear preimage
  `z + (y − φ(z))/φ′(z)`, and `|φ′(z)/φ′(x) − 1| ≤ ε` (the log-derivative correction of l. 120–122).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology

namespace SupercriticalConformalCovariance.BiLip

/-- The geometry of `φ` at the centre `z` and scale `r`, with tolerance `ε`. -/
def GeomGood (φ : ℂ → ℂ) (U : Set ℂ) (z : ℂ) (r ε : ℝ) : Prop :=
  0 < r ∧ deriv φ z ≠ 0 ∧ closedBall z (4 * r) ⊆ U ∧
  (∀ x ∈ closedBall z (3 * r),
    ‖φ x - φ z - deriv φ z * (x - z)‖ ≤ ε * (r * ‖deriv φ z‖)) ∧
  (∀ y ∈ closedBall (φ z) (3 * (r * ‖deriv φ z‖)), ∃ x ∈ closedBall z (4 * r), φ x = y ∧
    ‖x - z - (y - φ z) / deriv φ z‖ ≤ ε * r ∧ ‖deriv φ z / deriv φ x - 1‖ ≤ ε)

/-- The Koebe constant of the Koebe estimates, made available (and enlarged to be `≥ 1`). -/
theorem exists_koebe_const : ∃ C : ℝ, 1 ≤ C ∧
    (∀ {f : ℂ → ℂ} {R : ℝ}, 0 < R → DifferentiableOn ℂ f (ball 0 R) → InjOn f (ball 0 R) →
      f 0 = 0 → deriv f 0 = 1 → ∀ {w : ℂ}, ‖w‖ ≤ R / 4 → ‖f w - w‖ ≤ C * ‖w‖ ^ 2 / R) ∧
    (∀ {f : ℂ → ℂ} {R : ℝ}, 0 < R → DifferentiableOn ℂ f (ball 0 R) → InjOn f (ball 0 R) →
      deriv f 0 = 1 → ∀ {w : ℂ}, ‖w‖ ≤ R / 4 → ‖deriv f w - 1‖ ≤ C * ‖w‖ / R) := by
  obtain ⟨C₀, h1, h2⟩ : ∃ C₀ : ℝ,
      (∀ {f : ℂ → ℂ} {R : ℝ}, 0 < R → DifferentiableOn ℂ f (ball 0 R) → InjOn f (ball 0 R) →
        f 0 = 0 → deriv f 0 = 1 → ∀ {w : ℂ}, ‖w‖ ≤ R / 4 → ‖f w - w‖ ≤ C₀ * ‖w‖ ^ 2 / R) ∧
      (∀ {f : ℂ → ℂ} {R : ℝ}, 0 < R → DifferentiableOn ℂ f (ball 0 R) → InjOn f (ball 0 R) →
        deriv f 0 = 1 → ∀ {w : ℂ}, ‖w‖ ≤ R / 4 → ‖deriv f w - 1‖ ≤ C₀ * ‖w‖ / R) :=
    ⟨_, fun hR hd hi h0 h1 _ hw => SupercriticalConformalCovariance.Univalent.normalized_map_bound hR hd hi h0 h1 hw,
      fun hR hd hi h1 _ hw => SupercriticalConformalCovariance.Univalent.normalized_deriv_bound hR hd hi h1 hw⟩
  refine ⟨max C₀ 1, le_max_right _ _, fun hR hd hi h0 hd1 w hw => ?_,
    fun hR hd hi hd1 w hw => ?_⟩
  · refine (h1 hR hd hi h0 hd1 hw).trans ?_
    gcongr
    exact le_max_left _ _
  · refine (h2 hR hd hi hd1 hw).trans ?_
    gcongr
    exact le_max_left _ _

/-- The normalized map at `(z, r)` and its basic properties on `B_{s/r}(0)`. -/
theorem normalized_props {φ : ℂ → ℂ} {z : ℂ} {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (hd : DifferentiableOn ℂ φ (ball z s)) (hinj : InjOn φ (ball z s)) :
    let F : ℂ → ℂ := fun w => (φ (z + (r : ℂ) * w) - φ z) / ((r : ℂ) * deriv φ z)
    deriv φ z ≠ 0 ∧ (∀ w ∈ ball (0 : ℂ) (s / r), z + (r : ℂ) * w ∈ ball z s) ∧
      DifferentiableOn ℂ F (ball 0 (s / r)) ∧ InjOn F (ball 0 (s / r)) ∧ F 0 = 0 ∧
      deriv F 0 = 1 ∧
      (∀ w ∈ ball (0 : ℂ) (s / r), deriv F w = deriv φ (z + (r : ℂ) * w) / deriv φ z) := by
  intro F
  have hφderiv : deriv φ z ≠ 0 :=
    QuantumZipper.CA.Koebe.deriv_ne_zero_of_injOn isOpen_ball hd hinj (mem_ball_self hs)
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hden : (r : ℂ) * deriv φ z ≠ 0 := mul_ne_zero hrC hφderiv
  have hinto : ∀ w ∈ ball (0 : ℂ) (s / r), z + (r : ℂ) * w ∈ ball z s := by
    intro w hw
    have hwr : ‖w‖ < s / r := by simpa only [mem_ball, dist_zero_right] using hw
    have htw : r * ‖w‖ < s := by simpa only [mul_comm] using (lt_div_iff₀ hr).mp hwr
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
    exact htw
  have hderivAt : ∀ w ∈ ball (0 : ℂ) (s / r),
      HasDerivAt F (deriv φ (z + (r : ℂ) * w) / deriv φ z) w := by
    intro w hw
    have hφ : HasDerivAt φ (deriv φ (z + (r : ℂ) * w)) (z + (r : ℂ) * w) :=
      ((hd.differentiableAt (isOpen_ball.mem_nhds (hinto w hw)))).hasDerivAt
    have harg : HasDerivAt (fun v : ℂ => z + (r : ℂ) * v) (r : ℂ) w :=
      (hasDerivAt_const_mul (r : ℂ)).const_add z
    have hcomp := (hφ.comp w harg).sub_const (φ z) |>.div_const ((r : ℂ) * deriv φ z)
    have heq : deriv φ (z + (r : ℂ) * w) / deriv φ z =
        deriv φ (z + (r : ℂ) * w) * (r : ℂ) / ((r : ℂ) * deriv φ z) := by
      rw [mul_comm (r : ℂ) (deriv φ z), mul_div_mul_right _ _ hrC]
    rw [heq]
    exact hcomp
  refine ⟨hφderiv, hinto, fun w hw => (hderivAt w hw).differentiableAt.differentiableWithinAt,
    ?_, ?_, ?_, fun w hw => (hderivAt w hw).deriv⟩
  · intro x hx y hy hxy
    have hnum : φ (z + (r : ℂ) * x) - φ z = φ (z + (r : ℂ) * y) - φ z :=
      (div_left_inj' hden).mp hxy
    have harg := hinj (hinto x hx) (hinto y hy) (sub_left_inj.mp hnum)
    exact mul_left_cancel₀ hrC (add_left_cancel harg)
  · simp only [F, mul_zero, add_zero, sub_self, zero_div]
  · rw [(hderivAt 0 (mem_ball_self (div_pos hs hr))).deriv]
    simp only [mul_zero, add_zero]
    exact div_self hφderiv

/-- The normalized inverse on the Koebe disk `B_{κR}(0)`: it is normalized univalent there. -/
theorem normalized_inverse_props {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ F (ball 0 R)) (hinj : InjOn F (ball 0 R)) (hzero : F 0 = 0)
    (hderiv : deriv F 0 = 1) :
    let g := Function.invFunOn F (ball 0 R)
    let ρ := QuantumZipper.CA.Koebe.koebeCovConst * R
    ball 0 ρ ⊆ F '' ball 0 R ∧ DifferentiableOn ℂ g (ball 0 ρ) ∧ InjOn g (ball 0 ρ) ∧
      g 0 = 0 ∧ deriv g 0 = 1 ∧ (∀ w ∈ ball (0 : ℂ) ρ, g w ∈ ball 0 R ∧ F (g w) = w) := by
  intro g ρ
  have hcover : ball 0 ρ ⊆ F '' ball 0 R := by
    have h := QuantumZipper.CA.Koebe.ball_subset_image_koebe hd hinj
    simpa only [hzero, hderiv, norm_one, mul_one] using h
  refine ⟨hcover, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨z, hz, rfl⟩ := hcover hw
    exact (QuantumZipper.CA.Koebe.hasDerivAt_invFunOn_of_injOn
      isOpen_ball hd hinj hz).differentiableAt.differentiableWithinAt
  · exact (Function.invFunOn_injOn_image F (ball 0 R)).mono hcover
  · have hz : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
    have hx : ∃ z ∈ ball 0 R, F z = 0 := ⟨0, hz, hzero⟩
    exact hinj (Function.invFunOn_mem hx) hz ((Function.invFunOn_eq hx).trans hzero.symm)
  · have hz : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
    have h := QuantumZipper.CA.Koebe.hasDerivAt_invFunOn_of_injOn isOpen_ball hd hinj hz
    rw [hzero, hderiv] at h
    simpa only [inv_one] using h.deriv
  · intro w hw
    obtain ⟨z, hz, rfl⟩ := hcover hw
    have hx : ∃ z' ∈ ball 0 R, F z' = F z := ⟨z, hz, rfl⟩
    exact ⟨Function.invFunOn_mem hx, Function.invFunOn_eq hx⟩

theorem aux_koebe_le {C κ ε R : ℝ} (hC : 0 < C) (hκ : 0 < κ) (hε : 0 < ε)
    (h : 9 * C / κ * (1 + 1 / ε) ≤ R) : 9 * C ≤ ε * (κ * R) ∧ 9 * C ≤ κ * R := by
  have e : 9 * C / κ * (1 + 1 / ε) = 9 * C * (ε + 1) / (κ * ε) := by field_simp
  rw [e, div_le_iff₀ (mul_pos hκ hε)] at h
  have h1 : 9 * C ≤ R * (κ * ε) := by nlinarith
  have h2 : 9 * C * ε ≤ R * (κ * ε) := by nlinarith
  refine ⟨by nlinarith, ?_⟩
  have : 9 * C * ε ≤ (κ * R) * ε := by nlinarith
  exact le_of_mul_le_mul_right this hε

theorem aux_deriv_le {C ε R : ℝ} (hC : 0 < C) (hε : 0 < ε)
    (h : 8 * C * (1 + 1 / ε) ≤ R) : 8 * C ≤ R ∧ 8 * C ≤ ε * R := by
  have e : 8 * C * (1 + 1 / ε) = 8 * C * (ε + 1) / ε := by field_simp
  rw [e, div_le_iff₀ hε] at h
  constructor
  · have : 8 * C * ε ≤ R * ε := by nlinarith
    exact le_of_mul_le_mul_right this hε
  · nlinarith

theorem inv_sub_one_le {q : ℂ} {ε : ℝ} (h1 : ‖q - 1‖ ≤ 1 / 2) (h2 : ‖q - 1‖ ≤ ε / 2) :
    ‖q⁻¹ - 1‖ ≤ ε := by
  have hqn : 1 / 2 ≤ ‖q‖ := by
    have h := norm_sub_norm_le (1 : ℂ) q
    rw [norm_one, norm_sub_rev] at h
    linarith
  have hq0 : q ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hqn; linarith
  have hid : q⁻¹ - 1 = (1 - q) / q := by field_simp
  have hε : 0 ≤ ε := by linarith [norm_nonneg (q - 1)]
  rw [hid, norm_div, norm_sub_rev, div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg hε (sub_nonneg.2 hqn)]

theorem geom_forward_conv {φ : ℂ → ℂ} {z x : ℂ} {r ε : ℝ} (hrC : (r : ℂ) ≠ 0)
    (hφd : deriv φ z ≠ 0)
    (hb : ‖(φ (z + (r : ℂ) * ((x - z) / (r : ℂ))) - φ z) / ((r : ℂ) * deriv φ z) -
      (x - z) / (r : ℂ)‖ ≤ ε) :
    ‖φ x - φ z - deriv φ z * (x - z)‖ ≤ ε * (‖(r : ℂ)‖ * ‖deriv φ z‖) := by
  have hx : z + (r : ℂ) * ((x - z) / (r : ℂ)) = x := by field_simp; ring
  rw [hx] at hb
  have hid : φ x - φ z - deriv φ z * (x - z) =
      ((r : ℂ) * deriv φ z) * ((φ x - φ z) / ((r : ℂ) * deriv φ z) - (x - z) / (r : ℂ)) := by
    field_simp
  rw [hid, norm_mul, norm_mul]
  have := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ ‖(r : ℂ)‖ * ‖deriv φ z‖)
  linarith

theorem geom_inverse_eq {φ : ℂ → ℂ} {z y w' : ℂ} {r : ℝ} (hden : (r : ℂ) * deriv φ z ≠ 0)
    (hF : (φ (z + (r : ℂ) * w') - φ z) / ((r : ℂ) * deriv φ z) =
      (y - φ z) / ((r : ℂ) * deriv φ z)) : φ (z + (r : ℂ) * w') = y := by
  have := (div_left_inj' hden).1 hF
  linear_combination this

theorem geom_inverse_conv {φ : ℂ → ℂ} {z y w' : ℂ} {r ε : ℝ} (hrC : (r : ℂ) ≠ 0)
    (hφd : deriv φ z ≠ 0) (hr : 0 < r)
    (hw : ‖w' - (y - φ z) / ((r : ℂ) * deriv φ z)‖ ≤ ε) :
    ‖z + (r : ℂ) * w' - z - (y - φ z) / deriv φ z‖ ≤ ε * r := by
  have hid : z + (r : ℂ) * w' - z - (y - φ z) / deriv φ z =
      (r : ℂ) * (w' - (y - φ z) / ((r : ℂ) * deriv φ z)) := by
    field_simp
    ring
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  nlinarith [norm_nonneg (w' - (y - φ z) / ((r : ℂ) * deriv φ z))]

/-- **Normalized maps are close to the identity** on `B̄_3(0)` (forward and inverse, with the derivative
ratio), once the univalence radius is large. -/
theorem normalized_close {ε : ℝ} (hε : 0 < ε) : ∃ R₀ : ℝ, 576 ≤ R₀ ∧
    ∀ {F : ℂ → ℂ} {R : ℝ}, R₀ ≤ R → DifferentiableOn ℂ F (ball 0 R) → InjOn F (ball 0 R) →
      F 0 = 0 → deriv F 0 = 1 →
      (∀ w : ℂ, ‖w‖ ≤ 3 → ‖F w - w‖ ≤ ε) ∧
      (∀ w : ℂ, ‖w‖ ≤ 3 → ∃ w' ∈ ball (0 : ℂ) R, ‖w'‖ ≤ 4 ∧ F w' = w ∧ ‖w' - w‖ ≤ ε ∧
        ‖(deriv F w')⁻¹ - 1‖ ≤ ε) := by
  obtain ⟨C, hC1, hmap, hder⟩ := exists_koebe_const
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC1
  have hκ0 : 0 < QuantumZipper.CA.Koebe.koebeCovConst := QuantumZipper.CA.Koebe.koebeCovConst_pos
  have hκ1 : QuantumZipper.CA.Koebe.koebeCovConst = 1 / 48 := rfl
  set κ := QuantumZipper.CA.Koebe.koebeCovConst
  refine ⟨576 + 9 * C / κ * (1 + 1 / ε) + 8 * C * (1 + 1 / ε) + 9 * C / ε, ?_, ?_⟩
  · have : 0 ≤ 9 * C / κ * (1 + 1 / ε) + 8 * C * (1 + 1 / ε) + 9 * C / ε := by positivity
    linarith
  intro F R hR hd hi h0 h1
  have hn1 : 0 ≤ 9 * C / κ * (1 + 1 / ε) := by positivity
  have hn2 : 0 ≤ 8 * C * (1 + 1 / ε) := by positivity
  have hn3 : 0 ≤ 9 * C / ε := by positivity
  have hR576 : 576 ≤ R := by linarith
  have hRpos : 0 < R := by linarith
  have hA : 9 * C / κ * (1 + 1 / ε) ≤ R := by linarith
  have hB : 8 * C * (1 + 1 / ε) ≤ R := by linarith
  have hD : 9 * C / ε ≤ R := by linarith
  have hD' : 9 * C ≤ ε * R := by rw [div_le_iff₀ hε] at hD; linarith
  obtain ⟨hk1, hk2⟩ := aux_koebe_le hC0 hκ0 hε hA
  obtain ⟨hd1, hd2⟩ := aux_deriv_le hC0 hε hB
  constructor
  · intro w hw
    have hwR : ‖w‖ ≤ R / 4 := le_trans hw (by linarith)
    have hw9 : ‖w‖ ^ 2 ≤ 9 := by nlinarith [norm_nonneg w]
    have hw2 : C * ‖w‖ ^ 2 ≤ 9 * C := by
      have := mul_le_mul_of_nonneg_left hw9 hC0.le; linarith
    refine (hmap hRpos hd hi h0 h1 hwR).trans ?_
    rw [div_le_iff₀ hRpos]; linarith
  · intro w hw
    obtain ⟨hcover, hgd, hgi, hg0, hg1, hgF⟩ := normalized_inverse_props hRpos hd hi h0 h1
    have hκRpos : 0 < κ * R := mul_pos hκ0 hRpos
    have hwb : w ∈ ball (0 : ℂ) (κ * R) := by
      rw [mem_ball, dist_zero_right]; rw [hκ1]; linarith
    have hκR4 : ‖w‖ ≤ κ * R / 4 := by rw [hκ1]; linarith
    obtain ⟨hgw, hFgw⟩ := hgF w hwb
    have hgb := hmap hκRpos hgd hgi hg0 hg1 hκR4
    have hw9 : ‖w‖ ^ 2 ≤ 9 := by nlinarith [norm_nonneg w]
    have hw2 : C * ‖w‖ ^ 2 ≤ 9 * C := by
      have := mul_le_mul_of_nonneg_left hw9 hC0.le; linarith
    set w' := Function.invFunOn F (ball 0 R) w with hw'
    have hgε : ‖w' - w‖ ≤ ε := by
      refine hgb.trans ?_; rw [div_le_iff₀ hκRpos]; linarith
    have hg1' : ‖w' - w‖ ≤ 1 := by
      refine hgb.trans ?_; rw [div_le_iff₀ hκRpos]; linarith
    have hw'n : ‖w'‖ ≤ 4 := by
      have : ‖w'‖ ≤ ‖w‖ + ‖w' - w‖ := by
        calc ‖w'‖ = ‖w + (w' - w)‖ := by ring_nf
          _ ≤ ‖w‖ + ‖w' - w‖ := norm_add_le _ _
      linarith
    refine ⟨w', hgw, hw'n, hFgw, hgε, ?_⟩
    have hw'R : ‖w'‖ ≤ R / 4 := le_trans hw'n (by linarith)
    have hdF := hder hRpos hd hi h1 hw'R
    have hb4 : C * ‖w'‖ / R ≤ 4 * C / R := by
      apply div_le_div_of_nonneg_right _ hRpos.le
      nlinarith
    have hq1 : ‖deriv F w' - 1‖ ≤ 1 / 2 := by
      refine hdF.trans (hb4.trans ?_); rw [div_le_iff₀ hRpos]; linarith
    have hq2 : ‖deriv F w' - 1‖ ≤ ε / 2 := by
      refine hdF.trans (hb4.trans ?_); rw [div_le_iff₀ hRpos]; linarith
    exact inv_sub_one_le hq1 hq2

/-- **The geometry at one centre**: for every `ε > 0` there is `c₀ > 0` such that `φ` univalent on
`B_s(z) ⊆ U` and `0 < r ≤ c₀ s` give `GeomGood φ U z r ε`. -/
theorem geomGood_of_ball {ε : ℝ} (hε : 0 < ε) : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {φ : ℂ → ℂ} {U : Set ℂ} {z : ℂ} {s r : ℝ}, 0 < s → ball z s ⊆ U →
      DifferentiableOn ℂ φ (ball z s) → InjOn φ (ball z s) → 0 < r → r ≤ c₀ * s →
      GeomGood φ U z r ε := by
  obtain ⟨R₀, hR₀, hN⟩ := normalized_close hε
  have hR₀pos : 0 < R₀ := by linarith
  refine ⟨1 / R₀, by positivity, ?_⟩
  intro φ U z s r hs hsU hd hinj hr hrs
  have hRge : R₀ ≤ s / r := by
    rw [le_div_iff₀ hr]
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hR₀pos] at hrs
    linarith
  obtain ⟨hφd, hinto, hFd, hFi, hF0, hF1, hFder⟩ := normalized_props hs hr hd hinj
  obtain ⟨hfwd, hinv⟩ := hN hRge hFd hFi hF0 hF1
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hrn : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hden : (r : ℂ) * deriv φ z ≠ 0 := mul_ne_zero hrC hφd
  have hφdn : 0 < ‖deriv φ z‖ := norm_pos_iff.2 hφd
  have h4rs : 4 * r < s := by
    have h4 : 4 < s / r := by linarith
    rw [lt_div_iff₀ hr] at h4
    linarith
  refine ⟨hr, hφd, (closedBall_subset_ball h4rs).trans hsU, ?_, ?_⟩
  · intro x hx
    have hwn : ‖(x - z) / (r : ℂ)‖ ≤ 3 := by
      rw [norm_div, hrn, div_le_iff₀ hr]
      have := mem_closedBall.1 hx
      rw [dist_eq_norm] at this
      linarith
    have hb := hfwd _ hwn
    have := geom_forward_conv hrC hφd hb
    rwa [hrn] at this
  · intro y hy
    have hwn : ‖(y - φ z) / ((r : ℂ) * deriv φ z)‖ ≤ 3 := by
      rw [norm_div, norm_mul, hrn, div_le_iff₀ (by positivity)]
      have := mem_closedBall.1 hy
      rw [dist_eq_norm] at this
      linarith
    obtain ⟨w', hw'b, hw'n, hFw', hw'ε, hdw'⟩ := hinv _ hwn
    refine ⟨z + (r : ℂ) * w', ?_, ?_, ?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, hrn]
      nlinarith
    · exact geom_inverse_eq hden hFw'
    · exact geom_inverse_conv hrC hφd hr hw'ε
    · rw [hFder w' hw'b] at hdw'
      rwa [inv_div] at hdw'

/-- **Uniform geometry on a compact set**: for `φ` univalent on the open `U` and a compact `L ⊆ U`, for
every `ε > 0` there is `r₁ > 0` with `GeomGood φ U z r ε` for all `z ∈ cl B_{r₁}(L)` and `r ∈ (0, r₁]`. -/
theorem geomGood_on_compact {φ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hd : DifferentiableOn ℂ φ U) (hinj : InjOn φ U) {L : Set ℂ} (hL : IsCompact L)
    (hLU : L ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ z ∈ cthickening r₁ L, ∀ r ∈ Ioc (0 : ℝ) r₁, GeomGood φ U z r ε := by
  obtain ⟨c₀, hc₀, hgeom⟩ := geomGood_of_ball hε
  obtain ⟨ρ, hρ, hρU⟩ := hL.exists_cthickening_subset_open hU hLU
  refine ⟨min (ρ / 2) (c₀ * (ρ / 2)), lt_min (by positivity) (by positivity), ?_⟩
  intro z hz r hr
  have hzρ : z ∈ cthickening (ρ / 2) L := cthickening_mono (min_le_left _ _) L hz
  have hball : ball z (ρ / 2) ⊆ U := by
    refine (ball_subset_closedBall.trans
      (closedBall_subset_cthickening hzρ (ρ / 2))).trans ?_
    refine (cthickening_cthickening_subset (by positivity) (by positivity) L).trans ?_
    rw [show ρ / 2 + ρ / 2 = ρ by ring]
    exact hρU
  exact hgeom (by positivity) hball (hd.mono hball) (hinj.mono hball) hr.1
    (hr.2.trans (min_le_right _ _))

end SupercriticalConformalCovariance.BiLip
