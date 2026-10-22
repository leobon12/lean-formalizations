import HigherDimLQGContinuity.Lemma21.Unit
import HigherDimLQGContinuity.Norm.ScalingSets
import HigherDimLQGContinuity.Norm.PinGauss
import HigherDimLQGContinuity.ConvTransfer.Moments
import GaussianLQG.LQG.Localization.Tail
import HigherDimLQGContinuity.Events.RefsProb

/-!
# Transfer of Lemma 2.1 from the unit pin to a positive pin (packet L4)

The radius-one recentered field has the normalized law under every positive
pin. Exact scaling multiplies each metric by one positive Gaussian factor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

/-- The radius-one recentered field has the normalized law under any positive pin. -/
theorem l4_pin_unitLaw {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s) :
    (pinLaw d s).map (recentre 1 1 (0 : Rd d)) = normLGFLaw d := by
  simpa only [pinLaw_one hd] using
    recentre_law hd (s := 1) (s₀ := s) (r := 1) one_pos hs one_pos (0 : Rd d)

/-- The associated identity for lower integrals of a.e.-measurable observables. -/
theorem l4_pin_lintegral_unitLaw {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s)
    (f : DistRd d → ℝ≥0∞) (hf : AEMeasurable f (normLGFLaw d)) :
    (∫⁻ g, f (recentre 1 1 (0 : Rd d) g) ∂(pinLaw d s)) =
      ∫⁻ g, f g ∂(normLGFLaw d) := by
  have hf' : AEMeasurable f ((pinLaw d s).map (recentre 1 1 (0 : Rd d))) := by
    rwa [l4_pin_unitLaw hd hs]
  calc
    (∫⁻ g, f (recentre 1 1 (0 : Rd d) g) ∂(pinLaw d s)) =
        ∫⁻ g, f g ∂((pinLaw d s).map (recentre 1 1 (0 : Rd d))) :=
          (lintegral_map' hf' (measurable_recentre 1 1 0).aemeasurable).symm
    _ = ∫⁻ g, f g ∂(normLGFLaw d) := by rw [l4_pin_unitLaw hd hs]

/-- At physical scale one, the random factor is `exp(ξ g₁(0))`. -/
theorem l4_scaleS_one {d : ℕ} (ξ : ℝ) (g : DistRd d) :
    scaleS d ξ 1 1 (0 : Rd d) g = Real.exp (ξ * sphereAvg g 1 0) := by
  simp only [scaleS, Real.one_rpow, one_mul]

/-- Both the factor and its reciprocal are bounded by the same Gaussian envelope. -/
theorem l4_pin_factor_bound {d : ℕ} {b ξ : ℝ} (hξ : 0 ≤ ξ) (hξb : ξ ≤ b)
    (g : DistRd d) :
    scaleS d ξ 1 1 (0 : Rd d) g ≤ Real.exp (b * |sphereAvg g 1 0|) ∧
      (scaleS d ξ 1 1 (0 : Rd d) g)⁻¹ ≤ Real.exp (b * |sphereAvg g 1 0|) := by
  let z := sphereAvg g 1 0
  have hz : -|z| ≤ z ∧ z ≤ |z| := abs_le.mp le_rfl
  have hmain : ξ * z ≤ b * |z| := by
    calc ξ * z ≤ ξ * |z| := mul_le_mul_of_nonneg_left hz.2 hξ
      _ ≤ b * |z| := mul_le_mul_of_nonneg_right hξb (abs_nonneg _)
  have hneg : -(ξ * z) ≤ b * |z| := by
    calc -(ξ * z) = ξ * (-z) := by ring
      _ ≤ ξ * |z| := mul_le_mul_of_nonneg_left (by linarith [hz.1]) hξ
      _ ≤ b * |z| := mul_le_mul_of_nonneg_right hξb (abs_nonneg _)
  constructor
  · rw [l4_scaleS_one]
    exact Real.exp_le_exp.mpr hmain
  · rw [l4_scaleS_one, ← Real.exp_neg]
    exact Real.exp_le_exp.mpr hneg

/-- The Gaussian envelope has a finite moment of every positive order under a fixed pin. -/
theorem l4_pin_gauss_moment {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s)
    (b q : ℝ) (hq : 0 ≤ q) :
    ∃ G : ℝ, 0 < G ∧
      (∫⁻ g, (ENNReal.ofReal (Real.exp (b * |sphereAvg g 1 0|))) ^ q
        ∂(pinLaw d s)) ≤ ENNReal.ofReal G := by
  haveI : IsProbabilityMeasure (pinLaw d s) := isProbabilityMeasure_pinLaw hd s
  obtain ⟨hG, hmean⟩ := hasGaussianLaw_sphereAvg_pinLaw hd hs one_pos 0
  let V : ℝ := Var[fun g : DistRd d => sphereAvg g 1 0; pinLaw d s]
  obtain hbound := convEnv_lintegral_exp_abs_gauss hG hmean (le_refl V) (q * b)
  refine ⟨2 * Real.exp (V * (q * b) ^ 2 / 2), by positivity, ?_⟩
  have heq (g : DistRd d) :
      (ENNReal.ofReal (Real.exp (b * |sphereAvg g 1 0|))) ^ q =
        ENNReal.ofReal (Real.exp ((q * b) * |sphereAvg g 1 0|)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hq]
    rw [← Real.exp_mul]
    congr 1
    ring_nf
  simp_rw [heq]
  exact hbound

/-- Cauchy–Schwarz transfers any nonnegative homogeneous observable from the unit law.
The same lemma is used for envelopes, crossings, and buffered diameters. -/
theorem l4_pin_product_moment {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s)
    (b : ℝ) {q : ℝ} (hq : 0 ≤ q)
    (f : DistRd d → ℝ≥0∞) (hf : AEMeasurable f (normLGFLaw d))
    {G : ℝ} (hG0 : 0 < G)
    (hG : (∫⁻ g, (ENNReal.ofReal (Real.exp (b * |sphereAvg g 1 0|))) ^ (2 * q)
      ∂(pinLaw d s)) ≤ ENNReal.ofReal G)
    {M : ℝ} (hM : ∫⁻ g, f g ^ (2 * q) ∂(normLGFLaw d) ≤ ENNReal.ofReal M) :
    (∫⁻ g, (ENNReal.ofReal (Real.exp (b * |sphereAvg g 1 0|)) *
        f (recentre 1 1 (0 : Rd d) g)) ^ q ∂(pinLaw d s)) ≤
      ENNReal.ofReal (G ^ (1 / 2 : ℝ) * (max 0 M) ^ (1 / 2 : ℝ)) := by
  let μs := pinLaw d s
  let a : DistRd d → ℝ≥0∞ := fun g =>
    ENNReal.ofReal (Real.exp (b * |sphereAvg g 1 0|))
  let f' : DistRd d → ℝ≥0∞ := fun g => f (recentre 1 1 (0 : Rd d) g)
  have hfm : AEMeasurable f' μs := by
    have hf' : AEMeasurable f (μs.map (recentre 1 1 (0 : Rd d))) := by
      rwa [l4_pin_unitLaw hd hs]
    exact hf'.comp_measurable (measurable_recentre 1 1 0)
  have ham : AEMeasurable a μs := by
    dsimp [a, μs]
    exact (ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp
        (measurable_const.mul (measurable_sphereAvg_left 1 0).abs))).aemeasurable
  have hf'mom : (∫⁻ g, f' g ^ (2 * q) ∂μs) ≤ ENNReal.ofReal M := by
    simpa only [f', μs] using (l4_pin_lintegral_unitLaw hd hs
      (fun g => f g ^ (2 * q)) (hf.pow_const _)).le.trans hM
  let C : ℝ := G ^ (1 / 2 : ℝ) * (max 0 M) ^ (1 / 2 : ℝ)
  have hCS := GaussianLQG.lintegral_rpow_mul_rpow_le ham hfm (q := q)
  have hpoint (g : DistRd d) : (a g * f' g) ^ q = a g ^ q * f' g ^ q :=
    ENNReal.mul_rpow_of_nonneg _ _ hq
  have hM' : ENNReal.ofReal M ≤ ENNReal.ofReal (max 0 M) :=
    ENNReal.ofReal_le_ofReal (le_max_right 0 M)
  have hfin :
      (ENNReal.ofReal G) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal (max 0 M)) ^ (1 / 2 : ℝ) = ENNReal.ofReal C := by
    dsimp [C]
    rw [ENNReal.ofReal_rpow_of_nonneg hG0.le (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.ofReal_rpow_of_nonneg (le_max_left 0 M) (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.ofReal_mul (Real.rpow_nonneg hG0.le _)]
  change (∫⁻ g, (a g * f' g) ^ q ∂μs) ≤ ENNReal.ofReal C
  calc
    (∫⁻ g, (ENNReal.ofReal (Real.exp (b * |sphereAvg g 1 0|)) *
        f (recentre 1 1 (0 : Rd d) g)) ^ q ∂(pinLaw d s)) =
        ∫⁻ g, a g ^ q * f' g ^ q ∂μs := by simp only [a, f', μs, hpoint]
    _ ≤ (∫⁻ g, a g ^ (2 * q) ∂μs) ^ (1 / 2 : ℝ) *
          (∫⁻ g, f' g ^ (2 * q) ∂μs) ^ (1 / 2 : ℝ) := hCS
    _ ≤ (ENNReal.ofReal G) ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal (max 0 M)) ^ (1 / 2 : ℝ) := by
            apply mul_le_mul
            · exact ENNReal.rpow_le_rpow hG (by norm_num)
            · exact ENNReal.rpow_le_rpow (hf'mom.trans hM') (by norm_num)
            · exact bot_le
            · exact bot_le
    _ = ENNReal.ofReal C := hfin

/-- At scale one, set distances and internal diameters are multiplied by the
same positive factor after recentring. -/
theorem l4_pin_set_scaling {d : ℕ} (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ)
    {D : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    {s : ℝ} (hs : 0 < s) :
    ∀ᵐ g ∂(pinLaw d s),
      (∀ V A B : Set (Rd d),
        setDistIn (rho D g) V A B =
          ENNReal.ofReal (Real.exp (ξ * sphereAvg g 1 0)) *
            setDistIn (rho D (recentre 1 1 0 g)) V A B) ∧
      (∀ V A : Set (Rd d),
        diamIn (rho D g) V A =
          ENNReal.ofReal (Real.exp (ξ * sphereAvg g 1 0)) *
            diamIn (rho D (recentre 1 1 0 g)) V A) := by
  filter_upwards [rho_scaling_sets hd hξ hD (s := 1) (s₀ := s) (r := 1)
    hs one_pos (0 : Rd d)] with g hg
  have hΦ : (fun w : Rd d => (1 : ℝ) • w + 0) = id := by funext w; simp
  simpa only [hΦ, image_id, l4_scaleS_one] using hg

/-- The same scale-one identity for point distances. -/
theorem l4_pin_point_scaling {d : ℕ} (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ)
    {D : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    {s : ℝ} (hs : 0 < s) :
    ∀ᵐ g ∂(pinLaw d s), ∀ x y : Rd d,
      (rho D g).1 (x, y) =
        Real.exp (ξ * sphereAvg g 1 0) *
          (rho D (recentre 1 1 (0 : Rd d) g)).1 (x, y) := by
  filter_upwards [rho_scaling hd hξ hD one_pos hs one_pos (0 : Rd d)] with g hg x y
  simpa only [one_smul, add_zero, l4_scaleS_one] using hg.1 x y

/-- A unit-pin Hölder envelope transfers with half its moment order. -/
theorem l4_pin_envelope {d : ℕ} (hd : 3 ≤ d) {s : ℝ} (hs : 0 < s)
    {b ξbar : ℝ} (_hb : 0 < b)
    (hwin : ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ξ ≤ b)
    (hU : UniformEstimates d ξbar 1) :
    ∃ p σ β C A : ℝ, 0 < p ∧ 0 < σ ∧ σ < 1 ∧ 1 < β ∧ 0 < C ∧ 0 ≤ A ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξbar,
        ∀ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D →
          HolderEnvelope (pinLaw d s) (rho D) p σ β C A := by
  have hd2 : 2 ≤ d := by omega
  obtain ⟨p0, σ, β, C0, A0, hp0, hσ, hσ1, hβ, hC0, hA0, henv⟩ := hU.envelope
  obtain ⟨G, hG0, hG⟩ := l4_pin_gauss_moment hd2 hs b p0 hp0.le
  let p : ℝ := p0 / 2
  let C : ℝ := G ^ (1 / 2 : ℝ) * C0 ^ (1 / 2 : ℝ)
  let A : ℝ := A0 / 2
  have hp : 0 < p := by dsimp [p]; linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hA : 0 ≤ A := by dsimp [A]; linarith
  refine ⟨p, σ, β, C, A, hp, hσ, hσ1, hβ, hC, hA,
    fun ξ hξ D hD R hR => ?_⟩
  obtain ⟨H1, hH1m, hH11, hH1mom, hH1pt⟩ := henv ξ hξ D hD R hR
  let F : DistRd d → ℝ := fun g => Real.exp (b * |sphereAvg g 1 0|)
  let H : DistRd d → ℝ := fun g => F g * H1 (recentre 1 1 0 g)
  have hFm : Measurable F := by
    dsimp [F]
    exact Real.measurable_exp.comp
      (measurable_const.mul (measurable_sphereAvg_left 1 0).abs)
  have hF1 : ∀ g, 1 ≤ F g := by
    intro g
    dsimp [F]
    exact Real.one_le_exp (mul_nonneg (le_trans hξ.1.le (hwin ξ hξ)) (abs_nonneg _))
  have hHm : Measurable H := hFm.mul (hH1m.comp (measurable_recentre 1 1 0))
  have hH1 : ∀ g, 1 ≤ H g := fun g => by
    dsimp [H]
    exact one_le_mul_of_one_le_of_one_le (hF1 g) (hH11 _)
  refine ⟨H, hHm, hH1, ?_, ?_⟩
  · have hMpos : 0 ≤ C0 * (1 + R) ^ A0 :=
      mul_nonneg hC0.le (Real.rpow_nonneg (by linarith) _)
    have htwo : 2 * p = p0 := by dsimp [p]; ring
    have hG' : (∫⁻ g, (ENNReal.ofReal (Real.exp (b * |sphereAvg g 1 0|))) ^ (2 * p)
        ∂(pinLaw d s)) ≤ ENNReal.ofReal G := by simpa only [htwo] using hG
    have hM' : (∫⁻ g, (ENNReal.ofReal (H1 g)) ^ (2 * p)
        ∂(normLGFLaw d)) ≤ ENNReal.ofReal (C0 * (1 + R) ^ A0) := by
      rw [htwo]
      calc
        (∫⁻ g, (ENNReal.ofReal (H1 g)) ^ p0 ∂(normLGFLaw d)) =
            ∫⁻ g, ENNReal.ofReal (H1 g ^ p0) ∂(normLGFLaw d) := by
              apply lintegral_congr
              intro g
              exact ENNReal.ofReal_rpow_of_nonneg (by linarith [hH11 g]) hp0.le
        _ ≤ _ := by simpa only [pinLaw_one hd2] using hH1mom
    have hprod := l4_pin_product_moment hd2 hs b (by dsimp [p]; linarith : 0 ≤ p)
      (fun g => ENNReal.ofReal (H1 g))
      (ENNReal.measurable_ofReal.comp hH1m).aemeasurable hG0 hG'
      (M := C0 * (1 + R) ^ A0) hM'
    have hconstant :
        G ^ (1 / 2 : ℝ) * (max 0 (C0 * (1 + R) ^ A0)) ^ (1 / 2 : ℝ) =
          C * (1 + R) ^ A := by
      rw [max_eq_right hMpos, Real.mul_rpow hC0.le
        (Real.rpow_nonneg (by linarith : 0 ≤ 1 + R) _)]
      dsimp [C, A]
      rw [show A0 / 2 = A0 * (1 / 2 : ℝ) by ring,
        Real.rpow_mul (by linarith : 0 ≤ 1 + R)]
      ring
    have hpoint (g : DistRd d) :
        ENNReal.ofReal (H g ^ p) =
          (ENNReal.ofReal (F g) *
            ENNReal.ofReal (H1 (recentre 1 1 0 g))) ^ p := by
      rw [← ENNReal.ofReal_rpow_of_nonneg (by linarith [hH1 g]) hp.le,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    simpa only [hpoint, F, hconstant] using hprod
  · have hset := l4_pin_set_scaling hd2 hξ.1 hD hs
    have hpt := l4_pin_point_scaling hd2 hξ.1 hD hs
    have hunit : ∀ᵐ g ∂(pinLaw d s),
        (∀ z ∈ closedBall (0 : Rd d) R, ∀ r ∈ Ioc (0 : ℝ) 1,
          diamIn (rho D (recentre 1 1 0 g)) (ball z (2 * r)) (ball z r) ≤
            ENNReal.ofReal (H1 (recentre 1 1 0 g) * r ^ σ)) ∧
        (∀ x ∈ closedBall (0 : Rd d) R, ∀ y ∈ closedBall (0 : Rd d) R,
          (H1 (recentre 1 1 0 g))⁻¹ * ‖x - y‖ ^ β ≤
            (rho D (recentre 1 1 0 g)).1 (x, y)) := by
      exact ae_recentre_of_ae hd2 one_pos hs one_pos 0
        (by simpa only [pinLaw_one hd2] using hH1pt)
    filter_upwards [hset, hpt, hunit] with g hg hgp hgu
    have ha := l4_pin_factor_bound hξ.1.le (hwin ξ hξ) g
    rw [l4_scaleS_one] at ha
    let a : ℝ := Real.exp (ξ * sphereAvg g 1 0)
    have ha0 : 0 < a := Real.exp_pos _
    have hF0 : 0 < F g := Real.exp_pos _
    have hF_eq : F g = Real.exp (b * |sphereAvg g 1 0|) := rfl
    constructor
    · intro z hz r hr
      rw [hg.2 (ball z (2 * r)) (ball z r)]
      calc
        ENNReal.ofReal a * diamIn (rho D (recentre 1 1 0 g)) (ball z (2 * r)) (ball z r) ≤
            ENNReal.ofReal a * ENNReal.ofReal (H1 (recentre 1 1 0 g) * r ^ σ) := by
              exact mul_le_mul_of_nonneg_left (hgu.1 z hz r hr) bot_le
        _ ≤ ENNReal.ofReal (F g) * ENNReal.ofReal
            (H1 (recentre 1 1 0 g) * r ^ σ) := by
              exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ha.1) bot_le
        _ = ENNReal.ofReal (H g * r ^ σ) := by
              rw [← ENNReal.ofReal_mul hF0.le]
              congr 1
              dsimp [H]
              ring
    · intro x hx y hy
      have hinv : (F g)⁻¹ ≤ a := by
        have h : a⁻¹ ≤ F g := by simpa only [a, F] using ha.2
        have h' : a⁻¹ * a ≤ F g * a := mul_le_mul_of_nonneg_right h ha0.le
        have hFA : 1 ≤ a * F g := by
          calc
            1 = a⁻¹ * a := (inv_mul_cancel₀ ha0.ne').symm
            _ ≤ F g * a := h'
            _ = a * F g := mul_comm _ _
        simpa only [one_div] using (div_le_iff₀ hF0).2 hFA
      have hHinv : (H g)⁻¹ ≤ a * (H1 (recentre 1 1 0 g))⁻¹ := by
        dsimp [H]
        rw [mul_inv_rev]
        rw [mul_comm (H1 (recentre 1 1 0 g))⁻¹ (F g)⁻¹]
        exact mul_le_mul_of_nonneg_right hinv
          (inv_nonneg.mpr (by linarith [hH11 (recentre 1 1 (0 : Rd d) g)]))
      calc
        (H g)⁻¹ * ‖x - y‖ ^ β ≤
            (a * (H1 (recentre 1 1 0 g))⁻¹) * ‖x - y‖ ^ β :=
              mul_le_mul_of_nonneg_right hHinv (Real.rpow_nonneg (norm_nonneg _) _)
        _ = a * ((H1 (recentre 1 1 0 g))⁻¹ * ‖x - y‖ ^ β) := by ring
        _ ≤ a * (rho D (recentre 1 1 0 g)).1 (x, y) :=
              mul_le_mul_of_nonneg_left (hgu.2 x hx y hy) ha0.le
        _ = (rho D g).1 (x, y) := (hgp x y).symm

/-- The pinned inverse crossing moment is finite uniformly over a parameter
window whenever the doubled-order unit crossing moment is. -/
theorem l4_pin_cross {d : ℕ} (hd : 3 ≤ d) {s : ℝ} (hs : 0 < s)
    {b ξbar : ℝ} (_hb : 0 < b)
    (hwin : ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ξ ≤ b)
    (hU : UniformEstimates d ξbar 1)
    (z : Rd d) {a c q : ℝ} (ha : 0 < a) (hac : a < c) (hq : 0 < q) :
    ∃ C : ℝ, ∀ ξ ∈ Ioc (0 : ℝ) ξbar,
      ∀ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D →
        ∫⁻ g, (setDistIn (rho D g) univ (sphere z a) (sphere z c))⁻¹ ^ q
          ∂(pinLaw d s) ≤ ENNReal.ofReal C := by
  have hd2 : 2 ≤ d := by omega
  obtain ⟨M, hM⟩ := hU.cross z a c (2 * q) ha hac (by linarith)
  obtain ⟨G, hG0, hG⟩ := l4_pin_gauss_moment hd2 hs b (2 * q) (by linarith)
  let C : ℝ := G ^ (1 / 2 : ℝ) * (max 0 M) ^ (1 / 2 : ℝ)
  refine ⟨C, fun ξ hξ D hD => ?_⟩
  let f : DistRd d → ℝ≥0∞ := fun g =>
    (setDistIn (rho D g) univ (sphere z a) (sphere z c))⁻¹
  have hlen : ∀ᵐ g ∂(normLGFLaw d), (rho D g).IsLength := by
    simpa only [pinLaw_one hd2] using p5b_ae_isLength_rho hd2 hD one_pos
  have hfm : AEMeasurable f (normLGFLaw d) :=
    (p5b_aemeasurable_setDistIn_univ hD.measurable (normLGFLaw d) hlen
      (sphere z a) (sphere z c)).inv
  have hbound : ∫⁻ g, f g ^ (2 * q) ∂(normLGFLaw d) ≤ ENNReal.ofReal M := by
    simpa only [f, pinLaw_one hd2] using hM ξ hξ D hD
  have hprod := l4_pin_product_moment hd2 hs b (by linarith : 0 ≤ q) f hfm hG0 hG hbound
  have hscale := l4_pin_set_scaling hd2 hξ.1 hD hs
  have hpoint : ∀ᵐ g ∂(pinLaw d s),
      (setDistIn (rho D g) univ (sphere z a) (sphere z c))⁻¹ ^ q ≤
        (ENNReal.ofReal (Real.exp (b * |sphereAvg g 1 0|)) *
          f (recentre 1 1 (0 : Rd d) g)) ^ q := by
    filter_upwards [hscale] with g hg
    have ha0 : ENNReal.ofReal (Real.exp (ξ * sphereAvg g 1 0)) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    have hfactor := (l4_pin_factor_bound hξ.1.le (hwin ξ hξ) g).2
    rw [l4_scaleS_one] at hfactor
    have hinv :
        (setDistIn (rho D g) univ (sphere z a) (sphere z c))⁻¹ =
          (ENNReal.ofReal (Real.exp (ξ * sphereAvg g 1 0)))⁻¹ *
            f (recentre 1 1 (0 : Rd d) g) := by
      rw [hg.1 univ (sphere z a) (sphere z c), ENNReal.mul_inv (Or.inl ha0)
        (Or.inl ENNReal.ofReal_ne_top)]
    rw [hinv]
    apply ENNReal.rpow_le_rpow _ hq.le
    exact mul_le_mul_of_nonneg_right (by
      simpa only [ENNReal.ofReal_inv_of_pos (Real.exp_pos _)] using
        ENNReal.ofReal_le_ofReal hfactor) bot_le
  calc
    (∫⁻ g, (setDistIn (rho D g) univ (sphere z a) (sphere z c))⁻¹ ^ q
      ∂(pinLaw d s)) ≤
        ∫⁻ g, (ENNReal.ofReal (Real.exp (b * |sphereAvg g 1 0|)) *
          f (recentre 1 1 (0 : Rd d) g)) ^ q ∂(pinLaw d s) :=
          lintegral_mono_ae hpoint
    _ ≤ ENNReal.ofReal C := hprod

/-- A positive internal-diameter moment transfers to every positive pin, with half its order. -/
theorem l4_pin_diam {d : ℕ} (hd : 3 ≤ d) {s : ℝ} (hs : 0 < s)
    {b ξbar : ℝ} (_hb : 0 < b)
    (hwin : ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ξ ≤ b)
    (hU : UniformEstimates d ξbar 1) :
    ∃ pplus : ℝ, 0 < pplus ∧
      ∀ U Kc : Set (Rd d), IsOpen U → Bornology.IsBounded U → IsConnected U →
        IsCompact Kc → Kc ⊆ U → ∃ C : ℝ,
      ∀ ξ ∈ Ioc (0 : ℝ) ξbar,
      ∀ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D →
        ∫⁻ g, (diamIn (rho D g) U Kc) ^ pplus
          ∂(pinLaw d s) ≤ ENNReal.ofReal C := by
  have hd2 : 2 ≤ d := by omega
  obtain ⟨p0, hp0, hdiam⟩ := hU.diam
  refine ⟨p0 / 2, by linarith, fun U Kc hUopen hUb hUc hK hKU => ?_⟩
  obtain ⟨M, hM⟩ := hdiam U Kc hUopen hUb hUc hK hKU
  obtain ⟨G, hG0, hG⟩ := l4_pin_gauss_moment hd2 hs b p0 hp0.le
  let C : ℝ := G ^ (1 / 2 : ℝ) * (max 0 M) ^ (1 / 2 : ℝ)
  refine ⟨C, fun ξ hξ D hD => ?_⟩
  let f : DistRd d → ℝ≥0∞ := fun g => diamIn (rho D g) U Kc
  have hlen : ∀ᵐ g ∂(normLGFLaw d), (rho D g).IsLength := by
    simpa only [pinLaw_one hd2] using p5b_ae_isLength_rho hd2 hD one_pos
  have hfm : AEMeasurable f (normLGFLaw d) :=
    aemeasurable_diamIn_of_ae_length (normLGFLaw d) (rho D)
      (measurable_rho hD.measurable) hlen hUopen hKU
  have hbound : ∫⁻ g, f g ^ (2 * (p0 / 2)) ∂(normLGFLaw d) ≤ ENNReal.ofReal M := by
    simpa only [f, pinLaw_one hd2, show 2 * (p0 / 2) = p0 by ring] using hM ξ hξ D hD
  have hprod := l4_pin_product_moment hd2 hs b (by linarith : 0 ≤ p0 / 2)
    f hfm hG0 (by simpa only [show 2 * (p0 / 2) = p0 by ring] using hG) hbound
  have hscale := l4_pin_set_scaling hd2 hξ.1 hD hs
  have hpoint : ∀ᵐ g ∂(pinLaw d s),
      (diamIn (rho D g) U Kc) ^ (p0 / 2) ≤
        (ENNReal.ofReal (Real.exp (b * |sphereAvg g 1 0|)) *
          f (recentre 1 1 (0 : Rd d) g)) ^ (p0 / 2) := by
    filter_upwards [hscale] with g hg
    rw [hg.2 U Kc]
    apply ENNReal.rpow_le_rpow _ (by linarith : 0 ≤ p0 / 2)
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (by
        rw [← l4_scaleS_one ξ g]
        exact (l4_pin_factor_bound hξ.1.le (hwin ξ hξ) g).1)) bot_le
  exact (lintegral_mono_ae hpoint).trans hprod

/-- The relative escape event is invariant under the positive scalar factor
in the pin change, so its probability transfers with the same constants. -/
theorem l4_pin_escape {d : ℕ} (hd : 3 ≤ d) {s : ℝ} (hs : 0 < s)
    {ξbar : ℝ} (hU : UniformEstimates d ξbar 1) :
    ∃ pesc : ℝ, 0 < pesc ∧ ∀ K : ℝ, 1 ≤ K → ∃ CK : ℝ,
      ∀ ξ ∈ Ioc (0 : ℝ) ξbar,
      ∀ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D →
      ∀ R S : ℝ, 1 ≤ R → 4 ≤ S →
        pinLaw d s {g | ¬ (ENNReal.ofReal K *
          diamIn (rho D g) (ball 0 (2 * R)) (ball 0 R) <
          setDistIn (rho D g) univ (sphere 0 (2 * R)) (sphere 0 (S * R)))} ≤
          ENNReal.ofReal (CK * S ^ (-pesc)) := by
  have hd2 : 2 ≤ d := by omega
  obtain ⟨pesc, hpesc, hesc⟩ := hU.escape
  refine ⟨pesc, hpesc, fun K hK => ?_⟩
  obtain ⟨CK, hCK⟩ := hesc K hK
  refine ⟨CK, fun ξ hξ D hD R S hR hS => ?_⟩
  let bad : DistRd d → Prop := fun g =>
    ¬ (ENNReal.ofReal K * diamIn (rho D g) (ball 0 (2 * R)) (ball 0 R) <
      setDistIn (rho D g) univ (sphere 0 (2 * R)) (sphere 0 (S * R)))
  have hevent : {g | bad g} =ᵐ[pinLaw d s]
      {g | bad (recentre 1 1 (0 : Rd d) g)} := by
    filter_upwards [l4_pin_set_scaling hd2 hξ.1 hD hs] with g hg
    have ha0 : ENNReal.ofReal (Real.exp (ξ * sphereAvg g 1 0)) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    have hatop : ENNReal.ofReal (Real.exp (ξ * sphereAvg g 1 0)) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    have hiff :
        (ENNReal.ofReal K * diamIn (rho D g) (ball 0 (2 * R)) (ball 0 R) <
          setDistIn (rho D g) univ (sphere 0 (2 * R)) (sphere 0 (S * R))) ↔
        (ENNReal.ofReal K * diamIn (rho D (recentre 1 1 0 g))
          (ball 0 (2 * R)) (ball 0 R) <
          setDistIn (rho D (recentre 1 1 0 g)) univ
            (sphere 0 (2 * R)) (sphere 0 (S * R))) := by
      rw [hg.2 (ball 0 (2 * R)) (ball 0 R),
        hg.1 univ (sphere 0 (2 * R)) (sphere 0 (S * R))]
      rw [mul_left_comm (ENNReal.ofReal K)]
      constructor
      · intro h
        by_contra hn
        exact (not_lt_of_ge (mul_le_mul_of_nonneg_left (not_lt.mp hn) bot_le)) h
      · intro h
        exact ENNReal.mul_lt_mul_right ha0 hatop h
    exact propext (not_congr hiff)
  calc
    pinLaw d s {g | ¬ (ENNReal.ofReal K *
      diamIn (rho D g) (ball 0 (2 * R)) (ball 0 R) <
      setDistIn (rho D g) univ (sphere 0 (2 * R)) (sphere 0 (S * R)))} =
        pinLaw d s {g | bad (recentre 1 1 (0 : Rd d) g)} := measure_congr hevent
    _ ≤ pinLaw d 1 {g | bad g} := by
      convert pinLaw_preimage_recentre_le hd2 one_pos hs one_pos 0 {g | bad g} using 1
      rfl
    _ ≤ ENNReal.ofReal (CK * S ^ (-pesc)) := hCK ξ hξ D hD R S hR hS

/-- Every fixed absolute moment of the pin-change Gaussian is finite. -/
theorem l4_pin_abs_gauss_moment {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s)
    {q : ℝ} (hq : 0 < q) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∫⁻ g, ENNReal.ofReal (|sphereAvg g 1 0| ^ q) ∂(pinLaw d s)) ≤
        ENNReal.ofReal C := by
  obtain ⟨hG, _⟩ := hasGaussianLaw_sphereAvg_pinLaw hd hs one_pos 0
  have hp0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  have hfin : (∫⁻ g, ENNReal.ofReal (|sphereAvg g 1 0| ^ q)
      ∂(pinLaw d s)) < ⊤ := by
    have hLp := hG.memLp (p := ENNReal.ofReal q) ENNReal.ofReal_ne_top
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0
      ENNReal.ofReal_ne_top hLp.eLpNorm_lt_top
    simpa only [ENNReal.toReal_ofReal hq.le, Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq.le] using h
  refine ⟨(∫⁻ g, ENNReal.ofReal (|sphereAvg g 1 0| ^ q) ∂(pinLaw d s)).toReal,
    ENNReal.toReal_nonneg, ?_⟩
  rw [ENNReal.ofReal_toReal hfin.ne]

/-- Fixed-point logarithmic moments transfer under the radius-one pin change. -/
theorem l4_pin_logMoments {d : ℕ} (hd : 3 ≤ d) {s : ℝ} (hs : 0 < s)
    {b ξbar : ℝ} (_hb : 0 < b)
    (hwin : ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ξ ≤ b)
    (hU : UniformEstimates d ξbar 1)
    (x y : Rd d) (hxy : x ≠ y) {q : ℝ} (hq : 1 ≤ q) :
    ∃ C : ℝ, ∀ ξ ∈ Ioc (0 : ℝ) ξbar,
      ∀ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D →
        ∫⁻ g, ENNReal.ofReal (|Real.log ((rho D g).1 (x, y))| ^ q)
          ∂(pinLaw d s) ≤ ENNReal.ofReal C := by
  have hd2 : 2 ≤ d := by omega
  obtain ⟨M, hM⟩ := hU.logMoments x y hxy q hq
  obtain ⟨G, hG0, hG⟩ := l4_pin_abs_gauss_moment hd2 hs (by linarith : 0 < q)
  let T : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (q - 1)
  let C : ℝ := 2 ^ (q - 1) * (b ^ q * G + max 0 M)
  refine ⟨C, fun ξ hξ D hD => ?_⟩
  let Z : DistRd d → ℝ := fun g => |sphereAvg g 1 0| ^ q
  let Y : DistRd d → ℝ := fun g =>
    |Real.log ((rho D g).1 (x, y))| ^ q
  have hYm : Measurable Y := by
    dsimp [Y]
    exact ((measurable_log_rho_apply hD.measurable (x, y)).abs).pow_const q
  have hYm' : AEMeasurable (fun g => ENNReal.ofReal (Y g)) (normLGFLaw d) :=
    (ENNReal.measurable_ofReal.comp hYm).aemeasurable
  have hY : ∫⁻ g, ENNReal.ofReal (Y (recentre 1 1 0 g)) ∂(pinLaw d s) ≤
      ENNReal.ofReal M := by
    rw [l4_pin_lintegral_unitLaw hd2 hs _ hYm']
    simpa only [Y, pinLaw_one hd2] using hM ξ hξ D hD
  have hZm : Measurable fun g : DistRd d => ENNReal.ofReal (Z g) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_sphereAvg_left 1 0).abs.pow_const q)
  have hpt := l4_pin_point_scaling hd2 hξ.1 hD hs
  have hbound : ∀ᵐ g ∂(pinLaw d s),
      ENNReal.ofReal (|Real.log ((rho D g).1 (x, y))| ^ q) ≤
        T * (ENNReal.ofReal (b ^ q) * ENNReal.ofReal (Z g) +
          ENNReal.ofReal (Y (recentre 1 1 0 g))) := by
    filter_upwards [hpt] with g hg
    have hξ0 : 0 ≤ ξ := hξ.1.le
    have hb0 : 0 ≤ b := hξ0.trans (hwin ξ hξ)
    have hprod :
        Real.log ((rho D g).1 (x, y)) =
          ξ * sphereAvg g 1 0 +
            Real.log ((rho D (recentre 1 1 0 g)).1 (x, y)) := by
      rw [hg x y, Real.log_mul (Real.exp_pos _).ne'
        ((rho D (recentre 1 1 0 g)).apply_pos hxy).ne', Real.log_exp]
    have hξabs : |ξ * sphereAvg g 1 0| ≤ b * |sphereAvg g 1 0| := by
      rw [abs_mul, abs_of_nonneg hξ0]
      exact mul_le_mul_of_nonneg_right (hwin ξ hξ) (abs_nonneg _)
    have hbase : ENNReal.ofReal |Real.log ((rho D g).1 (x, y))| ≤
        ENNReal.ofReal (b * |sphereAvg g 1 0|) +
          ENNReal.ofReal |Real.log ((rho D (recentre 1 1 0 g)).1 (x, y))| := by
      rw [hprod]
      calc
        ENNReal.ofReal |ξ * sphereAvg g 1 0 +
          Real.log ((rho D (recentre 1 1 0 g)).1 (x, y))| ≤
            ENNReal.ofReal (|ξ * sphereAvg g 1 0| +
              |Real.log ((rho D (recentre 1 1 0 g)).1 (x, y))|) :=
                ENNReal.ofReal_le_ofReal (abs_add_le _ _)
        _ = ENNReal.ofReal |ξ * sphereAvg g 1 0| +
            ENNReal.ofReal |Real.log ((rho D (recentre 1 1 0 g)).1 (x, y))| :=
              ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
        _ ≤ _ := by gcongr
    calc
      ENNReal.ofReal (|Real.log ((rho D g).1 (x, y))| ^ q) =
          (ENNReal.ofReal |Real.log ((rho D g).1 (x, y))|) ^ q :=
            (ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by linarith)).symm
      _ ≤ (ENNReal.ofReal (b * |sphereAvg g 1 0|) +
          ENNReal.ofReal |Real.log ((rho D (recentre 1 1 0 g)).1 (x, y))|) ^ q :=
            ENNReal.rpow_le_rpow hbase (by linarith)
      _ ≤ T * ((ENNReal.ofReal (b * |sphereAvg g 1 0|)) ^ q +
          (ENNReal.ofReal |Real.log ((rho D (recentre 1 1 0 g)).1 (x, y))|) ^ q) :=
            ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hq
      _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hb0 (abs_nonneg _))
          (by linarith : 0 ≤ q), Real.mul_rpow hb0 (abs_nonneg _),
          ENNReal.ofReal_mul (Real.rpow_nonneg hb0 _),
          ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by linarith : 0 ≤ q)]

  calc
    (∫⁻ g, ENNReal.ofReal (|Real.log ((rho D g).1 (x, y))| ^ q)
      ∂(pinLaw d s)) ≤
        ∫⁻ g, T * (ENNReal.ofReal (b ^ q) * ENNReal.ofReal (Z g) +
          ENNReal.ofReal (Y (recentre 1 1 0 g))) ∂(pinLaw d s) :=
            lintegral_mono_ae hbound
    _ = T * (ENNReal.ofReal (b ^ q) *
          ∫⁻ g, ENNReal.ofReal (Z g) ∂(pinLaw d s) +
          ∫⁻ g, ENNReal.ofReal (Y (recentre 1 1 0 g)) ∂(pinLaw d s)) := by
            have hTfin : T ≠ ⊤ := by
              dsimp [T]
              exact ENNReal.rpow_ne_top_of_nonneg (by linarith : 0 ≤ q - 1)
                (by norm_num)
            rw [lintegral_const_mul' T _ hTfin,
              lintegral_add_left (hZm.const_mul _),
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ T * (ENNReal.ofReal (b ^ q) * ENNReal.ofReal G +
          ENNReal.ofReal (max 0 M)) := by
            apply mul_le_mul_of_nonneg_left _ bot_le
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left (by simpa only [Z] using hG) bot_le
            · exact hY.trans (ENNReal.ofReal_le_ofReal (le_max_right 0 M))
    _ = ENNReal.ofReal C := by
          dsimp [C, T]
          rw [show (2 : ℝ≥0∞) ^ (q - 1) =
              ENNReal.ofReal ((2 : ℝ) ^ (q - 1)) by
                rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
                norm_num,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith : 0 ≤ b) _),
            ← ENNReal.ofReal_add (by positivity) (le_max_left 0 M),
            ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ (q - 1))]

/-- Assemble all seven estimates at a positive pin from their unit-pin form. -/
theorem l4_pin_estimates {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    {b μ ξbar s : ℝ} (hb : 0 < b) (hs : 0 < s)
    (hwin : ∀ ξ ∈ Ioc (0 : ℝ) ξbar, UHyp d κ b μ ξ)
    (hU : UniformEstimates d ξbar 1) :
    UniformEstimates d ξbar s := by
  have hξb : ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ξ ≤ b := fun ξ hξ => (hwin ξ hξ).le_b
  refine ⟨hU.logIntegrable, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact l4_pin_envelope hd hs hb hξb hU
  · intro z a c q ha hac hq
    exact l4_pin_cross hd hs hb hξb hU z ha hac hq
  · exact l4_pin_diam hd hs hb hξb hU
  · intro x y hxy q hq
    exact l4_pin_logMoments hd hs hb hξb hU x y hxy hq
  · exact l4_pin_escape hd hs hU
  · intro ξ hξ D hD
    exact l4_pinned_proper hd (hwin ξ hξ) hD hs

end HigherDimLQGContinuity
