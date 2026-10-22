import HigherDimLQGContinuity.MarginalEuclid.Unit
import HigherDimLQGContinuity.Lemma21.PinTransfer

/-! Transfer of the Euclidean marginal from the unit pin to the radius-ten pin. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- Scaling a pair function changes its Euclidean error by the scalar error. -/
theorem n5_supDistLU_smul_euclid_le {d : ℕ} {R a : ℝ}
    (hR : 0 ≤ R) (ha : 0 ≤ a) (F : C(Rd d × Rd d, ℝ)) :
    supDistLU d R (a • F) (euclidDistC d) ≤
      ENNReal.ofReal a * supDistLU d R F (euclidDistC d) +
        ENNReal.ofReal (2 * R * |a - 1|) := by
  apply endpt_supDistLU_le_iff.mpr
  intro p hp
  have hx := mem_closedBall_zero_iff.mp hp.1
  have hy := mem_closedBall_zero_iff.mp hp.2
  have hdist : dist p.1 p.2 ≤ 2 * R := by
    have h := norm_sub_le p.1 p.2
    rw [dist_eq_norm]
    linarith
  have heq : a * F p - dist p.1 p.2 =
      a * (F p - dist p.1 p.2) + (a - 1) * dist p.1 p.2 := by ring
  have hreal : |a * F p - dist p.1 p.2| ≤
      a * |F p - dist p.1 p.2| + 2 * R * |a - 1| := by
    rw [heq]
    calc
      |a * (F p - dist p.1 p.2) + (a - 1) * dist p.1 p.2| ≤
          |a * (F p - dist p.1 p.2)| + |(a - 1) * dist p.1 p.2| := abs_add_le _ _
      _ = a * |F p - dist p.1 p.2| + |a - 1| * dist p.1 p.2 := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg (dist_nonneg)]
      _ ≤ a * |F p - dist p.1 p.2| + 2 * R * |a - 1| := by
        nlinarith [mul_le_mul_of_nonneg_left hdist (abs_nonneg (a - 1))]
  rw [edist_dist, Real.dist_eq]
  change ENNReal.ofReal |a * F p - dist p.1 p.2| ≤ _
  calc
    ENNReal.ofReal |a * F p - dist p.1 p.2| ≤
        ENNReal.ofReal (a * |F p - dist p.1 p.2| + 2 * R * |a - 1|) :=
          ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal a * edist (F p) (euclidDistC d p) +
          ENNReal.ofReal (2 * R * |a - 1|) := by
          rw [ENNReal.ofReal_add (mul_nonneg ha (abs_nonneg _))
            (mul_nonneg (by positivity) (abs_nonneg _)),
            ENNReal.ofReal_mul ha]
          simp [edist_dist, Real.dist_eq, euclidDistC]
    _ ≤ ENNReal.ofReal a * supDistLU d R F (euclidDistC d) +
          ENNReal.ofReal (2 * R * |a - 1|) := by
          exact add_le_add (mul_le_mul_right (endpt_edist_le_supDistLU hp) _) le_rfl

/-- A global exponential difference bound convenient for Gaussian pin transfer. -/
theorem n5_abs_exp_sub_one_le (t : ℝ) :
    |Real.exp t - 1| ≤ |t| * Real.exp |t| := by
  by_cases ht : 0 ≤ t
  · have h := Real.add_one_le_exp (-t)
    have hexp := Real.exp_pos t
    have hneg : 0 ≤ Real.exp t - 1 := by
      have := Real.exp_le_exp.mpr ht
      simpa using this
    rw [abs_of_nonneg hneg, abs_of_nonneg ht]
    rw [Real.exp_neg] at h
    have hm := mul_le_mul_of_nonneg_left h hexp.le
    field_simp at hm
    nlinarith
  · have ht' : t ≤ 0 := le_of_not_ge ht
    have h := Real.add_one_le_exp t
    have he : Real.exp t ≤ 1 := by simpa using Real.exp_le_exp.mpr ht'
    rw [abs_of_nonpos (by linarith : Real.exp t - 1 ≤ 0),
      abs_of_nonpos ht']
    have hbig : 1 ≤ Real.exp (-t) := by
      simpa using Real.exp_le_exp.mpr (by linarith : 0 ≤ -t)
    nlinarith [mul_le_mul_of_nonneg_left hbig (by linarith : 0 ≤ -t)]

theorem n5_pin_scalar_bounds {ξ : ℝ} (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (z : ℝ) :
    Real.exp (ξ * z) ≤ Real.exp |z| ∧
      |Real.exp (ξ * z) - 1| ≤ ξ * Real.exp (2 * |z|) := by
  have hz : ξ * z ≤ |z| := by
    calc ξ * z ≤ ξ * |z| := mul_le_mul_of_nonneg_left (le_abs_self z) hξ
      _ ≤ |z| := by nlinarith [abs_nonneg z]
  have habs : |ξ * z| = ξ * |z| := by rw [abs_mul, abs_of_nonneg hξ]
  have hmax : ξ * |z| ≤ |z| := by nlinarith [abs_nonneg z]
  have hbig : |z| ≤ Real.exp |z| := by
    have h := Real.add_one_le_exp |z|
    linarith
  have hsmall : |Real.exp (ξ * z) - 1| ≤ ξ * |z| * Real.exp |z| := by
    calc
      _ ≤ |ξ * z| * Real.exp |ξ * z| := n5_abs_exp_sub_one_le _
      _ = ξ * |z| * Real.exp (ξ * |z|) := by rw [habs]
      _ ≤ ξ * |z| * Real.exp |z| := by
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hmax)
          (mul_nonneg hξ (abs_nonneg _))
  constructor
  · exact Real.exp_le_exp.mpr hz
  · calc
      |Real.exp (ξ * z) - 1| ≤ ξ * |z| * Real.exp |z| := hsmall
      _ ≤ ξ * Real.exp |z| * Real.exp |z| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbig hξ) (Real.exp_pos _).le
      _ = ξ * Real.exp (2 * |z|) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        ring_nf

/-- The radius-ten pin: the unit-pin marginal bound and Gaussian scalar moments. -/
theorem marginalEuclid_ten {d : ℕ} (hd : 3 ≤ d)
    (hφ : PhiRate d) (hRot : StrongRotLaw d) (hConc : ConcentrationStmt d)
    {R p r : ℝ} (hR : 1 ≤ R) (hp : 1 ≤ p) (hr : 0 < r) (hr1 : r < 1) :
    ∃ ξ₁ C : ℝ, 0 < ξ₁ ∧ 0 ≤ C ∧ ∀ ξ ∈ Ioc (0 : ℝ) ξ₁,
      ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
          ∫⁻ g, supDistLU d R (rho D g).1 (euclidDistC d) ^ p ∂(pinLaw d 10) ≤
            ENNReal.ofReal (C * ξ ^ (r * p)) := by
  have h2p : 1 ≤ 2 * p := by linarith
  obtain ⟨ξu, Cu, hξu, hCu, hunit⟩ :=
    marginalEuclid_unit hd hφ hRot hConc hR h2p hr hr1
  obtain ⟨G₁, hG₁, hgauss₁⟩ :=
    l4_pin_gauss_moment (by omega : 2 ≤ d) (by norm_num : (0 : ℝ) < 10)
      1 (2 * p) (by linarith)
  obtain ⟨G₂, hG₂, hgauss₂⟩ :=
    l4_pin_gauss_moment (by omega : 2 ≤ d) (by norm_num : (0 : ℝ) < 10)
      2 p (by linarith)
  let ξ₁ : ℝ := min 1 ξu
  have hξ₁ : 0 < ξ₁ := by dsimp [ξ₁]; simp [hξu]
  let A : ℝ := G₁ ^ (1 / 2 : ℝ) * Cu ^ (1 / 2 : ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let E : ℝ≥0∞ := (2 : ℝ≥0∞) ^ p *
    (ENNReal.ofReal A + ENNReal.ofReal (2 * R) ^ p * ENNReal.ofReal G₂)
  have hE : E ≠ ⊤ := by dsimp [E]; finiteness
  refine ⟨ξ₁, E.toReal, hξ₁, ENNReal.toReal_nonneg, ?_⟩
  intro ξ hξ D hD
  have hξ0 : 0 < ξ := hξ.1
  have hξ1 : ξ ≤ 1 := (le_min_iff.mp hξ.2).1
  have hξu : ξ ∈ Ioc (0 : ℝ) ξu := ⟨hξ0, (le_min_iff.mp hξ.2).2⟩
  let μ := pinLaw d 10
  let f : DistRd d → ℝ≥0∞ := fun g =>
    supDistLU d R (rho D g).1 (euclidDistC d)
  let Z : DistRd d → ℝ := fun g => sphereAvg g 1 0
  let e : DistRd d → ℝ≥0∞ := fun g => ENNReal.ofReal (Real.exp |Z g|)
  let e₂ : DistRd d → ℝ≥0∞ := fun g => ENNReal.ofReal (Real.exp (2 * |Z g|))
  have hfm : Measurable f := endpt_measurable_supDistLU
    (fun p => p2_measurable_contMetric_apply (measurable_rho hD.measurable) p)
    (fun _ => measurable_const) R
  have hem : Measurable e :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_sphereAvg_left 1 0).abs)
  have he₂m : Measurable e₂ :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (measurable_sphereAvg_left 1 0).abs))
  have hscale := l4_pin_point_scaling (by omega : 2 ≤ d) hξ0 hD
    (by norm_num : (0 : ℝ) < 10)
  have hpath : ∀ᵐ g ∂μ, f g ≤
      e g * f (recentre 1 1 (0 : Rd d) g) +
        ENNReal.ofReal (2 * R * ξ) * e₂ g := by
    filter_upwards [hscale] with g hg
    have hF : (rho D g).1 =
        Real.exp (ξ * Z g) • (rho D (recentre 1 1 (0 : Rd d) g)).1 := by
      ext p
      simpa only [ContinuousMap.smul_apply, smul_eq_mul] using hg p.1 p.2
    have hdet := n5_supDistLU_smul_euclid_le (a := Real.exp (ξ * Z g))
      (by linarith : 0 ≤ R)
      (Real.exp_pos _).le (rho D (recentre 1 1 (0 : Rd d) g)).1
    rw [← hF] at hdet
    have hb := n5_pin_scalar_bounds hξ0.le hξ1 (Z g)
    have hcoeff : ENNReal.ofReal (2 * R * |Real.exp (ξ * Z g) - 1|) ≤
        ENNReal.ofReal (2 * R * ξ) * e₂ g := by
      calc
        ENNReal.ofReal (2 * R * |Real.exp (ξ * Z g) - 1|) ≤
            ENNReal.ofReal (2 * R * ξ * Real.exp (2 * |Z g|)) :=
          ENNReal.ofReal_le_ofReal (by
            have hh := mul_le_mul_of_nonneg_left hb.2
              (show 0 ≤ 2 * R by positivity)
            nlinarith only [hh])
        _ = _ := ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * R * ξ)
    calc
      f g ≤ ENNReal.ofReal (Real.exp (ξ * Z g)) *
          f (recentre 1 1 (0 : Rd d) g) +
          ENNReal.ofReal (2 * R * |Real.exp (ξ * Z g) - 1|) := hdet
      _ ≤ e g * f (recentre 1 1 (0 : Rd d) g) +
          ENNReal.ofReal (2 * R * ξ) * e₂ g := by
        exact add_le_add (mul_le_mul_left (ENNReal.ofReal_le_ofReal hb.1) _) hcoeff
  have hunit' : ∫⁻ g, f g ^ (2 * p) ∂(normLGFLaw d) ≤
      ENNReal.ofReal (Cu * ξ ^ (r * (2 * p))) := hunit ξ hξu D hD
  have hprod := l4_pin_product_moment (by omega : 2 ≤ d)
    (by norm_num : (0 : ℝ) < 10) 1 (by linarith : 0 ≤ p)
    f hfm.aemeasurable hG₁ hgauss₁ hunit'
  have hAprod : G₁ ^ (1 / 2 : ℝ) *
      (max 0 (Cu * ξ ^ (r * (2 * p)))) ^ (1 / 2 : ℝ) =
      A * ξ ^ (r * p) := by
    have hξpow : 0 ≤ ξ ^ (r * (2 * p)) := (Real.rpow_pos_of_pos hξ0 _).le
    have hpowe : (ξ ^ (r * (2 * p))) ^ (1 / 2 : ℝ) = ξ ^ (r * p) := by
      rw [← Real.rpow_mul hξ0.le]
      congr 1
      ring
    calc
      _ = G₁ ^ (1 / 2 : ℝ) *
          ((Cu * ξ ^ (r * (2 * p))) ^ (1 / 2 : ℝ)) := by
            rw [max_eq_right (mul_nonneg hCu hξpow)]
      _ = (G₁ ^ (1 / 2 : ℝ) * Cu ^ (1 / 2 : ℝ)) *
          ((ξ ^ (r * (2 * p))) ^ (1 / 2 : ℝ)) := by
            rw [Real.mul_rpow hCu hξpow]
            ring
      _ = A * ξ ^ (r * p) := by rw [hpowe]
  have hprod' : ∫⁻ g, (e g * f (recentre 1 1 (0 : Rd d) g)) ^ p ∂μ ≤
      ENNReal.ofReal A * ENNReal.ofReal (ξ ^ (r * p)) := by
    calc
      _ ≤ ENNReal.ofReal (G₁ ^ (1 / 2 : ℝ) *
          (max 0 (Cu * ξ ^ (r * (2 * p)))) ^ (1 / 2 : ℝ)) := by
            simpa only [e, Z, μ, one_mul] using hprod
      _ = ENNReal.ofReal A * ENNReal.ofReal (ξ ^ (r * p)) := by
        rw [hAprod, ENNReal.ofReal_mul hA]
  have hξpow : ENNReal.ofReal ξ ^ p ≤ ENNReal.ofReal (ξ ^ (r * p)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hξ0.le (by linarith : 0 ≤ p)]
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hξ0 hξ1 (by nlinarith : r * p ≤ p))
  have hscalar : ∫⁻ g, (ENNReal.ofReal (2 * R * ξ) * e₂ g) ^ p ∂μ ≤
      ENNReal.ofReal (2 * R) ^ p * ENNReal.ofReal G₂ *
        ENNReal.ofReal (ξ ^ (r * p)) := by
    have hc : ENNReal.ofReal (2 * R * ξ) =
        ENNReal.ofReal (2 * R) * ENNReal.ofReal ξ := ENNReal.ofReal_mul (by positivity)
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ p)]
    rw [lintegral_const_mul' _ _ (by finiteness : ENNReal.ofReal (2 * R * ξ) ^ p ≠ ⊤)]
    calc
      ENNReal.ofReal (2 * R * ξ) ^ p * (∫⁻ g, e₂ g ^ p ∂μ) ≤
          ENNReal.ofReal (2 * R * ξ) ^ p * ENNReal.ofReal G₂ :=
            mul_le_mul_right hgauss₂ _
      _ ≤ ENNReal.ofReal (2 * R) ^ p * ENNReal.ofReal G₂ *
          ENNReal.ofReal (ξ ^ (r * p)) := by
            rw [hc, ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ p)]
            calc
              ENNReal.ofReal (2 * R) ^ p * ENNReal.ofReal ξ ^ p * ENNReal.ofReal G₂ ≤
                  ENNReal.ofReal (2 * R) ^ p *
                    ENNReal.ofReal (ξ ^ (r * p)) * ENNReal.ofReal G₂ := by
                      gcongr
              _ = _ := by ring
  have hmain : ∫⁻ g, f g ^ p ∂μ ≤
      E * ENNReal.ofReal (ξ ^ (r * p)) := by
    have hpoint : ∀ᵐ g ∂μ, f g ^ p ≤
        (2 : ℝ≥0∞) ^ p *
          ((e g * f (recentre 1 1 (0 : Rd d) g)) ^ p +
            (ENNReal.ofReal (2 * R * ξ) * e₂ g) ^ p) := by
      filter_upwards [hpath] with g hg
      exact (ENNReal.rpow_le_rpow hg (by linarith : 0 ≤ p)).trans
        (ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow _ _ (by linarith : 0 ≤ p))
    calc
      ∫⁻ g, f g ^ p ∂μ ≤
          ∫⁻ g, (2 : ℝ≥0∞) ^ p *
            ((e g * f (recentre 1 1 (0 : Rd d) g)) ^ p +
              (ENNReal.ofReal (2 * R * ξ) * e₂ g) ^ p) ∂μ :=
              lintegral_mono_ae hpoint
      _ = (2 : ℝ≥0∞) ^ p *
          ((∫⁻ g, (e g * f (recentre 1 1 (0 : Rd d) g)) ^ p ∂μ) +
            (∫⁻ g, (ENNReal.ofReal (2 * R * ξ) * e₂ g) ^ p ∂μ)) := by
              rw [lintegral_const_mul' _ _ (by finiteness : (2 : ℝ≥0∞) ^ p ≠ ⊤)]
              rw [lintegral_add_left (f := fun g =>
                (e g * f (recentre 1 1 (0 : Rd d) g)) ^ p)]
              exact ((hem.mul (hfm.comp (measurable_recentre 1 1 0))).pow_const p)
      _ ≤ (2 : ℝ≥0∞) ^ p *
          (ENNReal.ofReal A * ENNReal.ofReal (ξ ^ (r * p)) +
            ENNReal.ofReal (2 * R) ^ p * ENNReal.ofReal G₂ *
              ENNReal.ofReal (ξ ^ (r * p))) := by
              gcongr
      _ = E * ENNReal.ofReal (ξ ^ (r * p)) := by dsimp [E]; ring
  calc
    ∫⁻ g, f g ^ p ∂μ ≤ E * ENNReal.ofReal (ξ ^ (r * p)) := hmain
    _ = ENNReal.ofReal (E.toReal * ξ ^ (r * p)) := by
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hE]

end HigherDimLQGContinuity
