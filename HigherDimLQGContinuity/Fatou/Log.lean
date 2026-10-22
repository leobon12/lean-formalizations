import HigherDimLQGContinuity.Fatou.Cross
import HigherDimLQGContinuity.Fatou.Upper
import HigherDimLQGMetric.Sec10.Lemma103Det

/-!
# Unit-distance bounds and log integrability

The fixed shell centered at one quarter of `e₁` contains `(0,e₁)` as an admissible
boundary pair. This gives a direct inverse-moment bound for the unit distance.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

/-- A quarter-way point on the unit coordinate segment. -/
def fatouQuarter (d : ℕ) : Rd d := (4⁻¹ : ℝ) • e₁ d

theorem fatou_zero_mem_inner_sphere {d : ℕ} (hd : 1 ≤ d) :
    (0 : Rd d) ∈ sphere (fatouQuarter d) (1 / 4 : ℝ) := by
  rw [mem_sphere, dist_eq_norm, zero_sub, norm_neg, fatouQuarter, norm_smul,
    HigherDimLFPP.norm_e₁ (by omega), mul_one, Real.norm_eq_abs]
  norm_num

theorem fatou_e₁_mem_outer_sphere {d : ℕ} (hd : 1 ≤ d) :
    e₁ d ∈ sphere (fatouQuarter d) (3 / 4 : ℝ) := by
  rw [mem_sphere, dist_eq_norm, fatouQuarter]
  have heq : e₁ d - (4⁻¹ : ℝ) • e₁ d = (3 / 4 : ℝ) • e₁ d := by
    calc
      e₁ d - (4⁻¹ : ℝ) • e₁ d = (1 - 4⁻¹ : ℝ) • e₁ d := by
        rw [sub_smul, one_smul]
      _ = (3 / 4 : ℝ) • e₁ d := by norm_num
  rw [heq, norm_smul, HigherDimLFPP.norm_e₁ (by omega), mul_one, Real.norm_eq_abs]
  norm_num

/-- The quarter-centered crossing is bounded by the point distance `D(0,e₁)`.
No length-metric argument is needed: the pair itself belongs to the two spheres. -/
theorem fatou_across_le_unit {d : ℕ} (hd : 1 ≤ d) (D : ContMetric d) :
    acrossDist D (fatouQuarter d) (1 / 4) (3 / 4) ≤
      ENNReal.ofReal (D.1 (0, e₁ d)) := by
  unfold acrossDist
  exact iInf_le_of_le (0 : Rd d) <| iInf_le_of_le (fatou_zero_mem_inner_sphere hd) <|
    iInf_le_of_le (e₁ d) <| iInf_le_of_le (fatou_e₁_mem_outer_sphere hd) le_rfl

/-- A local upper envelope at radius one controls the unit point distance. -/
theorem fatou_unit_le_envelope {d : ℕ} (hd : 1 ≤ d) (D : ContMetric d) {H σ : ℝ}
    (h : internalDiamRd D (ball (s8bCenter d) 1) (ball (s8bCenter d) 2) ≤
      ENNReal.ofReal (H * (1 : ℝ) ^ σ)) :
    ENNReal.ofReal (D.1 (0, e₁ d)) ≤ ENNReal.ofReal H := by
  have h0 : (0 : Rd d) ∈ ball (s8bCenter d) 1 :=
    (ball_subset_ball (by norm_num : (3 / 4 : ℝ) ≤ 1)) (s8b_zero_mem_dom hd)
  have h1 : e₁ d ∈ ball (s8bCenter d) 1 :=
    (ball_subset_ball (by norm_num : (3 / 4 : ℝ) ≤ 1)) (s8b_e₁_mem_dom hd)
  calc
    ENNReal.ofReal (D.1 (0, e₁ d)) ≤ D.internal (ball (s8bCenter d) 2) 0 (e₁ d) :=
      D.ofReal_le_internal _ _ _
    _ ≤ internalDiamRd D (ball (s8bCenter d) 1) (ball (s8bCenter d) 2) := by
      unfold internalDiamRd
      exact le_iSup_of_le 0 <| le_iSup_of_le h0 <|
        le_iSup_of_le (e₁ d) <| le_iSup_of_le h1 le_rfl
    _ ≤ ENNReal.ofReal H := by simpa only [Real.one_rpow, mul_one] using h

/-- A positive power controls both signs of the logarithm. -/
theorem fatou_abs_log_le_powers {x p : ℝ} (hx : 0 < x) (hp : 0 < p) :
    |Real.log x| ≤ (x ^ p + x⁻¹ ^ p) / p := by
  have hpos : 0 ≤ x ^ p := Real.rpow_nonneg hx.le _
  have hneg : 0 ≤ x⁻¹ ^ p := Real.rpow_nonneg (inv_nonneg.mpr hx.le) _
  have hupper := Real.log_le_rpow_div hx.le hp
  have hlower := Real.log_le_rpow_div (inv_nonneg.mpr hx.le) hp
  rw [Real.log_inv] at hlower
  rw [add_div]
  apply abs_le.mpr
  constructor <;> linarith [div_nonneg hpos hp.le, div_nonneg hneg hp.le]

/-- Extended-real form of the logarithmic estimate used with positive and inverse moments. -/
theorem fatou_ofReal_abs_log_le {x H p : ℝ} {J : ℝ≥0∞}
    (hx : 0 < x) (hp : 0 < p) (hH : x ≤ H) (hJ : J ≤ ENNReal.ofReal x) :
    ENNReal.ofReal |Real.log x| ≤
      ENNReal.ofReal p⁻¹ * (ENNReal.ofReal (H ^ p) + J⁻¹ ^ p) := by
  have hxp : 0 ≤ x ^ p := Real.rpow_nonneg hx.le _
  have hxip : 0 ≤ x⁻¹ ^ p := Real.rpow_nonneg (inv_nonneg.mpr hx.le) _
  have hXupper : ENNReal.ofReal (x ^ p) ≤ ENNReal.ofReal (H ^ p) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hx.le hH hp.le)
  have hXlower : ENNReal.ofReal (x⁻¹ ^ p) ≤ J⁻¹ ^ p := by
    calc
      ENNReal.ofReal (x⁻¹ ^ p) = (ENNReal.ofReal x)⁻¹ ^ p := by
        rw [← ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hx.le) hp.le,
          ENNReal.ofReal_inv_of_pos hx]
      _ ≤ J⁻¹ ^ p := ENNReal.rpow_le_rpow (ENNReal.inv_le_inv.mpr hJ) hp.le
  calc
    ENNReal.ofReal |Real.log x| ≤ ENNReal.ofReal ((x ^ p + x⁻¹ ^ p) / p) :=
      ENNReal.ofReal_le_ofReal (fatou_abs_log_le_powers hx hp)
    _ = ENNReal.ofReal p⁻¹ *
        (ENNReal.ofReal (x ^ p) + ENNReal.ofReal (x⁻¹ ^ p)) := by
      have heq : (x ^ p + x⁻¹ ^ p) / p = p⁻¹ * (x ^ p + x⁻¹ ^ p) := by ring
      rw [heq, ENNReal.ofReal_mul (inv_nonneg.mpr hp.le),
        ENNReal.ofReal_add hxp hxip]
    _ ≤ ENNReal.ofReal p⁻¹ * (ENNReal.ofReal (H ^ p) + J⁻¹ ^ p) := by
      gcongr

/-- Positive and inverse moments yield a uniform bound on the mean absolute logarithm. -/
theorem fatou_integrable_log_of_moments {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {p B C : ℝ} (hp : 0 < p)
    (X H : Ω → ℝ) (J : Ω → ℝ≥0∞)
    (hXm : Measurable X) (hHm : Measurable H) (hJm : Measurable J)
    (hXpos : ∀ ω, 0 < X ω)
    (hXH : ∀ᵐ ω ∂P, X ω ≤ H ω)
    (hJX : ∀ᵐ ω ∂P, J ω ≤ ENNReal.ofReal (X ω))
    (hHmom : ∫⁻ ω, ENNReal.ofReal (H ω ^ p) ∂P ≤ ENNReal.ofReal B)
    (hJmom : ∫⁻ ω, (J ω)⁻¹ ^ p ∂P ≤ ENNReal.ofReal C) :
    Integrable (fun ω => Real.log (X ω)) P ∧
      |∫ ω, Real.log (X ω) ∂P| ≤
        (ENNReal.ofReal p⁻¹ * (ENNReal.ofReal B + ENNReal.ofReal C)).toReal := by
  have hmU : Measurable (fun ω => ENNReal.ofReal (H ω ^ p)) :=
    (hHm.pow_const p).ennreal_ofReal
  have hmV : Measurable (fun ω => (J ω)⁻¹ ^ p) :=
    (hJm.inv).pow_const p
  have hlogMeas : Measurable (fun ω => Real.log (X ω)) := hXm.log
  have hAbsMeas : Measurable (fun ω => |Real.log (X ω)|) := hlogMeas.abs
  have hlin : (∫⁻ ω, ENNReal.ofReal |Real.log (X ω)| ∂P) ≤
      ENNReal.ofReal p⁻¹ * (ENNReal.ofReal B + ENNReal.ofReal C) := by
    calc
      (∫⁻ ω, ENNReal.ofReal |Real.log (X ω)| ∂P) ≤
          ∫⁻ ω, ENNReal.ofReal p⁻¹ *
            (ENNReal.ofReal (H ω ^ p) + (J ω)⁻¹ ^ p) ∂P := by
        apply lintegral_mono_ae
        filter_upwards [hXH, hJX] with ω hupper hlower
        exact fatou_ofReal_abs_log_le (hXpos ω) hp hupper hlower
      _ = ENNReal.ofReal p⁻¹ *
          ((∫⁻ ω, ENNReal.ofReal (H ω ^ p) ∂P) +
            (∫⁻ ω, (J ω)⁻¹ ^ p ∂P)) := by
        calc
          _ = ENNReal.ofReal p⁻¹ *
              (∫⁻ ω, ENNReal.ofReal (H ω ^ p) + (J ω)⁻¹ ^ p ∂P) :=
            lintegral_const_mul _ (hmU.add hmV)
          _ = _ := by rw [lintegral_add_left hmU]
      _ ≤ ENNReal.ofReal p⁻¹ * (ENNReal.ofReal B + ENNReal.ofReal C) := by
        gcongr
  have hKfin : ENNReal.ofReal p⁻¹ *
      (ENNReal.ofReal B + ENNReal.ofReal C) ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
  have hAbsInt : Integrable (fun ω => |Real.log (X ω)|) P :=
    (lintegral_ofReal_ne_top_iff_integrable hAbsMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => abs_nonneg _)).mp
      (ne_top_of_le_ne_top hKfin hlin)
  have hLogInt : Integrable (fun ω => Real.log (X ω)) P :=
    (integrable_norm_iff hlogMeas.aestronglyMeasurable).mp
      (by simpa only [Real.norm_eq_abs] using hAbsInt)
  refine ⟨hLogInt, ?_⟩
  have hAbsNonneg : 0 ≤ ∫ ω, |Real.log (X ω)| ∂P :=
    integral_nonneg fun _ => abs_nonneg _
  have hAbsBound : ∫ ω, |Real.log (X ω)| ∂P ≤
      (ENNReal.ofReal p⁻¹ * (ENNReal.ofReal B + ENNReal.ofReal C)).toReal := by
    have hEq := ofReal_integral_eq_lintegral_ofReal hAbsInt
      (Filter.Eventually.of_forall fun ω => abs_nonneg (Real.log (X ω)))
    have ht := ENNReal.toReal_mono hKfin (hEq.trans_le hlin)
    simpa only [ENNReal.toReal_ofReal hAbsNonneg] using ht
  exact (abs_integral_le_integral_abs).trans hAbsBound

/-- The two convolution moment inputs give a uniform bound on the canonical mean logarithm. -/
theorem fatou_log_of_conv {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ σ p : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hσ : 0 < σ) (hσμ : σ < μ) (hp : 0 < p)
    (hpb : 32 * p * b ≤ Real.sqrt (2 * d)) :
    ∃ M : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ → ∀ D : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ (distExp d ξ) D →
      TendstoInProbLU (normLGFLaw d)
        (fun ε g => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε g) (𝓝[>] 0)
        (fun g => (D g).1) →
      Integrable (fun g => Real.log ((D g).1 (0, e₁ d))) (normLGFLaw d) ∧
      |logMean D| ≤ M := by
  obtain ⟨Cu, Au, hupper⟩ :=
    fatou_upper_of_conv hd hκ hC1 hb hμ hμ1 hσ hσμ hp hpb
  obtain ⟨Ci, hcross⟩ := fatou_invCross_of_conv hd hκ hC2 hb hμ
    (fatouQuarter d) (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 3 / 4) hp
  let M := (ENNReal.ofReal p⁻¹ *
    (ENNReal.ofReal (Cu * (1 + 1 : ℝ) ^ Au) + ENNReal.ofReal Ci)).toReal
  refine ⟨M, fun ξ hξ D hD hconv => ?_⟩
  obtain ⟨H, hHm, hH1, hHmom, hHpt⟩ := hupper ξ hξ D hD hconv 1 le_rfl
  have hJmom := hcross ξ hξ D hconv
  let X : DistRd d → ℝ := fun g => (D g).1 (0, e₁ d)
  let J : DistRd d → ℝ≥0∞ := fun g =>
    acrossDist (D g) (fatouQuarter d) (1 / 4) (3 / 4)
  have hXm : Measurable X := p2_measurable_contMetric_apply hD.measurable _
  have hJm : Measurable J :=
    (fatou_continuous_across (fatouQuarter d) (1 / 4) (3 / 4)).measurable.comp
      (measurable_subtype_coe.comp hD.measurable)
  have hXpos (g : DistRd d) : 0 < X g := (D g).apply_pos (p2_zero_ne_e₁ (by omega))
  have hJX : ∀ᵐ g ∂(normLGFLaw d), J g ≤ ENNReal.ofReal (X g) :=
    Filter.Eventually.of_forall fun g => fatou_across_le_unit (by omega) (D g)
  have hXH : ∀ᵐ g ∂(normLGFLaw d), X g ≤ H g := by
    filter_upwards [hHpt] with g hg
    have hz : s8bCenter d ∈ closedBall (0 : Rd d) 1 := by
      rw [mem_closedBall, dist_zero_right, s8b_norm_center (by omega)]
      norm_num
    have hs : (1 : ℝ) ∈ Ioc 0 1 := ⟨by norm_num, le_rfl⟩
    have h := fatou_unit_le_envelope (by omega) (D g)
      (show internalDiamRd (D g) (ball (s8bCenter d) 1)
        (ball (s8bCenter d) 2) ≤ ENNReal.ofReal (H g * (1 : ℝ) ^ σ) by
          simpa only [mul_one] using hg _ hz 1 hs)
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith [hH1 g])).mp h
  have h := fatou_integrable_log_of_moments (normLGFLaw d) hp
    X H J hXm hHm hJm hXpos hXH hJX hHmom hJmom
  exact ⟨h.1, by simpa only [logMean, M] using h.2⟩

end HigherDimLQGContinuity
