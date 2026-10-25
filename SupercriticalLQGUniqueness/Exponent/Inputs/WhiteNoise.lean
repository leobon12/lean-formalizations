import LQGMetric.Papers.DDDF.S6P26Up0
import LQGMetric.Papers.DDDF.P18Law
import LQGMetric.Papers.DDDF.P18S2




 
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Exponent.Inputs.WhiteNoise
open LQGMetric LQGMetric.WhiteNoise LQGMetric.DDDF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

 
theorem variance_dyadic_band (hW : IsWhiteNoise P W) {a b : ℝ} (hab : a ≤ b) (x : ℂ) :
    Var[phi W ((2 : ℝ) ^ (-b)) ((2 : ℝ) ^ (-a)) x; P] = (b - a) * Real.log 2 := by
  have hp : 0 < (2 : ℝ) ^ (-b) := Real.rpow_pos_of_pos (by norm_num) _
  have hle : (2 : ℝ) ^ (-b) ≤ (2 : ℝ) ^ (-a) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  rw [variance_phi hW hp hle x, Real.log_div (by positivity) (by positivity)]
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2), Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  ring

 
theorem band_add_ae (hW : IsWhiteNoise P W) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (x : ℂ) :
    phi W ((2 : ℝ) ^ (-c)) ((2 : ℝ) ^ (-a)) x =ᵐ[P]
      fun ω => phi W ((2 : ℝ) ^ (-c)) ((2 : ℝ) ^ (-b)) x ω +
        phi W ((2 : ℝ) ^ (-b)) ((2 : ℝ) ^ (-a)) x ω := by
  apply phi_add_ae hW (by positivity)
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))

 
theorem band_independent (hW : IsWhiteNoise P W) {a b c : ℝ} (_hab : a ≤ b)
    (hbc : b ≤ c) :
    IndepFun (fun ω x => phi W ((2 : ℝ) ^ (-c)) ((2 : ℝ) ^ (-b)) x ω)
      (fun ω x => phi W ((2 : ℝ) ^ (-b)) ((2 : ℝ) ^ (-a)) x ω) P := by
  exact indepFun_phi hW (by positivity)
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))

 
theorem dyadic_motion_law (hW : IsWhiteNoise P W) {m n : ℕ} (hmn : m ≤ n)
    (u : Circle) (c : ℂ) :
    P.map (fun ω x => phiMN W P m n ((u : ℂ) * x + c) ω) =
      P.map (fun ω x => phiMN W P m n x ω) :=
  map_phiMN_motion hW hmn u c

 
theorem band_scale_law (hW : IsWhiteNoise P W) {a b r : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hr : 0 < r) :
    P.map (fun ω x => phi W a b ((r : ℂ) * x) ω) =
      P.map (fun ω x => phi W (a / r) (b / r) x ω) :=
  map_phi_scale hW ha hab hr

 
theorem square_crossing_pos_finite {ξ : ℝ} {Y : ℂ → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun x => Y x ω) (ω : Ω) :
    0 < lenObs ξ Y (rectAB 1 1) ω ∧
      rectLen ξ (fun x => Y x ω) (rectAB 1 1) ≠ ⊤ := by
  constructor
  · exact lenObs_pos hYc (rectAB 1 1) (by norm_num [rectAB])
      (by norm_num [rectAB]) (by norm_num [rectAB, MarkedRect.crossWidth]) ω
  · exact rectLen_ne_top (rectAB 1 1) (by norm_num [rectAB])
      (by norm_num [rectAB]) (hYc ω)

 
theorem square_quantile_closed_right {ξ : ℝ} {Y : ℂ → Ω → ℝ} (hW : IsWhiteNoise P W)
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x))
    {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    p ≤ P {ω | lenObs ξ Y (rectAB 1 1) ω ≤ ellQ ξ P Y (rectAB 1 1) p} := by
  letI := hW.isProbabilityMeasure
  exact prob_le_ellQ hYc hYm (rectAB 1 1) hp0 hp1

 
theorem square_quantile_pos {ξ : ℝ} {Y : ℂ → Ω → ℝ} (hW : IsWhiteNoise P W)
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x))
    {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < ellQ ξ P Y (rectAB 1 1) p := by
  letI := hW.isProbabilityMeasure
  let L : Ω → ℝ := lenObs ξ Y (rectAB 1 1)
  have hLm : Measurable L := measurable_lenObs hYc hYm (rectAB 1 1)
  have h0 : P {ω | L ω ≤ 0} = 0 := by
    have e : {ω | L ω ≤ 0} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact not_le.mpr (square_crossing_pos_finite hYc ω).1
    simp only [e, measure_empty]
  by_contra hq
  have hq0 : ellQ ξ P Y (rectAB 1 1) p ≤ 0 := le_of_not_gt hq
  have h := (le_measure_Iic_iff_lowerQuantile_le (μ := P.map L) hp0 hp1).2 hq0
  rw [Measure.map_apply hLm measurableSet_Iic] at h
  change p ≤ P {ω | L ω ≤ 0} at h
  rw [h0] at h
  exact (not_le.mpr hp0) h

 
theorem square_quantile_strict_left {ξ : ℝ} {Y : ℂ → Ω → ℝ} (hW : IsWhiteNoise P W)
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x))
    {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    P {ω | lenObs ξ Y (rectAB 1 1) ω < ellQ ξ P Y (rectAB 1 1) p} ≤ p := by
  letI := hW.isProbabilityMeasure
  have h := prob_ge_ellQ (ξ := ξ) (Y := Y) (P := P) hYc hYm (rectAB 1 1) hp0 hp1
  have hm : MeasurableSet {ω | ellQ ξ P Y (rectAB 1 1) p ≤
      lenObs ξ Y (rectAB 1 1) ω} :=
    measurableSet_le measurable_const (measurable_lenObs hYc hYm (rectAB 1 1))
  have e : {ω | lenObs ξ Y (rectAB 1 1) ω < ellQ ξ P Y (rectAB 1 1) p} =
      {ω | ellQ ξ P Y (rectAB 1 1) p ≤ lenObs ξ Y (rectAB 1 1) ω}ᶜ := by
    ext ω; simp
  rw [e, prob_compl_eq_one_sub hm]
  calc 1 - P {ω | ellQ ξ P Y (rectAB 1 1) p ≤ lenObs ξ Y (rectAB 1 1) ω}
      ≤ 1 - (1 - p) := tsub_le_tsub_left h 1
    _ = p := ENNReal.sub_sub_cancel ENNReal.one_ne_top hp1.le

 
theorem dyadic_square_quantile {ξ : ℝ} (hW : IsWhiteNoise P W) (n : ℕ)
    {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < ellN ξ W P n p ∧
      P {ω | lenMN ξ W P 1 1 0 n ω < ellN ξ W P n p} ≤ p ∧
      p ≤ P {ω | lenMN ξ W P 1 1 0 n ω ≤ ellN ξ W P n p} := by
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  change 0 < ellQ ξ P (phiMN W P 0 n) (rectAB 1 1) p ∧
    P {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω <
      ellQ ξ P (phiMN W P 0 n) (rectAB 1 1) p} ≤ p ∧
    p ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω ≤
      ellQ ξ P (phiMN W P 0 n) (rectAB 1 1) p}
  exact ⟨square_quantile_pos hW hφ.cont hφ.meas hp0 hp1,
    square_quantile_strict_left hW hφ.cont hφ.meas hp0 hp1,
    square_quantile_closed_right hW hφ.cont hφ.meas hp0 hp1⟩

 
theorem gradient_exp_moment {s : ℝ} (hs : 0 < s) :
    ∃ c K : ℝ, 0 ≤ c ∧ 0 ≤ K ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ},
      IsWhiteNoise P W → ∀ (n : ℕ), 1 ≤ n → ∀ (Y : ℂ → Ω → ℝ),
      (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ n)⁻¹ 1 x) →
      (∀ ω, ContDiff ℝ 1 fun x => Y x ω) →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (s * LQGMetric.DDDF.T20C.Obig n Y ω)) ∂P ≤
        ENNReal.ofReal (25 * K * Real.exp (c * √(n : ℝ))) :=
  LQGMetric.DDDF.S6U.obig_expMoment hs

 
theorem gradient_exp_moment_sqrt {s : ℝ} (hs : 0 < s) :
    ∃ H v : ℝ, 0 ≤ H ∧ 0 ≤ v ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ},
      IsWhiteNoise P W → ∀ (n : ℕ), 1 ≤ n → ∀ (Y : ℂ → Ω → ℝ),
      (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ n)⁻¹ 1 x) →
      (∀ ω, ContDiff ℝ 1 fun x => Y x ω) →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (s * LQGMetric.DDDF.T20C.Obig n Y ω)) ∂P ≤
        ENNReal.ofReal (H * Real.exp (s * (v * √(n : ℝ)))) := by
  obtain ⟨c, K, hc, hK, h⟩ := gradient_exp_moment hs
  refine ⟨25 * K, c / s, by positivity, div_nonneg hc hs.le, ?_⟩
  intro Ω _ P W hW n hn Y hY hYc
  have hh := h hW n hn Y hY hYc
  convert hh using 1
  congr 2
  field_simp

end SupercriticalLQGUniqueness.Exponent.Inputs.WhiteNoise
