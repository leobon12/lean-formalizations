import HigherDimLFPP.Field.OscBlock
import HigherDimLFPP.Upper.PathTree

/-!
# The root average of the cutoff field (packet P-OSC, target T2)

Source: `source/higher-dimensional-lfpp-limit.pdf`, Lemma 4.1 ("Moreover": `H_root = O_P(1)`);
planning audit HA3, Details D3 (a) and the second conjunct of its Lean statement
`OscillationBound` in (c).

Let `H` be a continuous version of the band field `H_{a,b}` (`0 < a ≤ b`), let `ρ` be a support
radius of `κ` (`κ y = 0` for `‖y‖ ≥ ρ`), and let `X = ⟨H, ν_{[0,e₁]}⟩ = ∫₀¹ H(s e₁) ds` be the
pathwise segment average (`Upper.segAvg`).  Then (HA3 D3 (a))

`E X² = ∫∫_{[0,1]²} ⟪k_{s e₁}, k_{s' e₁}⟫ ds ds'
      = ∫∫ ∫_a^b t⁻¹ C((s - s') e₁ / t) dt ds ds' ≤ ∫_a^b t⁻¹ · 4ρt dt = 4ρ (b - a)`,

using `|C| ≤ 1`, `C = 0` off `B(0, 2ρ)` and `λ{s' ∈ (0,1] : |s - s'| < 2ρt} ≤ 4ρt`.

* `RootAvg.integral_segAvg_sq_le`: `X² ∈ L¹` and `E X² ≤ 4ρ(b - a)`;
* `RootAvg.variance_segAvg_le`: `Var X ≤ 4ρ(b - a)`;
* `RootAvg.segAvg_tail_le`: `P*(M < |X|) ≤ 4ρ(b - a)/M²` (Chebyshev);
* `segAvg_cutoff_variance_le`, `segAvg_cutoff_tail_le`, `segAvg_cutoff_bounded` (target T2): for
  continuous versions `H ε` of `H_{ε,1}`, `Var ⟨H ε, ν_{[0,e₁]}⟩ ≤ 4ρ` for all `ε ∈ (0,1)`, hence
  `P*(|H_root| > M) ≤ 4ρ/M²` uniformly in `ε`, and `H_root = O_P(1)` in HA3's form.

The proof computes the second moment by Fubini on `Ω × (0,1]²` (the integrand is jointly
measurable since versions are, and `E|H(x) H(y)| ≤ log(b/a)`), then on `(0,1] × (a,b)`.

2D template: `LQGDimension/LFPP/OscillationAux.lean` (`Osc37.segVar_le`, `segAvg_bounded`), where
the variance came from the circle-average covariance through `segCombLaw`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP

namespace RootAvg

variable {d : ℕ}

/-- The segment average `⟨φ, ν_{[0,e₁]}⟩` as an integral over `(0, 1]`. -/
theorem segAvg_zero_e₁ (φ : Rd d → ℝ) :
    Upper.segAvg φ 0 (e₁ d) = ∫ s in Ioc (0 : ℝ) 1, φ (s • e₁ d) := by
  unfold Upper.segAvg
  rw [intervalIntegral.integral_of_le zero_le_one]
  simp only [zero_add, sub_zero]

/-- A support radius of an admissible kernel is nonnegative. -/
theorem radius_nonneg {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {ρ : ℝ}
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) : 0 ≤ ρ := by
  by_contra hneg
  push Not at hneg
  have hzero : ∀ y, κ y = 0 := fun y => hρ y (hneg.le.trans (norm_nonneg y))
  have h := hκ.integral_sq
  simp only [hzero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero] at h
  exact zero_ne_one h

/-- `∫_{(0,1]} C(t⁻¹ (s - s') e₁) / t ds' ≤ 4ρ` for `t > 0`. -/
theorem integral_autoCorr_div_le [NeZero d] {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {ρ : ℝ}
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) (s : ℝ) {t : ℝ} (ht : 0 < t) :
    ∫ s' in Ioc (0 : ℝ) 1, autoCorr κ (t⁻¹ • (s • e₁ d - s' • e₁ d)) / t ≤ 4 * ρ := by
  have hρ0 := radius_nonneg hκ hρ
  set S : Set ℝ := Ioo (s - 2 * ρ * t) (s + 2 * ρ * t) with hS
  have hC := continuous_autoCorr hκ
  have hcont : Continuous fun s' : ℝ => autoCorr κ (t⁻¹ • (s • e₁ d - s' • e₁ d)) / t := by
    fun_prop
  have hint : Integrable (fun s' : ℝ => autoCorr κ (t⁻¹ • (s • e₁ d - s' • e₁ d)) / t)
      ((volume : Measure ℝ).restrict (Ioc 0 1)) :=
    Integrable.of_bound hcont.aestronglyMeasurable (1 / t) (Eventually.of_forall fun s' => by
      rw [Real.norm_eq_abs, abs_div, abs_of_pos ht]
      exact div_le_div_of_nonneg_right (abs_autoCorr_le_one hκ _) ht.le)
  have hpt : ∀ s', autoCorr κ (t⁻¹ • (s • e₁ d - s' • e₁ d)) / t ≤
      S.indicator (fun _ => 1 / t) s' := by
    intro s'
    by_cases hs' : s' ∈ S
    · rw [indicator_of_mem hs']
      exact div_le_div_of_nonneg_right (autoCorr_le_one hκ _) ht.le
    · rw [indicator_of_notMem hs']
      have hfar : 2 * ρ ≤ ‖t⁻¹ • (s • e₁ d - s' • e₁ d)‖ := by
        rw [← sub_smul, norm_smul, norm_smul, Upper.norm_e₁, mul_one, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_inv, abs_of_pos ht, inv_mul_eq_div, le_div_iff₀ ht]
        rw [hS, mem_Ioo, not_and_or, not_lt, not_lt] at hs'
        have hρt : 0 ≤ ρ * t := mul_nonneg hρ0 ht.le
        rcases hs' with h | h
        · rw [abs_of_nonneg (by linarith)]
          linarith
        · rw [abs_of_nonpos (by linarith)]
          linarith
      rw [autoCorr_eq_zero_of_two_mul_le hρ hfar, zero_div]
  have hvol : (volume : Measure ℝ).real S = 4 * ρ * t := by
    rw [hS, measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by nlinarith)]
    ring
  calc ∫ s' in Ioc (0 : ℝ) 1, autoCorr κ (t⁻¹ • (s • e₁ d - s' • e₁ d)) / t
      ≤ ∫ s' in Ioc (0 : ℝ) 1, S.indicator (fun _ => 1 / t) s' :=
        integral_mono hint ((integrable_const (1 / t)).indicator measurableSet_Ioo) hpt
    _ = ((volume : Measure ℝ).restrict (Ioc 0 1)).real S * (1 / t) := by
        rw [integral_indicator_const _ measurableSet_Ioo, smul_eq_mul]
    _ ≤ (volume : Measure ℝ).real S * (1 / t) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [measureReal_restrict_apply measurableSet_Ioo]
        exact measureReal_mono inter_subset_left
          (by rw [hS, Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    _ = 4 * ρ := by
        rw [hvol]
        field_simp

/-- For each `s`, `∫_{(0,1]} ⟪k_{s e₁}, k_{s' e₁}⟫ ds' ≤ 4ρ(b - a)` (Fubini on `(0,1] × (a,b)`). -/
theorem integral_inner_bandVec_le [NeZero d] {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {ρ : ℝ}
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (s : ℝ) :
    ∫ s' in Ioc (0 : ℝ) 1, ⟪bandVec κ a b (s • e₁ d), bandVec κ a b (s' • e₁ d)⟫ ≤
      4 * ρ * (b - a) := by
  set f : ℝ → ℝ → ℝ := fun s' t => autoCorr κ (t⁻¹ • (s • e₁ d - s' • e₁ d)) / t with hf
  simp_rw [inner_bandVec_self_band hκ ha b]
  have hC := continuous_autoCorr hκ
  have hfm : Measurable (Function.uncurry f) := by
    have h1 : Measurable fun q : ℝ × ℝ => q.2⁻¹ • (s • e₁ d - q.1 • e₁ d) := by fun_prop
    exact (hC.measurable.comp h1).div measurable_snd
  have hfint : Integrable (Function.uncurry f)
      (((volume : Measure ℝ).restrict (Ioc 0 1)).prod
        ((volume : Measure ℝ).restrict (Ioo a b))) := by
    refine Integrable.of_bound hfm.aestronglyMeasurable (1 / a) ?_
    rw [Measure.prod_restrict]
    refine (ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioo)).2
      (Eventually.of_forall fun q hq => ?_)
    have ht : a < q.2 := hq.2.1
    have ht0 : 0 < q.2 := ha.trans ht
    show ‖autoCorr κ (q.2⁻¹ • (s • e₁ d - q.1 • e₁ d)) / q.2‖ ≤ 1 / a
    rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0]
    calc |autoCorr κ (q.2⁻¹ • (s • e₁ d - q.1 • e₁ d))| / q.2 ≤ 1 / q.2 :=
          div_le_div_of_nonneg_right (abs_autoCorr_le_one hκ _) ht0.le
      _ ≤ 1 / a := one_div_le_one_div_of_le ha ht.le
  have hswap := integral_integral_swap hfint
  rw [show (∫ s' in Ioc (0 : ℝ) 1, ∫ t in Ioo a b,
      autoCorr κ (t⁻¹ • (s • e₁ d - s' • e₁ d)) / t) =
      ∫ s' in Ioc (0 : ℝ) 1, ∫ t in Ioo a b, f s' t from rfl, hswap]
  have hinner : ∀ t ∈ Ioo a b, ∫ s' in Ioc (0 : ℝ) 1, f s' t ≤ 4 * ρ := fun t ht =>
    integral_autoCorr_div_le hκ hρ s (ha.trans ht.1)
  calc ∫ t in Ioo a b, ∫ s' in Ioc (0 : ℝ) 1, f s' t
      ≤ ∫ _t in Ioo a b, 4 * ρ :=
        setIntegral_mono_on hfint.integral_prod_right (integrable_const _) measurableSet_Ioo
          hinner
    _ = 4 * ρ * (b - a) := by
        rw [setIntegral_const, Real.volume_real_Ioo_of_le hab, smul_eq_mul]
        ring

section Field

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} {κ : Rd d → ℝ}
  {a b : ℝ} {H : Rd d → Ω → ℝ}

/-- `E[H x H y] = ⟪k_x, k_y⟫`. -/
theorem integral_mul_eq_inner (hH : IsBandVersion P W κ a b H) (hW : IsWhiteNoise P W)
    (x y : Rd d) : ∫ ω, H x ω * H y ω ∂P = ⟪bandVec κ a b x, bandVec κ a b y⟫ := by
  rw [← hW.cov_eq]
  unfold covariance
  rw [hW.integral_eq_zero, hW.integral_eq_zero]
  simp only [sub_zero]
  refine integral_congr_ae ?_
  filter_upwards [hH.ae_eq x, hH.ae_eq y] with ω h1 h2
  rw [h1, h2]

/-- **Second moment of the root average** (HA3 D3 (a)): for a continuous version `H` of
`H_{a,b}` (`0 < a ≤ b`) and a support radius `ρ` of `κ`, the segment average
`X = ⟨H, ν_{[0,e₁]}⟩` satisfies `X² ∈ L¹(P)` and `E X² ≤ 4ρ(b - a)`. -/
theorem integral_segAvg_sq_le [NeZero d] (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    (ha : 0 < a) (hab : a ≤ b) (hH : IsBandVersion P W κ a b H) {ρ : ℝ}
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) :
    Integrable (fun ω => Upper.segAvg (fun z => H z ω) 0 (e₁ d) ^ 2) P ∧
      ∫ ω, Upper.segAvg (fun z => H z ω) 0 (e₁ d) ^ 2 ∂P ≤ 4 * ρ * (b - a) := by
  have := hW.isProbabilityMeasure
  set μ₁ : Measure ℝ := (volume : Measure ℝ).restrict (Ioc 0 1) with hμ₁
  set F : Ω × (ℝ × ℝ) → ℝ := fun q => H (q.2.1 • e₁ d) q.1 * H (q.2.2 • e₁ d) q.1 with hF
  have hHm := hH.measurable_uncurry
  have hF1 : Measurable fun q : Ω × (ℝ × ℝ) => H (q.2.1 • e₁ d) q.1 :=
    hHm.comp ((measurable_snd.fst.smul_const (e₁ d)).prodMk measurable_fst)
  have hF2 : Measurable fun q : Ω × (ℝ × ℝ) => H (q.2.2 • e₁ d) q.1 :=
    hHm.comp ((measurable_snd.snd.smul_const (e₁ d)).prodMk measurable_fst)
  have hFm : Measurable F := hF1.mul hF2
  have hsq : ∀ x : Rd d, ∫ ω, H x ω ^ 2 ∂P = Real.log (b / a) := fun x => by
    have h := integral_mul_eq_inner hH hW x x
    rw [real_inner_self_eq_norm_sq, norm_bandVec_sq hκ ha hab] at h
    simpa only [sq] using h
  have hbound : ∀ p : ℝ × ℝ, ∫ ω, ‖F (ω, p)‖ ∂P ≤ Real.log (b / a) := fun p => by
    have hx := (Osc.memLp_two_of_isBandVersion hH hW (p.1 • e₁ d)).integrable_sq
    have hy := (Osc.memLp_two_of_isBandVersion hH hW (p.2 • e₁ d)).integrable_sq
    calc ∫ ω, ‖F (ω, p)‖ ∂P
        ≤ ∫ ω, (H (p.1 • e₁ d) ω ^ 2 + H (p.2 • e₁ d) ω ^ 2) / 2 ∂P := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _)
            ((hx.add hy).div_const 2) (Eventually.of_forall fun ω => ?_)
          show ‖H (p.1 • e₁ d) ω * H (p.2 • e₁ d) ω‖ ≤
            (H (p.1 • e₁ d) ω ^ 2 + H (p.2 • e₁ d) ω ^ 2) / 2
          rw [Real.norm_eq_abs, abs_mul]
          nlinarith [sq_nonneg (|H (p.1 • e₁ d) ω| - |H (p.2 • e₁ d) ω|),
            sq_abs (H (p.1 • e₁ d) ω), sq_abs (H (p.2 • e₁ d) ω)]
      _ = Real.log (b / a) := by
          rw [integral_div, integral_add hx hy, hsq, hsq]
          ring
  have hFint : Integrable F (P.prod (μ₁.prod μ₁)) := by
    refine (integrable_prod_iff' hFm.aestronglyMeasurable).2
      ⟨Eventually.of_forall fun p => ?_, ?_⟩
    · exact (Osc.memLp_two_of_isBandVersion hH hW (p.1 • e₁ d)).integrable_mul
        (Osc.memLp_two_of_isBandVersion hH hW (p.2 • e₁ d))
    · refine Integrable.of_bound ?_ (Real.log (b / a)) (Eventually.of_forall fun p => ?_)
      · exact (StronglyMeasurable.integral_prod_left (f := fun ω p => ‖F (ω, p)‖)
          hFm.norm.stronglyMeasurable).aestronglyMeasurable
      · rw [Real.norm_of_nonneg (integral_nonneg fun ω => norm_nonneg _)]
        exact hbound p
  have hsqpath : ∀ ω, Upper.segAvg (fun z => H z ω) 0 (e₁ d) ^ 2 =
      ∫ p, F (ω, p) ∂(μ₁.prod μ₁) := fun ω => by
    rw [segAvg_zero_e₁, sq, ← integral_prod_mul]
  have hint : Integrable (fun ω => Upper.segAvg (fun z => H z ω) 0 (e₁ d) ^ 2) P := by
    simp_rw [hsqpath]
    exact hFint.integral_prod_left
  refine ⟨hint, ?_⟩
  set g : ℝ × ℝ → ℝ := fun p => ⟪bandVec κ a b (p.1 • e₁ d), bandVec κ a b (p.2 • e₁ d)⟫
    with hg
  have hgF : ∀ p, ∫ ω, F (ω, p) ∂P = g p := fun p =>
    integral_mul_eq_inner hH hW (p.1 • e₁ d) (p.2 • e₁ d)
  have hgint : Integrable g (μ₁.prod μ₁) := by
    have h := hFint.integral_prod_right
    simp_rw [hgF] at h
    exact h
  have hμ₁univ : μ₁.real univ = 1 := by
    rw [hμ₁, measureReal_restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_real_Ioc_of_le zero_le_one, sub_zero]
  calc ∫ ω, Upper.segAvg (fun z => H z ω) 0 (e₁ d) ^ 2 ∂P
      = ∫ ω, ∫ p, F (ω, p) ∂(μ₁.prod μ₁) ∂P := by simp_rw [hsqpath]
    _ = ∫ p, ∫ ω, F (ω, p) ∂P ∂(μ₁.prod μ₁) :=
        integral_integral_swap (f := fun ω p => F (ω, p)) hFint
    _ = ∫ p, g p ∂(μ₁.prod μ₁) := by simp_rw [hgF]
    _ = ∫ s, ∫ s', g (s, s') ∂μ₁ ∂μ₁ := integral_prod g hgint
    _ ≤ ∫ _s, 4 * ρ * (b - a) ∂μ₁ :=
        integral_mono hgint.integral_prod_left (integrable_const _)
          fun s => integral_inner_bandVec_le hκ hρ ha hab s
    _ = 4 * ρ * (b - a) := by rw [integral_const, hμ₁univ, one_smul]

/-- The root average of a version is a random variable (versions are jointly measurable). -/
theorem aestronglyMeasurable_segAvg (hH : IsBandVersion P W κ a b H) :
    AEStronglyMeasurable (fun ω => Upper.segAvg (fun z => H z ω) 0 (e₁ d)) P := by
  have hm : Measurable fun q : Ω × ℝ => H (q.2 • e₁ d) q.1 :=
    hH.measurable_uncurry.comp ((measurable_snd.smul_const (e₁ d)).prodMk measurable_fst)
  have h := (StronglyMeasurable.integral_prod_right (ν := (volume : Measure ℝ).restrict (Ioc 0 1))
    (f := fun ω (s : ℝ) => H (s • e₁ d) ω) hm.stronglyMeasurable).aestronglyMeasurable (μ := P)
  simp_rw [segAvg_zero_e₁]
  exact h

/-- **Variance of the root average** (HA3 D3 (a)): `Var ⟨H, ν_{[0,e₁]}⟩ ≤ 4ρ(b - a)`. -/
theorem variance_segAvg_le [NeZero d] (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    (ha : 0 < a) (hab : a ≤ b) (hH : IsBandVersion P W κ a b H) {ρ : ℝ}
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) :
    Var[fun ω => Upper.segAvg (fun z => H z ω) 0 (e₁ d); P] ≤ 4 * ρ * (b - a) := by
  have := hW.isProbabilityMeasure
  exact (variance_le_expectation_sq (aestronglyMeasurable_segAvg hH)).trans
    (integral_segAvg_sq_le hκ hW ha hab hH hρ).2

/-- **Chebyshev for the root average**: `P*(M < |⟨H, ν_{[0,e₁]}⟩|) ≤ 4ρ(b - a)/M²`. -/
theorem segAvg_tail_le [NeZero d] (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    (ha : 0 < a) (hab : a ≤ b) (hH : IsBandVersion P W κ a b H) {ρ : ℝ}
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {M : ℝ} (hM : 0 < M) :
    P {ω | M < |Upper.segAvg (fun z => H z ω) 0 (e₁ d)|} ≤
      ENNReal.ofReal (4 * ρ * (b - a) / M ^ 2) := by
  have := hW.isProbabilityMeasure
  obtain ⟨hint, hle⟩ := integral_segAvg_sq_le hκ hW ha hab hH hρ
  set X : Ω → ℝ := fun ω => Upper.segAvg (fun z => H z ω) 0 (e₁ d) with hX
  have hsub : {ω | M < |X ω|} ⊆ {ω | M ^ 2 ≤ X ω ^ 2} := fun ω hω => by
    have h : M ^ 2 ≤ |X ω| ^ 2 := pow_le_pow_left₀ hM.le (le_of_lt hω) 2
    rwa [sq_abs] at h
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ω => X ω ^ 2)
    (Eventually.of_forall fun ω => sq_nonneg _) hint (M ^ 2)
  have hreal : P.real {ω | M ^ 2 ≤ X ω ^ 2} ≤ 4 * ρ * (b - a) / M ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  calc P {ω | M < |X ω|} ≤ P {ω | M ^ 2 ≤ X ω ^ 2} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | M ^ 2 ≤ X ω ^ 2}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (4 * ρ * (b - a) / M ^ 2) := ENNReal.ofReal_le_ofReal hreal

end Field

end RootAvg

open RootAvg

variable {d : ℕ} [NeZero d] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
  {κ : Rd d → ℝ}

/-- **Target T2, variance** (HA3 D3 (a)): for continuous versions `H ε` of `H_{ε,1}` and a
support radius `ρ` of `κ`, `Var ⟨H ε, ν_{[0,e₁]}⟩ ≤ 4ρ` for every `ε ∈ (0,1)`. -/
theorem segAvg_cutoff_variance_le (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    {H : ℝ → Rd d → Ω → ℝ} (hH : ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) {ρ : ℝ}
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) :
    Var[fun ω => Upper.segAvg (fun z => H ε z ω) 0 (e₁ d); P] ≤ 4 * ρ := by
  have hρ0 := radius_nonneg hκ hρ
  refine (variance_segAvg_le hκ hW hε.1 hε.2.le (hH ε hε) hρ).trans ?_
  nlinarith [hε.1]

/-- **Target T2, tail** (HA3 D3 (a)): `P*(|⟨H ε, ν_{[0,e₁]}⟩| > M) ≤ 4ρ/M²` for every
`ε ∈ (0,1)` and `M > 0`. -/
theorem segAvg_cutoff_tail_le (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    {H : ℝ → Rd d → Ω → ℝ} (hH : ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) {ρ : ℝ}
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) {M : ℝ} (hM : 0 < M) :
    P {ω | M < |Upper.segAvg (fun z => H ε z ω) 0 (e₁ d)|} ≤ ENNReal.ofReal (4 * ρ / M ^ 2) := by
  have hρ0 := radius_nonneg hκ hρ
  refine (segAvg_tail_le hκ hW hε.1 hε.2.le (hH ε hε) hρ hM).trans (ENNReal.ofReal_le_ofReal ?_)
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  nlinarith [hε.1]

/-- **Target T2** in the form of HA3's `OscillationBound` (second conjunct): `H_root = O_P(1)`
uniformly in `ε ∈ (0,1)`. -/
theorem segAvg_cutoff_bounded (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    {H : ℝ → Rd d → Ω → ℝ} (hH : ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε))
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ M : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
      P {ω | M < |Upper.segAvg (fun z => H ε z ω) 0 (e₁ d)|} ≤ ENNReal.ofReal θ := by
  obtain ⟨ρ, hρpos, hρ⟩ := hκ.exists_radius
  refine ⟨√(4 * ρ / θ) + 1, fun ε hε => ?_⟩
  have hM : 0 < √(4 * ρ / θ) + 1 := by positivity
  refine (segAvg_cutoff_tail_le hκ hW hH hρ hε hM).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [div_le_iff₀ (by positivity)]
  have h1 : 4 * ρ / θ ≤ (√(4 * ρ / θ) + 1) ^ 2 := by
    have h2 : (√(4 * ρ / θ)) ^ 2 = 4 * ρ / θ := Real.sq_sqrt (by positivity)
    nlinarith [Real.sqrt_nonneg (4 * ρ / θ)]
  rw [div_le_iff₀ hθ] at h1
  linarith

end HigherDimLFPP
