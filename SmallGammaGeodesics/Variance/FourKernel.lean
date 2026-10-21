import SmallGammaGeodesics.Variance.KernelBounds
import GaussianLQG.Energy.SegmentsBasic

/-!
# The four-kernel lemma and Corollary (5.5) (packet P-A4)

Source: `source/small-parameter-lqg-geodesics.pdf`, §3, Lemma 3.1 and its proof ("four-kernel"
argument), and §5, display (5.5). Mathematics: planning audit GA2, "Details for later use", D1
(Lemma FK and its Corollary), with the statement of GA2 Details (c).

Notation: `λ = segMeasure 0 1`, `μ = pathMeasure P = P_* Leb|_{[0,1]}`,
`‖ν - ν'‖_G² = energyDistSq ν ν' = ℰ(ν,ν) - 2ℰ(ν,ν') + ℰ(ν',ν')` (GaussianLQG `energy`).

* `fourKernel` (**Lemma FK**, GA2 (c) verbatim): if `P` is continuous, `|P(t) - t| ≤ r ≤ 1` on
  `[0,1]` and `μ(B_u(z)) ≤ min{A u^s, c₁ u + c₂ Δ}` for `0 < u ≤ 1`, then `μ` is regular and
  `‖μ - λ‖_G² ≤ (4 + 16 log 5 + c₁) r + (c₂Δ/s)(1 + log⁺ A + log⁺(1/(c₂Δ)))`.
* `energyDistSq_pathMeasure_le`: the same with the sharper constant `2 + 16 log 2 + 17π/8 + c₁`
  and only measurability of `P` (used for Lemma 3.1′).
* `fourKernel_of_lipschitz` (**Corollary (5.5)**): `Δ = 0`, `c₂ = 0`, `s = 1`.
* `fourKernel_of_coLipschitz`, `fourKernel_of_coLipschitz_real`: the same for a (complex- or
  real-valued) path, continuous on `[0,1]` with a lower Lipschitz bound `|t - t'| ≤ K |P t - P t'|`
  (e.g. bi-Lipschitz, such as `ϕ⁻¹` in §5); then `c₁ = max 1 (2K)`.

Proof (GA2 D1, with the far- and near-region estimates obtained from the cross-ratio identity, see
`fourKernel_pointwise`): `energy_sub_eq_logEnergy` writes `‖μ - λ‖_G²` as the four logarithmic
energies; all four are integrals over `[0,1]²` of `-log|·-·|` composed with `P` and `t ↦ t`
(`logEnergy_pathMeasure_eq`), so `‖μ - λ‖_G² = ∬ Φ` with
`Φ(t,v) = K(P t, P v) - K(P t, v) - K(t, P v) + K(t, v)`. The pointwise bound integrates to
`16 r log 2` (near band, area `≤ 8r`), `(17/8) π r` (far kernel), `c₁ r + (c₂Δ/s)(…)` (layer cake
for `μ`) and `2r` (layer cake for `λ`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal Real

namespace SmallGammaGeodesics

open GaussianLQG

/-- `‖ν - ν'‖_G² = ℰ(ν,ν) - 2ℰ(ν,ν') + ℰ(ν',ν')` (formal difference, GaussianLQG `energy`). -/
def energyDistSq (ν ν' : Measure ℂ) : ℝ :=
  energy ν ν - 2 * energy ν ν' + energy ν' ν'

/-- The occupation measure `P_* Leb|_{[0,1]}` of a path `P : ℝ → ℂ`. -/
def pathMeasure (P : ℝ → ℂ) : Measure ℂ := (volume.restrict (Icc (0 : ℝ) 1)).map P

/-- Lebesgue measure on `[0,1]`. -/
local notation "Leb01" => (volume.restrict (Icc (0 : ℝ) 1) : Measure ℝ)

/-- Lebesgue measure on `[0,1]²`. -/
local notation "Leb2" =>
  (Measure.prod (volume.restrict (Icc (0 : ℝ) 1)) (volume.restrict (Icc (0 : ℝ) 1)) :
    Measure (ℝ × ℝ))

/-! ## Basic API -/

theorem energyDistSq_self (ν : Measure ℂ) : energyDistSq ν ν = 0 := by
  unfold energyDistSq
  ring

instance isProbabilityMeasure_pathMeasure (P : ℝ → ℂ) : IsProbabilityMeasure (pathMeasure P) := by
  unfold pathMeasure
  infer_instance

theorem pathMeasure_apply {P : ℝ → ℂ} (hP : Measurable P) {S : Set ℂ} (hS : MeasurableSet S) :
    pathMeasure P S = volume (P ⁻¹' S ∩ Icc 0 1) := by
  unfold pathMeasure
  rw [Measure.map_apply hP hS, Measure.restrict_apply (hP hS)]

/-- The path measure only depends on the path on `[0,1]`. -/
theorem pathMeasure_congr {P Q : ℝ → ℂ} (h : ∀ t ∈ Icc (0 : ℝ) 1, P t = Q t) :
    pathMeasure P = pathMeasure Q := by
  unfold pathMeasure
  exact Measure.map_congr ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ h))

/-- `λ_{0,1} = (t ↦ t)_* Leb|_{[0,1]}`. -/
theorem segMeasure_zero_one_eq_pathMeasure : segMeasure 0 1 = pathMeasure Complex.ofReal := by
  rw [segMeasure_eq_map]
  unfold pathMeasure
  congr 1
  funext u
  exact segPath_zero_one u

/-- GaussianLQG's length measure of `η` is the path measure of `t ↦ η(proj t)`. -/
theorem lengthMeasure_eq_pathMeasure (η : C(unitInterval, ℂ)) :
    lengthMeasure η = pathMeasure fun t => η (projIcc 0 1 zero_le_one t) :=
  rfl

/-- A path measure of a measurable path that stays in `B̄_R(0)` on `[0,1]` and satisfies a
power-law ball bound is regular. -/
theorem isRegular_pathMeasure {P : ℝ → ℂ} (hP : Measurable P) {R C α : ℝ} (hα : 0 < α)
    (hR : ∀ t ∈ Icc (0 : ℝ) 1, ‖P t‖ ≤ R)
    (hb : ∀ u : ℂ, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → (pathMeasure P (ball u ρ)).toReal ≤ C * ρ ^ α) :
    IsRegular (pathMeasure P) := by
  refine ⟨inferInstance, ⟨R, ?_⟩, C, α, hα, hb⟩
  rw [pathMeasure_apply hP measurableSet_closedBall.compl]
  have e : P ⁻¹' (closedBall (0 : ℂ) R)ᶜ ∩ Icc 0 1 = ∅ := by
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_closedBall, dist_zero_right,
      mem_empty_iff_false, iff_false, not_and]
    intro h ht
    exact h (hR t ht)
  rw [e, measure_empty]

/-! ## Transfer to `[0,1]²` -/

theorem pathMeasure_prod_eq {f g : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g) :
    (pathMeasure f).prod (pathMeasure g) = Measure.map (Prod.map f g) Leb2 :=
  Measure.map_prod_map _ _ hf hg

theorem integral_pathMeasure_prod {f g : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g)
    {F : ℂ × ℂ → ℝ} (hF : Measurable F) :
    ∫ p, F p ∂((pathMeasure f).prod (pathMeasure g)) =
      ∫ q, F (f q.1, g q.2) ∂Leb2 := by
  rw [pathMeasure_prod_eq hf hg,
    integral_map (hf.prodMap hg).aemeasurable hF.aestronglyMeasurable]
  rfl

theorem integrable_pathMeasure_prod {f g : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g)
    {F : ℂ × ℂ → ℝ} (hF : Measurable F)
    (hi : Integrable F ((pathMeasure f).prod (pathMeasure g))) :
    Integrable (fun q : ℝ × ℝ => F (f q.1, g q.2)) Leb2 := by
  rw [pathMeasure_prod_eq hf hg] at hi
  exact (integrable_map_measure hF.aestronglyMeasurable (hf.prodMap hg).aemeasurable).1 hi

theorem ae_pathMeasure_prod {f g : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g)
    {Q : ℂ × ℂ → Prop} (h : ∀ᵐ p ∂((pathMeasure f).prod (pathMeasure g)), Q p) :
    ∀ᵐ q ∂Leb2, Q (f q.1, g q.2) := by
  rw [pathMeasure_prod_eq hf hg] at h
  exact ae_of_ae_map (hf.prodMap hg).aemeasurable h

/-- `L(f_* Leb, g_* Leb) = ∬_{[0,1]²} -log|f(t) - g(v)| dt dv` for regular path measures. -/
theorem logEnergy_pathMeasure_eq {f g : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hrf : IsRegular (pathMeasure f)) (hrg : IsRegular (pathMeasure g)) :
    logEnergy (pathMeasure f) (pathMeasure g) =
      ∫ q, -Real.log ‖f q.1 - g q.2‖ ∂Leb2 := by
  rw [logEnergy_eq_integral_prod hrf hrg]
  exact integral_pathMeasure_prod hf hg (F := fun p : ℂ × ℂ => -Real.log ‖p.1 - p.2‖)
    (by fun_prop)

theorem integrable_neg_log_pathMeasure {f g : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hrf : IsRegular (pathMeasure f)) (hrg : IsRegular (pathMeasure g)) :
    Integrable (fun q : ℝ × ℝ => -Real.log ‖f q.1 - g q.2‖) Leb2 :=
  integrable_pathMeasure_prod hf hg (F := fun p : ℂ × ℂ => -Real.log ‖p.1 - p.2‖)
    (by fun_prop) (hrf.integrable_neg_log_norm_sub hrg)

/-- **The four-kernel identity.** For regular `μ = P_* Leb` and `λ = λ_{0,1}`,
`‖μ - λ‖_G² = ∬_{[0,1]²} Φ` with `Φ(t,v) = K(P t,P v) - K(P t,v) - K(t,P v) + K(t,v)`,
`K = -log|·-·|`, the integrand being integrable. -/
theorem energyDistSq_pathMeasure_eq {P : ℝ → ℂ} (hP : Measurable P)
    (hreg : IsRegular (pathMeasure P)) :
    Integrable (fun q : ℝ × ℝ => -Real.log ‖P q.1 - P q.2‖ - -Real.log ‖P q.1 - q.2‖ -
        -Real.log ‖(q.1 : ℂ) - P q.2‖ + -Real.log ‖(q.1 : ℂ) - q.2‖) Leb2 ∧
    energyDistSq (pathMeasure P) (segMeasure 0 1) =
      ∫ q, (-Real.log ‖P q.1 - P q.2‖ - -Real.log ‖P q.1 - q.2‖ -
        -Real.log ‖(q.1 : ℂ) - P q.2‖ + -Real.log ‖(q.1 : ℂ) - q.2‖) ∂Leb2 := by
  have hι : Measurable Complex.ofReal := Complex.measurable_ofReal
  have hregS : IsRegular (pathMeasure Complex.ofReal) := by
    rw [← segMeasure_zero_one_eq_pathMeasure]
    exact isRegular_segMeasure zero_ne_one
  have i11 := integrable_neg_log_pathMeasure hP hP hreg hreg
  have i12 := integrable_neg_log_pathMeasure hP hι hreg hregS
  have i21 := integrable_neg_log_pathMeasure hι hP hregS hreg
  have i22 := integrable_neg_log_pathMeasure hι hι hregS hregS
  have i112 : Integrable (fun q : ℝ × ℝ => -Real.log ‖P q.1 - P q.2‖ -
      -Real.log ‖P q.1 - q.2‖) Leb2 := i11.sub i12
  have i1123 : Integrable (fun q : ℝ × ℝ => -Real.log ‖P q.1 - P q.2‖ -
      -Real.log ‖P q.1 - q.2‖ - -Real.log ‖(q.1 : ℂ) - P q.2‖) Leb2 := i112.sub i21
  refine ⟨i1123.add i22, ?_⟩
  have hmass : pathMeasure P univ = pathMeasure Complex.ofReal univ := by
    rw [measure_univ, measure_univ]
  unfold energyDistSq
  rw [segMeasure_zero_one_eq_pathMeasure, energy_sub_eq_logEnergy hreg hregS hmass,
    logEnergy_pathMeasure_eq hP hP hreg hreg, logEnergy_pathMeasure_eq hP hι hreg hregS,
    logEnergy_pathMeasure_eq hι hP hregS hreg, logEnergy_pathMeasure_eq hι hι hregS hregS,
    ← integral_sub i11 i12, ← integral_sub i112 i21, ← integral_add i1123 i22]

/-! ## The four integrals of the pointwise bound -/

/-- The near band `{|t - v| ≤ 4r}` has `Leb ⊗ Leb`-measure at most `8r` in `[0,1]²`. -/
theorem prod_near_band_le (r : ℝ) :
    Leb2 {q : ℝ × ℝ | ‖(q.1 : ℂ) - q.2‖ ≤ 4 * r} ≤ ENNReal.ofReal (8 * r) := by
  have hmeas : MeasurableSet {q : ℝ × ℝ | ‖(q.1 : ℂ) - q.2‖ ≤ 4 * r} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [Measure.prod_apply hmeas]
  calc ∫⁻ t, Leb01 (Prod.mk t ⁻¹' {q : ℝ × ℝ | ‖(q.1 : ℂ) - q.2‖ ≤ 4 * r}) ∂Leb01
      ≤ ∫⁻ _t, ENNReal.ofReal (8 * r) ∂Leb01 := by
        refine lintegral_mono fun t => (Measure.restrict_apply_le _ _).trans ?_
        calc volume (Prod.mk t ⁻¹' {q : ℝ × ℝ | ‖(q.1 : ℂ) - q.2‖ ≤ 4 * r})
            ≤ volume (Icc (t - 4 * r) (t + 4 * r)) := by
              refine measure_mono fun v hv => ?_
              simp only [mem_preimage, mem_ofPred_eq] at hv
              rw [norm_ofReal_sub_ofReal, abs_le] at hv
              exact ⟨by linarith [hv.2], by linarith [hv.1]⟩
          _ = ENNReal.ofReal (8 * r) := by
              rw [Real.volume_Icc]
              congr 1
              ring
    _ = ENNReal.ofReal (8 * r) := by rw [lintegral_const, measure_univ, mul_one]

/-- `∬_{[0,1]²} 1_{|t-v| ≤ 4r} 2 log 2 ≤ 16 r log 2`. -/
theorem integral_near_le {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun q : ℝ × ℝ => if ‖(q.1 : ℂ) - q.2‖ ≤ 4 * r then 2 * Real.log 2 else 0)
        Leb2 ∧
      ∫ q, (if ‖(q.1 : ℂ) - q.2‖ ≤ 4 * r then 2 * Real.log 2 else 0) ∂Leb2 ≤
        16 * Real.log 2 * r := by
  set N := {q : ℝ × ℝ | ‖(q.1 : ℂ) - q.2‖ ≤ 4 * r}
  have hmeas : MeasurableSet N := measurableSet_le (by fun_prop) measurable_const
  have e : (fun q : ℝ × ℝ => if ‖(q.1 : ℂ) - q.2‖ ≤ 4 * r then 2 * Real.log 2 else 0) =
      N.indicator fun _ => 2 * Real.log 2 := by
    funext q
    simp only [indicator, N, mem_ofPred_eq]
  rw [e]
  refine ⟨(integrable_const _).indicator hmeas, ?_⟩
  rw [integral_indicator_const _ hmeas, smul_eq_mul]
  have hN : Measure.real Leb2 N ≤ 8 * r :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) (prod_near_band_le r)
  have hlog : 0 ≤ 2 * Real.log 2 := by positivity
  calc Measure.real Leb2 N * (2 * Real.log 2) ≤ 8 * r * (2 * Real.log 2) :=
        mul_le_mul_of_nonneg_right hN hlog
    _ = 16 * Real.log 2 * r := by ring

/-- `∬_{[0,1]²} (17/8) r²/(r² + (t-v)²) ≤ (17/8) π r`. -/
theorem integral_far_le {r : ℝ} (hr : 0 < r) :
    Integrable (fun q : ℝ × ℝ => 17 / 8 * (r ^ 2 / (r ^ 2 + ‖(q.1 : ℂ) - q.2‖ ^ 2)))
        Leb2 ∧
      ∫ q, 17 / 8 * (r ^ 2 / (r ^ 2 + ‖(q.1 : ℂ) - q.2‖ ^ 2)) ∂Leb2 ≤
        17 / 8 * π * r := by
  have hmeas : Measurable fun q : ℝ × ℝ => 17 / 8 * (r ^ 2 / (r ^ 2 + ‖(q.1 : ℂ) - q.2‖ ^ 2)) := by
    fun_prop
  have hint : Integrable (fun q : ℝ × ℝ => 17 / 8 * (r ^ 2 / (r ^ 2 + ‖(q.1 : ℂ) - q.2‖ ^ 2)))
      Leb2 := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable (17 / 8) (ae_of_all _ fun q => ?_)
    have h0 : 0 ≤ r ^ 2 / (r ^ 2 + ‖(q.1 : ℂ) - q.2‖ ^ 2) := by positivity
    have h1 : r ^ 2 / (r ^ 2 + ‖(q.1 : ℂ) - q.2‖ ^ 2) ≤ 1 :=
      (div_le_one (by positivity)).2 (by nlinarith [sq_nonneg ‖(q.1 : ℂ) - q.2‖])
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith
  refine ⟨hint, ?_⟩
  rw [integral_prod _ hint]
  calc ∫ t, ∫ v, 17 / 8 * (r ^ 2 / (r ^ 2 + ‖(t : ℂ) - v‖ ^ 2)) ∂Leb01 ∂Leb01
      ≤ ∫ _t, 17 / 8 * π * r ∂Leb01 := by
        refine integral_mono hint.integral_prod_left (integrable_const _) fun t => ?_
        simp only [norm_ofReal_sub_ofReal, sq_abs]
        rw [integral_const_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left (integral_far_kernel_le t hr) (by norm_num)
    _ = 17 / 8 * π * r := by rw [integral_const, probReal_univ, one_smul]

/-- `∬_{[0,1]²} log⁺(r/|P t - P v|) ≤ c₁ r + (c₂Δ/s)(1 + log⁺ A + log⁺(1/(c₂Δ)))` from the ball
bound `μ(B_u(z)) ≤ min{A u^s, c₁ u + c₂ Δ}` (layer cake, GA2 D1 step 3 (iii)). -/
theorem integral_posLog_path_le {P : ℝ → ℂ} (hP : Measurable P) (hreg : IsRegular (pathMeasure P))
    {r A s c₁ c₂ Δ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hA : 0 ≤ A) (hs : 0 < s) (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) (hΔ : 0 ≤ Δ)
    (hball : ∀ z : ℂ, ∀ u : ℝ, 0 < u → u ≤ 1 →
      ((pathMeasure P) (ball z u)).toReal ≤ min (A * u ^ s) (c₁ * u + c₂ * Δ)) :
    Integrable (fun q : ℝ × ℝ => log⁺ (r / ‖P q.1 - P q.2‖)) Leb2 ∧
      ∫ q, log⁺ (r / ‖P q.1 - P q.2‖) ∂Leb2 ≤
        c₁ * r + c₂ * Δ / s * (1 + log⁺ A + log⁺ (1 / (c₂ * Δ))) := by
  have hF : Measurable fun p : ℂ × ℂ => log⁺ (r / ‖p.1 - p.2‖) := by fun_prop
  refine ⟨integrable_pathMeasure_prod hP hP hF (hreg.integrable_posLog_div hreg hr hr1), ?_⟩
  rw [← integral_pathMeasure_prod hP hP hF]
  have hnn : 0 ≤ᵐ[(pathMeasure P).prod (pathMeasure P)]
      fun p : ℂ × ℂ => log⁺ (r / ‖p.1 - p.2‖) := ae_of_all _ fun p => Real.posLog_nonneg
  rw [integral_eq_lintegral_of_nonneg_ae hnn hF.aestronglyMeasurable]
  have hlin := lintegral_prod_le_of_forall (μ := pathMeasure P) (ν := pathMeasure P)
    (f := fun p : ℂ × ℂ => ENNReal.ofReal (log⁺ (r / ‖p.1 - p.2‖))) (by fun_prop)
    fun z => lintegral_posLog_div_le_of_minBound (pathMeasure P) z hr hr1 hA hs hc₁
      (mul_nonneg hc₂ hΔ) (hball z)
  rw [measure_univ, one_mul] at hlin
  have hX : 0 ≤ c₂ * Δ / s * (1 + log⁺ A + log⁺ (1 / (c₂ * Δ))) := by
    have : 0 ≤ 1 + log⁺ A + log⁺ (1 / (c₂ * Δ)) := by
      linarith [Real.posLog_nonneg (x := A), Real.posLog_nonneg (x := 1 / (c₂ * Δ))]
    exact mul_nonneg (div_nonneg (mul_nonneg hc₂ hΔ) hs.le) this
  calc (∫⁻ p, ENNReal.ofReal (log⁺ (r / ‖p.1 - p.2‖))
        ∂((pathMeasure P).prod (pathMeasure P))).toReal
      ≤ (ENNReal.ofReal (c₁ * r) +
          ENNReal.ofReal (c₂ * Δ / s * (1 + log⁺ A + log⁺ (1 / (c₂ * Δ))))).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
          hlin
    _ = c₁ * r + c₂ * Δ / s * (1 + log⁺ A + log⁺ (1 / (c₂ * Δ))) := by
        rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
          ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hX]

/-- `∬_{[0,1]²} log⁺(r/|t - v|) ≤ 2r` (layer cake for `λ_{0,1}`, `λ(B_ρ) ≤ 2ρ`). -/
theorem integral_posLog_seg_le {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Integrable (fun q : ℝ × ℝ => log⁺ (r / ‖(q.1 : ℂ) - q.2‖)) Leb2 ∧
      ∫ q, log⁺ (r / ‖(q.1 : ℂ) - q.2‖) ∂Leb2 ≤ 2 * r := by
  have hι : Measurable Complex.ofReal := Complex.measurable_ofReal
  have hF : Measurable fun p : ℂ × ℂ => log⁺ (r / ‖p.1 - p.2‖) := by fun_prop
  have hball : ∀ u : ℂ, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      segMeasure 0 1 (ball u ρ) ≤ ENNReal.ofReal (2 * ρ ^ (1 : ℝ)) := by
    intro u ρ _ _
    refine (segMeasure_ball_le zero_ne_one u ρ).trans (le_of_eq ?_)
    rw [Real.rpow_one, show ‖(0 : ℂ) - 1‖ = 1 by norm_num, div_one]
  obtain ⟨hi, hle⟩ := integrable_posLog_div_prod (μ := segMeasure 0 1) (ν := segMeasure 0 1)
    hr hr1 one_pos (by norm_num : (0 : ℝ) ≤ 2) hball
  rw [segMeasure_zero_one_eq_pathMeasure] at hi hle
  refine ⟨integrable_pathMeasure_prod hι hι hF hi, ?_⟩
  rw [← integral_pathMeasure_prod hι hι hF]
  rw [probReal_univ, Real.rpow_one, div_one, one_mul] at hle
  exact hle

/-! ## The four-kernel lemma -/

/-- **Four-kernel lemma, sharp form** (GA2 D1, Lemma FK, with only measurability of `P`):
`‖μ - λ‖_G² ≤ (2 + 16 log 2 + 17π/8 + c₁) r + (c₂Δ/s)(1 + log⁺ A + log⁺(1/(c₂Δ)))`. -/
theorem energyDistSq_pathMeasure_le {P : ℝ → ℂ} (hP : Measurable P)
    (hreg : IsRegular (pathMeasure P)) {r A s c₁ c₂ Δ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hA : 0 ≤ A) (hs : 0 < s) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hΔ : 0 ≤ Δ)
    (hdisp : ∀ t ∈ Icc (0 : ℝ) 1, ‖P t - t‖ ≤ r)
    (hball : ∀ z : ℂ, ∀ u : ℝ, 0 < u → u ≤ 1 →
      ((pathMeasure P) (ball z u)).toReal ≤ min (A * u ^ s) (c₁ * u + c₂ * Δ)) :
    energyDistSq (pathMeasure P) (segMeasure 0 1) ≤
      (2 + 16 * Real.log 2 + 17 / 8 * π + c₁) * r +
        c₂ * Δ / s * (1 + log⁺ A + log⁺ (1 / (c₂ * Δ))) := by
  have hι : Measurable Complex.ofReal := Complex.measurable_ofReal
  have hregS : IsRegular (pathMeasure Complex.ofReal) := by
    rw [← segMeasure_zero_one_eq_pathMeasure]
    exact isRegular_segMeasure zero_ne_one
  obtain ⟨hΦint, hΦ⟩ := energyDistSq_pathMeasure_eq hP hreg
  obtain ⟨i1, I1⟩ := integral_near_le hr.le
  obtain ⟨i2, I2⟩ := integral_far_le hr
  obtain ⟨i3, I3⟩ := integral_posLog_path_le hP hreg hr hr1 hA hs hc₁ hc₂ hΔ hball
  obtain ⟨i4, I4⟩ := integral_posLog_seg_le hr hr1
  -- the pointwise bound, a.e. on `[0,1]²`
  have hae : ∀ᵐ q ∂Leb2,
      -Real.log ‖P q.1 - P q.2‖ - -Real.log ‖P q.1 - q.2‖ - -Real.log ‖(q.1 : ℂ) - P q.2‖ +
          -Real.log ‖(q.1 : ℂ) - q.2‖ ≤
        (if ‖(q.1 : ℂ) - q.2‖ ≤ 4 * r then 2 * Real.log 2 else 0) +
          17 / 8 * (r ^ 2 / (r ^ 2 + ‖(q.1 : ℂ) - q.2‖ ^ 2)) + log⁺ (r / ‖P q.1 - P q.2‖) +
            log⁺ (r / ‖(q.1 : ℂ) - q.2‖) := by
    filter_upwards [ae_mem_Icc_prod,
      ae_pathMeasure_prod hP hP (hreg.ae_prod_ne (μ := pathMeasure P)),
      ae_pathMeasure_prod hP hι (hregS.ae_prod_ne (μ := pathMeasure P)),
      ae_pathMeasure_prod hι hP (hreg.ae_prod_ne (μ := pathMeasure Complex.ofReal)),
      ae_pathMeasure_prod hι hι (hregS.ae_prod_ne (μ := pathMeasure Complex.ofReal))]
      with q hq h1 h2 h3 h4
    exact fourKernel_pointwise hr h1 h2 h3 h4 (hdisp q.1 hq.1) (hdisp q.2 hq.2)
  have i12 : Integrable (fun q : ℝ × ℝ =>
      (if ‖(q.1 : ℂ) - q.2‖ ≤ 4 * r then 2 * Real.log 2 else 0) +
        17 / 8 * (r ^ 2 / (r ^ 2 + ‖(q.1 : ℂ) - q.2‖ ^ 2))) Leb2 := i1.add i2
  have i123 : Integrable (fun q : ℝ × ℝ =>
      (if ‖(q.1 : ℂ) - q.2‖ ≤ 4 * r then 2 * Real.log 2 else 0) +
        17 / 8 * (r ^ 2 / (r ^ 2 + ‖(q.1 : ℂ) - q.2‖ ^ 2)) + log⁺ (r / ‖P q.1 - P q.2‖)) Leb2 :=
    i12.add i3
  rw [hΦ]
  calc ∫ q, (-Real.log ‖P q.1 - P q.2‖ - -Real.log ‖P q.1 - q.2‖ -
          -Real.log ‖(q.1 : ℂ) - P q.2‖ + -Real.log ‖(q.1 : ℂ) - q.2‖) ∂Leb2
      ≤ ∫ q, ((if ‖(q.1 : ℂ) - q.2‖ ≤ 4 * r then 2 * Real.log 2 else 0) +
          17 / 8 * (r ^ 2 / (r ^ 2 + ‖(q.1 : ℂ) - q.2‖ ^ 2)) + log⁺ (r / ‖P q.1 - P q.2‖) +
            log⁺ (r / ‖(q.1 : ℂ) - q.2‖)) ∂Leb2 :=
        integral_mono_ae hΦint (i123.add i4) hae
    _ = (∫ q, (if ‖(q.1 : ℂ) - q.2‖ ≤ 4 * r then 2 * Real.log 2 else 0) ∂Leb2) +
          (∫ q, 17 / 8 * (r ^ 2 / (r ^ 2 + ‖(q.1 : ℂ) - q.2‖ ^ 2)) ∂Leb2) +
          (∫ q, log⁺ (r / ‖P q.1 - P q.2‖) ∂Leb2) +
          ∫ q, log⁺ (r / ‖(q.1 : ℂ) - q.2‖) ∂Leb2 := by
        rw [integral_add i123 i4, integral_add i12 i3, integral_add i1 i2]
    _ ≤ 16 * Real.log 2 * r + 17 / 8 * π * r +
          (c₁ * r + c₂ * Δ / s * (1 + log⁺ A + log⁺ (1 / (c₂ * Δ)))) + 2 * r := by
        gcongr
    _ = (2 + 16 * Real.log 2 + 17 / 8 * π + c₁) * r +
          c₂ * Δ / s * (1 + log⁺ A + log⁺ (1 / (c₂ * Δ))) := by ring

/-- `2 + 16 log 2 + 17π/8 ≤ 4 + 16 log 5` (`π ≤ 4` and `log(5/2) ≥ 1 - 2/5`). -/
theorem fourKernel_const_le : 2 + 16 * Real.log 2 + 17 / 8 * π ≤ 4 + 16 * Real.log 5 := by
  have hπ := Real.pi_le_four
  have hlog : (3 : ℝ) / 5 ≤ Real.log 5 - Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have := Real.one_sub_inv_le_log_of_pos (x := 5 / 2) (by norm_num)
    norm_num at this ⊢
    linarith
  linarith

/-- **Four-kernel lemma (GA2 D1, Lemma FK; GA2 Details (c), verbatim).** Deterministic.
Let `P` be continuous with `|P(t) - t| ≤ r ≤ 1` on `[0,1]`, and let `μ = P_* Leb|_{[0,1]}` satisfy
`μ(B_u(z)) ≤ min{A u^s, c₁ u + c₂ Δ}` for all `z` and `0 < u ≤ 1`. Then `μ` is regular and
`‖μ - λ‖_G² ≤ (4 + 16 log 5 + c₁) r + (c₂Δ/s)(1 + log⁺ A + log⁺(1/(c₂Δ)))`
(the last term is `0` when `c₂Δ = 0`). -/
theorem fourKernel :
    ∀ (P : ℝ → ℂ) (r A s c₁ c₂ Δ : ℝ), Continuous P → 0 < r → r ≤ 1 → 0 < A → 0 < s → s ≤ 1 →
      1 ≤ c₁ → 0 ≤ c₂ → 0 ≤ Δ →
      (∀ t ∈ Icc (0 : ℝ) 1, ‖P t - t‖ ≤ r) →
      (∀ z : ℂ, ∀ u : ℝ, 0 < u → u ≤ 1 →
        ((pathMeasure P) (ball z u)).toReal ≤ min (A * u ^ s) (c₁ * u + c₂ * Δ)) →
      IsRegular (pathMeasure P) ∧
        energyDistSq (pathMeasure P) (segMeasure 0 1) ≤
          (4 + 16 * Real.log 5 + c₁) * r + c₂ * Δ / s * (1 + log⁺ A + log⁺ (1 / (c₂ * Δ))) := by
  intro P r A s c₁ c₂ Δ hP hr hr1 hA hs _ hc₁ hc₂ hΔ hdisp hball
  have hreg : IsRegular (pathMeasure P) := by
    refine isRegular_pathMeasure hP.measurable (R := r + 1) hs (fun t ht => ?_)
      fun u ρ hρ hρ1 => (hball u ρ hρ hρ1).trans (min_le_left _ _)
    calc ‖P t‖ = ‖(P t - t) + (t : ℂ)‖ := by rw [sub_add_cancel]
      _ ≤ ‖P t - t‖ + ‖(t : ℂ)‖ := norm_add_le _ _
      _ ≤ r + 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
          linarith [hdisp t ht, ht.2]
  refine ⟨hreg, ?_⟩
  refine (energyDistSq_pathMeasure_le hP.measurable hreg hr hr1 hA.le hs (by linarith) hc₂ hΔ
    hdisp hball).trans ?_
  have hc : 2 + 16 * Real.log 2 + 17 / 8 * π + c₁ ≤ 4 + 16 * Real.log 5 + c₁ := by
    linarith [fourKernel_const_le]
  have := mul_le_mul_of_nonneg_right hc hr.le
  linarith

/-! ## Corollary (5.5) -/

/-- **Corollary (5.5)** (GA2 D1, Corollary): the four-kernel lemma with `Δ = 0`, `c₂ = 0`,
`s = 1`. If `P` is continuous, `|P(t) - t| ≤ r ≤ 1` on `[0,1]` and `μ(B_u(z)) ≤ c₁ u` for
`0 < u ≤ 1`, then `μ` is regular and `‖μ - λ‖_G² ≤ (4 + 16 log 5 + c₁) r`. -/
theorem fourKernel_of_lipschitz (P : ℝ → ℂ) (r c₁ : ℝ) (hP : Continuous P) (hr : 0 < r)
    (hr1 : r ≤ 1) (hc₁ : 1 ≤ c₁) (hdisp : ∀ t ∈ Icc (0 : ℝ) 1, ‖P t - t‖ ≤ r)
    (hball : ∀ z : ℂ, ∀ u : ℝ, 0 < u → u ≤ 1 → ((pathMeasure P) (ball z u)).toReal ≤ c₁ * u) :
    IsRegular (pathMeasure P) ∧
      energyDistSq (pathMeasure P) (segMeasure 0 1) ≤ (4 + 16 * Real.log 5 + c₁) * r := by
  have h := fourKernel P r c₁ 1 c₁ 0 0 hP hr hr1 (by linarith) one_pos le_rfl hc₁ le_rfl le_rfl
    hdisp fun z u hu hu1 => by
      rw [Real.rpow_one, mul_zero, add_zero, min_self]
      exact hball z u hu hu1
  rw [mul_zero, zero_div, zero_mul, add_zero] at h
  exact h

/-- Ball bound for the path measure of a path with a lower Lipschitz bound on `[0,1]`:
`μ(B_u(z)) ≤ 2 K u` when `|t - t'| ≤ K |P t - P t'|` on `[0,1]` (the preimage of `B_u(z)` has
diameter at most `2Ku`). -/
theorem pathMeasure_ball_le_of_coLipschitz {P : ℝ → ℂ} (hP : Measurable P) {K : ℝ} (hK : 0 ≤ K)
    (hlow : ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, |t - t'| ≤ K * ‖P t - P t'‖) (z : ℂ)
    {u : ℝ} (hu : 0 ≤ u) : (pathMeasure P (ball z u)).toReal ≤ 2 * K * u := by
  rw [pathMeasure_apply hP measurableSet_ball]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  refine (Real.volume_le_diam _).trans (Metric.ediam_le_of_forall_dist_le fun t ht t' ht' => ?_)
  rw [Real.dist_eq]
  have h2 : ‖P t - P t'‖ ≤ 2 * u := by
    have a : dist (P t) z < u := ht.1
    have b : dist (P t') z < u := ht'.1
    rw [← dist_eq_norm]
    linarith [dist_triangle_right (P t) (P t') z]
  calc |t - t'| ≤ K * ‖P t - P t'‖ := hlow t ht.2 t' ht'.2
    _ ≤ K * (2 * u) := mul_le_mul_of_nonneg_left h2 hK
    _ = 2 * K * u := by ring

/-- **Corollary (5.5), co-Lipschitz form** (GA2 D1, Corollary; GA3 A4, steps 1–2). Let
`P : ℝ → ℂ` be continuous on `[0,1]` with `|P(t) - t| ≤ r ≤ 1` and `|t - t'| ≤ K |P t - P t'|`
for `t, t' ∈ [0,1]` (true for a bi-Lipschitz path such as `ϕ⁻¹|_{[0,1]}` of §5, with `K = 2`).
Then `μ = P_* Leb|_{[0,1]}` is regular and `‖μ - λ‖_G² ≤ (4 + 16 log 5 + max 1 (2K)) r`. -/
theorem fourKernel_of_coLipschitz (P : ℝ → ℂ) (r K : ℝ) (hP : ContinuousOn P (Icc 0 1))
    (hr : 0 < r) (hr1 : r ≤ 1) (hK : 0 < K) (hdisp : ∀ t ∈ Icc (0 : ℝ) 1, ‖P t - t‖ ≤ r)
    (hlow : ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, |t - t'| ≤ K * ‖P t - P t'‖) :
    IsRegular (pathMeasure P) ∧
      energyDistSq (pathMeasure P) (segMeasure 0 1) ≤
        (4 + 16 * Real.log 5 + max 1 (2 * K)) * r := by
  set P' : ℝ → ℂ := fun t => P (projIcc 0 1 zero_le_one t) with hP'def
  have hP' : Continuous P' :=
    hP.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun t =>
      (projIcc 0 1 zero_le_one t).2
  have hagree : ∀ t ∈ Icc (0 : ℝ) 1, P t = P' t := fun t ht => by
    rw [hP'def]
    simp only [projIcc_of_mem zero_le_one ht]
  have heq : pathMeasure P = pathMeasure P' := pathMeasure_congr hagree
  have hlow' : ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, |t - t'| ≤ K * ‖P' t - P' t'‖ :=
    fun t ht t' ht' => by rw [← hagree t ht, ← hagree t' ht']; exact hlow t ht t' ht'
  rw [heq]
  refine fourKernel_of_lipschitz P' r (max 1 (2 * K)) hP' hr hr1 (le_max_left _ _)
    (fun t ht => by rw [← hagree t ht]; exact hdisp t ht) fun z u hu _ => ?_
  calc (pathMeasure P' (ball z u)).toReal ≤ 2 * K * u :=
        pathMeasure_ball_le_of_coLipschitz hP'.measurable hK.le hlow' z hu.le
    _ ≤ max 1 (2 * K) * u := mul_le_mul_of_nonneg_right (le_max_right _ _) hu.le

/-- **Corollary (5.5), real-valued form** (GA2 D1, Corollary, for `ψ : [0,1] → ℝ`): if `ψ` is
continuous on `[0,1]` (e.g. bi-Lipschitz) with `|ψ(t) - t| ≤ r ≤ 1` and
`|t - t'| ≤ K |ψ t - ψ t'|`, then `μ = ψ_* Leb|_{[0,1]}` (on `ℝ ⊆ ℂ`) is regular and
`‖μ - λ‖_G² ≤ (4 + 16 log 5 + max 1 (2K)) r`. -/
theorem fourKernel_of_coLipschitz_real (ψ : ℝ → ℝ) (r K : ℝ) (hψ : ContinuousOn ψ (Icc 0 1))
    (hr : 0 < r) (hr1 : r ≤ 1) (hK : 0 < K) (hdisp : ∀ t ∈ Icc (0 : ℝ) 1, |ψ t - t| ≤ r)
    (hlow : ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, |t - t'| ≤ K * |ψ t - ψ t'|) :
    IsRegular (pathMeasure fun t => (ψ t : ℂ)) ∧
      energyDistSq (pathMeasure fun t => (ψ t : ℂ)) (segMeasure 0 1) ≤
        (4 + 16 * Real.log 5 + max 1 (2 * K)) * r :=
  fourKernel_of_coLipschitz (fun t => (ψ t : ℂ)) r K
    (Complex.continuous_ofReal.comp_continuousOn hψ) hr hr1 hK
    (fun t ht => by rw [norm_ofReal_sub_ofReal]; exact hdisp t ht)
    fun t ht t' ht' => by rw [norm_ofReal_sub_ofReal]; exact hlow t ht t' ht'

/-- **Corollary (5.5), bi-Lipschitz form**: `fourKernel_of_coLipschitz` for a path with
`|t - t'| ≤ K |P t - P t'|` and `|P t - P t'| ≤ L |t - t'|` on `[0,1]` (the upper bound only
supplies continuity). -/
theorem fourKernel_of_biLipschitz (P : ℝ → ℂ) (r K L : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hK : 0 < K)
    (hdisp : ∀ t ∈ Icc (0 : ℝ) 1, ‖P t - t‖ ≤ r)
    (hlow : ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, |t - t'| ≤ K * ‖P t - P t'‖)
    (hup : ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, ‖P t - P t'‖ ≤ L * |t - t'|) :
    IsRegular (pathMeasure P) ∧
      energyDistSq (pathMeasure P) (segMeasure 0 1) ≤ (4 + 16 * Real.log 5 + max 1 (2 * K)) * r :=
  fourKernel_of_coLipschitz P r K
    (LipschitzOnWith.of_dist_le' (K := L) fun x hx y hy => by
      rw [dist_eq_norm, Real.dist_eq]; exact hup x hx y hy).continuousOn hr hr1 hK hdisp hlow

/-- **Corollary (5.5), real-valued bi-Lipschitz form** (GA2 D1, Corollary, literally):
`ψ : [0,1] → ℝ` with `|t - t'| ≤ K |ψ t - ψ t'|`, `|ψ t - ψ t'| ≤ L |t - t'|` and
`|ψ(t) - t| ≤ r ≤ 1`. -/
theorem fourKernel_of_biLipschitz_real (ψ : ℝ → ℝ) (r K L : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hK : 0 < K) (hdisp : ∀ t ∈ Icc (0 : ℝ) 1, |ψ t - t| ≤ r)
    (hlow : ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, |t - t'| ≤ K * |ψ t - ψ t'|)
    (hup : ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, |ψ t - ψ t'| ≤ L * |t - t'|) :
    IsRegular (pathMeasure fun t => (ψ t : ℂ)) ∧
      energyDistSq (pathMeasure fun t => (ψ t : ℂ)) (segMeasure 0 1) ≤
        (4 + 16 * Real.log 5 + max 1 (2 * K)) * r :=
  fourKernel_of_coLipschitz_real ψ r K
    (LipschitzOnWith.of_dist_le' (K := L) fun x hx y hy => by
      rw [Real.dist_eq, Real.dist_eq]; exact hup x hx y hy).continuousOn hr hr1 hK hdisp hlow

/-- `ψ_* λ_{0,1} = (ψ ∘ ofReal)_* Leb|_{[0,1]}`: the image of the unit segment measure under a
measurable map is the path measure of `t ↦ ψ(t)` (the form `ψ_* λ` of (5.4)–(5.5)). -/
theorem map_segMeasure_eq_pathMeasure {ψ : ℂ → ℂ} (hψ : Measurable ψ) :
    (segMeasure 0 1).map ψ = pathMeasure fun t => ψ t := by
  rw [segMeasure_zero_one_eq_pathMeasure]
  unfold pathMeasure
  rw [Measure.map_map hψ Complex.measurable_ofReal]
  rfl

end SmallGammaGeodesics
