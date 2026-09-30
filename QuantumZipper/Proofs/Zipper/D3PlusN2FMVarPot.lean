import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarPotDef
import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarAdm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2Z-FMVAR, part E: the first-mode potential is `2π/τ`-Lipschitz

Task N2Z-FMVAR-POT. `fmPotLip_of_psi : FMPsiStmt → FMPotLipStmt`.

Route (own elementary bookkeeping on repository lemmas; the only analytic input is the
circle-average identity `avg_{|ζ-y|=r} log|ζ - c| = log max(r, |y - c|)`, i.e. Jensen's formula,
available as `SmoothConv.integral_log_norm_sub_circleUnif_sc`):

1. Newton's formula for folded circles (`SmoothConv.integral_neumannH_foldedCircle_sc`, and the
   Dirac case for `s = 0`) and admissibility of `fmMeas` (`fmAdmStmt_holds`) turn the pairing
   into `∫ Nr s (w + τ u e^{iθ}) x cos⁺ θ dθ`.
2. With `a = ū(x − w)/τ`, `b = ū(x̄ − w)/τ`, `r = s/τ`: for a.e. `θ`,
   `Nr s (w + τ u e^{iθ}) x = −2 log τ − log max(r, |a − e^{iθ}|) − log max(r, |b − e^{iθ}|)`.
   The `−v` arc is the `+v` arc with `u ↦ −u`, i.e. `a ↦ −a`, a shift by `π`, so
   `fmPot = fmPsiR r a + fmPsiR r b` (`cos = cos⁺ − cos⁻`).
3. `fmPsiR r y = ∫ fmPsi dcircleUnif(y, r)` (Jensen + Fubini on the torus), hence `fmPsiR r` is
   `π`-Lipschitz by `FMPsiStmt`; summing, `fmPot` is `2π/τ`-Lipschitz (conj is an isometry).
-/

noncomputable section

open MeasureTheory Set ComplexConjugate
open scoped Real

namespace QuantumZipper
namespace D3Plus

open SmoothConv

/-- The truncated first mode `∫ cos θ · (−log max(r, |y − e^{iθ}|)) dθ`. -/
def fmPsiR (r : ℝ) (y : ℂ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2 * π), Real.cos θ * -Real.log (max r ‖y - Complex.exp ((θ : ℂ) * Complex.I)‖)

theorem fmPsiR_zero (y : ℂ) : fmPsiR 0 y = fmPsi y := by
  unfold fmPsiR fmPsi
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [max_eq_right (norm_nonneg _)]

/-! ## Jensen's formula on circles and Fubini on the torus -/

theorem integral_abs_log_circleUnif_le (y c : ℂ) (hc : ‖c‖ = 1) {r : ℝ} (hr : 0 < r) :
    ∫ ζ, |Real.log ‖ζ - c‖| ∂circleUnif y r ≤ 2 * (‖y‖ + r + 1) - Real.log r := by
  have hi := integrable_log_norm_sub_circleUnif_sc y c r
  have hpt : ∀ ζ : ℂ, |Real.log ‖ζ - c‖| =
      2 * max (Real.log ‖ζ - c‖) 0 - Real.log ‖ζ - c‖ := by
    intro ζ
    rcases le_total 0 (Real.log ‖ζ - c‖) with h | h
    · rw [abs_of_nonneg h, max_eq_left h]; ring
    · rw [abs_of_nonpos h, max_eq_right h]; ring
  have hmax : Integrable (fun ζ => max (Real.log ‖ζ - c‖) 0) (circleUnif y r) := hi.pos_part
  simp_rw [hpt]
  rw [integral_sub (hmax.const_mul 2) hi, integral_const_mul,
    integral_log_norm_sub_circleUnif_sc y c hr]
  have h1 : ∫ ζ, max (Real.log ‖ζ - c‖) 0 ∂circleUnif y r ≤ ‖y‖ + r + 1 := by
    have : ∫ ζ, max (Real.log ‖ζ - c‖) 0 ∂circleUnif y r ≤
        ∫ _ζ, (‖y‖ + r + 1) ∂circleUnif y r := by
      refine integral_mono_ae hmax (integrable_const _) ?_
      filter_upwards [ae_circleUnif_sc y r] with ζ hζ
      refine max_le ?_ (by linarith [norm_nonneg y])
      calc Real.log ‖ζ - c‖ ≤ ‖ζ - c‖ := Real.log_le_self (norm_nonneg _)
        _ = ‖(ζ - y) + y - c‖ := by congr 1; ring
        _ ≤ ‖(ζ - y) + y‖ + ‖c‖ := norm_sub_le _ _
        _ ≤ ‖ζ - y‖ + ‖y‖ + ‖c‖ := by gcongr; exact norm_add_le _ _
        _ = ‖y‖ + r + 1 := by rw [hζ, abs_of_pos hr, hc]; ring
    simpa using this
  have h2 : Real.log r ≤ Real.log (max r ‖y - c‖) := Real.log_le_log hr (le_max_left _ _)
  linarith

theorem integrable_fmTorus (y : ℂ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun p : ℝ × ℂ =>
        Real.cos p.1 * -Real.log ‖p.2 - Complex.exp ((p.1 : ℂ) * Complex.I)‖)
      ((volume.restrict (Ioc 0 (2 * π))).prod (circleUnif y r)) := by
  have hc : Continuous fun p : ℝ × ℂ => p.2 - Complex.exp ((p.1 : ℂ) * Complex.I) := by
    fun_prop
  have hm : Measurable (fun p : ℝ × ℂ =>
      Real.cos p.1 * -Real.log ‖p.2 - Complex.exp ((p.1 : ℂ) * Complex.I)‖) :=
    (Real.continuous_cos.measurable.comp measurable_fst).mul
      (Real.measurable_log.comp hc.measurable.norm).neg
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (2 * π))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  refine (integrable_prod_iff hm.aestronglyMeasurable).2 ⟨ae_of_all _ fun θ => ?_, ?_⟩
  · exact Integrable.const_mul (integrable_log_norm_sub_circleUnif_sc y
      (Complex.exp ((θ : ℂ) * Complex.I)) r).neg (Real.cos θ)
  · refine Integrable.of_bound hm.aestronglyMeasurable.norm.integral_prod_right'
      (2 * (‖y‖ + r + 1) - Real.log r) (ae_of_all _ fun θ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have hE : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
    refine le_trans (integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
      (integrable_log_norm_sub_circleUnif_sc y (Complex.exp ((θ : ℂ) * Complex.I)) r).abs
      (ae_of_all _ fun ζ => ?_))
      (integral_abs_log_circleUnif_le y (Complex.exp ((θ : ℂ) * Complex.I)) hE hr)
    simp only [norm_mul, norm_neg, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)

/-- `fmPsiR r y` is the circle average of `fmPsi` over `∂B(y, r)`. -/
theorem fmPsiR_eq_integral (y : ℂ) {r : ℝ} (hr : 0 < r) :
    fmPsiR r y = ∫ ζ, fmPsi ζ ∂circleUnif y r := by
  have hswap := integral_integral_swap (f := fun (θ : ℝ) (ζ : ℂ) =>
    Real.cos θ * -Real.log ‖ζ - Complex.exp ((θ : ℂ) * Complex.I)‖) (integrable_fmTorus y hr)
  unfold fmPsiR fmPsi
  simp only [intervalIntegral.integral_of_le Real.two_pi_pos.le]
  refine Eq.trans ?_ hswap
  refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
  rw [integral_const_mul, integral_neg, integral_log_norm_sub_circleUnif_sc y _ hr]

theorem integral_circleUnif_eq (f : ℂ → ℝ) (hf : Continuous f) (y : ℂ) (r : ℝ) :
    ∫ ζ, f ζ ∂circleUnif y r = (2 * π)⁻¹ * ∫ φ in Ico 0 (2 * π), f (circleMap y r φ) := by
  unfold circleUnif
  rw [integral_smul_measure, integral_map (measurable_circleMap y r).aemeasurable
    hf.aestronglyMeasurable, smul_eq_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal Real.two_pi_pos.le]

/-- `fmPsiR r` is `π`-Lipschitz. -/
theorem fmPsiR_lip (hψ : FMPsiStmt) {r : ℝ} (hr : 0 ≤ r) (y y' : ℂ) :
    |fmPsiR r y - fmPsiR r y'| ≤ π * ‖y - y'‖ := by
  rcases hr.eq_or_lt with h0 | h0
  · subst h0; rw [fmPsiR_zero, fmPsiR_zero]; exact hψ.2 y y'
  have hc : Continuous fmPsi := by
    refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal π) fun a b => ?_).continuous
    rw [Real.coe_toNNReal _ Real.pi_pos.le, Real.dist_eq, dist_eq_norm]
    exact hψ.2 a b
  have hi : ∀ c : ℂ, IntegrableOn (fun φ => fmPsi (circleMap c r φ)) (Ico 0 (2 * π)) :=
    fun c => ((hc.comp (continuous_circleMap c r)).integrableOn_Icc).mono_set
      Ico_subset_Icc_self
  rw [fmPsiR_eq_integral y h0, fmPsiR_eq_integral y' h0, integral_circleUnif_eq _ hc,
    integral_circleUnif_eq _ hc, ← mul_sub, ← integral_sub (hi y) (hi y')]
  have hb : ‖∫ φ in Ico 0 (2 * π), (fmPsi (circleMap y r φ) - fmPsi (circleMap y' r φ))‖ ≤
      π * ‖y - y'‖ * volume.real (Ico 0 (2 * π)) := by
    refine norm_setIntegral_le_of_norm_le_const measure_Ico_lt_top fun φ _ => ?_
    have e : circleMap y r φ - circleMap y' r φ = y - y' := by unfold circleMap; ring
    have := hψ.2 (circleMap y r φ) (circleMap y' r φ)
    rw [e] at this
    rwa [Real.norm_eq_abs]
  rw [Real.volume_real_Ico_of_le Real.two_pi_pos.le, sub_zero, Real.norm_eq_abs] at hb
  rw [abs_mul, abs_of_pos (inv_pos.2 Real.two_pi_pos)]
  calc (2 * π)⁻¹ * |∫ φ in Ico 0 (2 * π), (fmPsi (circleMap y r φ) - fmPsi (circleMap y' r φ))|
      ≤ (2 * π)⁻¹ * (π * ‖y - y'‖ * (2 * π)) := by gcongr
    _ = π * ‖y - y'‖ := by field_simp

/-! ## The pairing as an arc integral -/

theorem Nr_zero_fm (w x : ℂ) : Nr 0 w x = neumannH w x := by
  unfold Nr neumannH
  rw [max_eq_right (norm_nonneg _), max_eq_right (norm_nonneg _)]

theorem integral_neumannH_fc_fm (x z : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    ∫ y, neumannH x y ∂foldedCircle z s = Nr s z x := by
  rcases hs.eq_or_lt with h0 | h0
  · subst h0
    rw [RegSample.fc_zero, integral_dirac, Nr_zero_fm, neumannH_symm, neumannH_foldH_sc]
  · rw [show (∫ y, neumannH x y ∂foldedCircle z s) = ∫ y, neumannH y x ∂foldedCircle z s from
      integral_congr_ae (ae_of_all _ fun y => neumannH_symm x y)]
    exact integral_neumannH_foldedCircle_sc z x h0

/-- Copy of `integrable_log_norm_sub_K3` (GFF/K3/MixedM6Kernel.lean), to avoid that import. -/
theorem integrable_log_norm_sub_adm_fm {ν : Measure ℂ} (hν : IsAdmissibleH ν) (x : ℂ) :
    Integrable (fun y => Real.log ‖y - x‖) ν := by
  obtain ⟨hνf, ⟨K, hK, -, hKc⟩, C, hC, hbd⟩ := hν
  have := hνf
  obtain ⟨ρ, hρ⟩ := hK.isBounded.exists_norm_le
  set D := max 1 (ρ + ‖x‖) with hD
  have hmeas : Measurable fun y : ℂ => Real.log ‖y - x‖ :=
    Real.measurable_log.comp (measurable_id.sub_const x).norm
  have hneg : Integrable (fun y => (ENNReal.ofReal (-Real.log ‖y - x‖)).toReal) ν :=
    integrable_toReal_of_lintegral_ne_top
      (ENNReal.measurable_ofReal.comp hmeas.neg).aemeasurable ((hbd x).trans_lt hC).ne
  refine ((integrable_const (Real.log D)).add hneg).mono' hmeas.aestronglyMeasurable ?_
  have hKae : ∀ᵐ y ∂ν, y ∈ K := ae_iff.2 hKc
  filter_upwards [hKae] with y hy
  simp only [Pi.add_apply]
  have hD1 : 0 ≤ Real.log D := Real.log_nonneg (le_max_left _ _)
  have hrD : ‖y - x‖ ≤ D :=
    calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ ρ + ‖x‖ := by linarith [hρ y hy]
      _ ≤ D := le_max_right _ _
  have hup : Real.log ‖y - x‖ ≤ Real.log D := by
    rcases (norm_nonneg (y - x)).eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero]; exact hD1
    · exact Real.log_le_log h0 hrD
  rw [Real.norm_eq_abs, ENNReal.toReal_ofReal']
  have m1 := le_max_left (-Real.log ‖y - x‖) 0
  have m2 := le_max_right (-Real.log ‖y - x‖) 0
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem measurable_Nr_fm (s : ℝ) (x : ℂ) : Measurable fun z => Nr s z x := by
  unfold Nr
  have h1 : Continuous fun z : ℂ => max s ‖z - x‖ :=
    continuous_const.max (continuous_id.sub continuous_const).norm
  have h2 : Continuous fun z : ℂ => max s ‖z - conj x‖ :=
    continuous_const.max (continuous_id.sub continuous_const).norm
  exact (Real.measurable_log.comp h1.measurable).neg.sub (Real.measurable_log.comp h2.measurable)

theorem integral_fmMeas_eq {w v : ℂ} {s : ℝ} (hs : 0 ≤ s) (hv : 0 < ‖v‖) (hvs : ‖v‖ + s < w.im)
    (x : ℂ) :
    ∫ y, neumannH x y ∂fmMeas w v s =
      ∫ θ in (0 : ℝ)..(2 * π),
        Nr s (w + v * Complex.exp ((θ : ℂ) * Complex.I)) x * max (Real.cos θ) 0 := by
  have hadm := fmAdmStmt_holds w v s hs hv hvs
  have hint : Integrable (fun y => neumannH x y) (fmMeas w v s) := by
    have := (integrable_log_norm_sub_adm_fm hadm x).neg.sub
      (integrable_log_norm_sub_adm_fm hadm (conj x))
    refine this.congr (ae_of_all _ fun y => ?_)
    show -Real.log ‖y - x‖ - Real.log ‖y - conj x‖ = neumannH x y
    rw [neumannH_symm]; rfl
  unfold fmMeas at hint ⊢
  rw [integral_bind_fc s hint]
  refine (integral_congr_ae (ae_of_all _ fun z => integral_neumannH_fc_fm x z hs)).trans ?_
  unfold fmArc
  rw [integral_map (measurable_fmArcMap w v).aemeasurable (measurable_Nr_fm s x).aestronglyMeasurable]
  unfold fmBase
  rw [integral_withDensity_eq_integral_toReal_smul
    (Real.continuous_cos.measurable.ennreal_ofReal) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    intervalIntegral.integral_of_le (by positivity)]
  refine integral_congr_ae (ae_of_all _ fun φ => ?_)
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  ring

/-! ## Rescaling to the unit circle -/

theorem norm_fm_rescale {u : ℂ} (hu : ‖u‖ = 1) (w p E : ℂ) {τ : ℝ} (hτ : 0 < τ) :
    ‖w + (τ : ℂ) * u * E - p‖ = τ * ‖conj u * (p - w) / (τ : ℂ) - E‖ := by
  have hu2 : u * conj u = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]; simp
  have hτc : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hτ.ne'
  calc ‖w + (τ : ℂ) * u * E - p‖ = ‖u * (conj u * (p - w) - τ * E)‖ := by
        rw [← norm_neg]; congr 1; linear_combination (w - p) * hu2
    _ = ‖(τ : ℂ) * (conj u * (p - w) / τ - E)‖ := by
        rw [norm_mul, hu, one_mul, mul_sub (τ : ℂ) _ E, mul_div_cancel₀ _ hτc]
    _ = τ * ‖conj u * (p - w) / (τ : ℂ) - E‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ.le]

theorem log_max_scale_fm {s τ t : ℝ} (hτ : 0 < τ) (ht : 0 < t) :
    Real.log (max s (τ * t)) = Real.log τ + Real.log (max (s / τ) t) := by
  rw [show max s (τ * t) = τ * max (s / τ) t by
    rw [mul_max_of_nonneg _ _ hτ.le, mul_div_cancel₀ _ hτ.ne']]
  exact Real.log_mul hτ.ne' (lt_of_lt_of_le ht (le_max_right _ _)).ne'

theorem ae_exp_ne_fm (c : ℂ) : ∀ᵐ θ : ℝ, Complex.exp ((θ : ℂ) * Complex.I) ≠ c := by
  by_cases h : ∃ θ₀ : ℝ, Complex.exp ((θ₀ : ℂ) * Complex.I) = c
  · obtain ⟨θ₀, rfl⟩ := h
    have hsub : {θ : ℝ | Complex.exp ((θ : ℂ) * Complex.I) =
        Complex.exp ((θ₀ : ℂ) * Complex.I)} ⊆ range (fun n : ℤ => θ₀ + n * (2 * π)) := by
      intro θ hθ
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 hθ
      refine ⟨n, ?_⟩
      have := congrArg Complex.im hn
      simp at this
      show θ₀ + (n : ℝ) * (2 * π) = θ
      linarith
    rw [ae_iff]
    simpa using ((countable_range _).mono hsub).measure_zero volume
  · exact ae_of_all _ fun θ hθ => h ⟨θ, hθ⟩

/-- `log max(r, |p − e^{iθ}|)`. -/
def fmL (r : ℝ) (p : ℂ) (θ : ℝ) : ℝ := Real.log (max r ‖p - Complex.exp ((θ : ℂ) * Complex.I)‖)

theorem intervalIntegrable_fmL (p : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    IntervalIntegrable (fmL r p) volume 0 (2 * π) := by
  rcases hr.eq_or_lt with h0 | h0
  · subst h0
    have h := circleIntegrable_log_norm_sub_const (a := p) (c := 0) 1
    have e : fmL 0 p = fun θ => Real.log ‖circleMap 0 1 θ - p‖ := by
      funext θ
      rw [fmL, max_eq_right (norm_nonneg _), norm_sub_rev]
      simp [circleMap]
    rw [e]; exact h
  · unfold fmL
    refine Continuous.intervalIntegrable ?_ _ _
    exact (continuous_const.max (continuous_const.sub (Complex.continuous_exp.comp
      (Complex.continuous_ofReal.mul continuous_const))).norm).log
      fun θ => (lt_of_lt_of_le h0 (le_max_left _ _)).ne'

theorem exp_add_two_pi_fm (θ : ℝ) :
    Complex.exp (((θ + 2 * π : ℝ) : ℂ) * Complex.I) = Complex.exp ((θ : ℂ) * Complex.I) := by
  push_cast; rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem exp_add_pi_fm (θ : ℝ) :
    Complex.exp (((θ + π : ℝ) : ℂ) * Complex.I) = -Complex.exp ((θ : ℂ) * Complex.I) := by
  push_cast; rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]

/-- Per-direction arc integral in unit-circle coordinates. -/
theorem arc_eq_fm {u : ℂ} (hu : ‖u‖ = 1) (w x : ℂ) {τ s : ℝ} (hτ : 0 < τ) (hs : 0 ≤ s) :
    ∫ θ in (0 : ℝ)..(2 * π),
        Nr s (w + (τ : ℂ) * u * Complex.exp ((θ : ℂ) * Complex.I)) x * max (Real.cos θ) 0 =
      -2 * Real.log τ * (∫ θ in (0 : ℝ)..(2 * π), max (Real.cos θ) 0)
        - (∫ θ in (0 : ℝ)..(2 * π), fmL (s / τ) (conj u * (x - w) / τ) θ * max (Real.cos θ) 0)
        - ∫ θ in (0 : ℝ)..(2 * π),
            fmL (s / τ) (conj u * (conj x - w) / τ) θ * max (Real.cos θ) 0 := by
  have hr : 0 ≤ s / τ := div_nonneg hs hτ.le
  have hcp : Continuous fun θ : ℝ => max (Real.cos θ) 0 :=
    Real.continuous_cos.max continuous_const
  have ia := (intervalIntegrable_fmL (conj u * (x - w) / τ) hr).mul_continuousOn
    hcp.continuousOn
  have ib := (intervalIntegrable_fmL (conj u * (conj x - w) / τ) hr).mul_continuousOn
    hcp.continuousOn
  have ic := (hcp.intervalIntegrable (μ := volume) 0 (2 * π)).const_mul (-2 * Real.log τ)
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub ic ia,
    ← intervalIntegral.integral_sub (ic.sub ia) ib]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_exp_ne_fm (conj u * (x - w) / τ),
    ae_exp_ne_fm (conj u * (conj x - w) / τ)] with θ h1 h2 _
  have ta : 0 < ‖conj u * (x - w) / (τ : ℂ) - Complex.exp ((θ : ℂ) * Complex.I)‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm h1))
  have tb : 0 < ‖conj u * (conj x - w) / (τ : ℂ) - Complex.exp ((θ : ℂ) * Complex.I)‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm h2))
  unfold Nr fmL
  rw [norm_fm_rescale hu w x _ hτ, norm_fm_rescale hu w (conj x) _ hτ, log_max_scale_fm hτ ta,
    log_max_scale_fm hτ tb]
  ring

/-- Copy of `integral_shift_fm` (D3PlusN2FMVarRepr.lean), to avoid that import. -/
theorem integral_shift_fm' (F : ℝ → ℝ) (hF : Function.Periodic F (2 * π)) (c : ℝ) :
    ∫ φ in (0 : ℝ)..(2 * π), F (φ + c) = ∫ φ in (0 : ℝ)..(2 * π), F φ := by
  rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm (2 * π) c]
  simpa using hF.intervalIntegral_add_eq c 0

/-- The `−v` arc is the `+v` arc shifted by `π`. -/
theorem arc_neg_fm (r : ℝ) (p : ℂ) :
    ∫ θ in (0 : ℝ)..(2 * π), fmL r (-p) θ * max (Real.cos θ) 0 =
      ∫ θ in (0 : ℝ)..(2 * π), fmL r p θ * max (-Real.cos θ) 0 := by
  have hF : Function.Periodic (fun θ => fmL r p θ * max (-Real.cos θ) 0) (2 * π) := by
    intro θ
    simp only [fmL, exp_add_two_pi_fm, Real.cos_add_two_pi]
  refine Eq.trans ?_ (integral_shift_fm' _ hF π)
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have e : ‖-p - Complex.exp ((θ : ℂ) * Complex.I)‖ =
      ‖p - Complex.exp (((θ + π : ℝ) : ℂ) * Complex.I)‖ := by
    rw [exp_add_pi_fm, ← norm_neg]; congr 1; ring
  simp only [fmL, Real.cos_add_pi, neg_neg]
  rw [e]

theorem fmPsiR_eq_arc (p : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    fmPsiR r p = (∫ θ in (0 : ℝ)..(2 * π), fmL r p θ * max (-Real.cos θ) 0) -
      ∫ θ in (0 : ℝ)..(2 * π), fmL r p θ * max (Real.cos θ) 0 := by
  have c1 : Continuous fun θ : ℝ => max (-Real.cos θ) 0 :=
    Real.continuous_cos.neg.max continuous_const
  have c2 : Continuous fun θ : ℝ => max (Real.cos θ) 0 :=
    Real.continuous_cos.max continuous_const
  have i1 := (intervalIntegrable_fmL p hr).mul_continuousOn c1.continuousOn
  have i2 := (intervalIntegrable_fmL p hr).mul_continuousOn c2.continuousOn
  rw [← intervalIntegral.integral_sub i1 i2]
  unfold fmPsiR
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [fmL]
  rcases le_total 0 (Real.cos θ) with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]; ring
  · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]; ring

/-! ## Assembly -/

theorem fmPot_eq_fmPsiR {u : ℂ} (hu : ‖u‖ = 1) (w : ℂ) {τ s : ℝ} (hτ : 0 < τ) (hs : 0 ≤ s)
    (hsτ : s ≤ τ) (hw : 3 * τ ≤ w.im) (x : ℂ) :
    fmPot w ((τ : ℂ) * u) s x =
      fmPsiR (s / τ) (conj u * (x - w) / τ) + fmPsiR (s / τ) (conj u * (conj x - w) / τ) := by
  have hv : ‖(τ : ℂ) * u‖ = τ := by
    rw [norm_mul, hu, mul_one, Complex.norm_real, Real.norm_of_nonneg hτ.le]
  have hv' : ‖-((τ : ℂ) * u)‖ = τ := by rw [norm_neg, hv]
  have hvs : τ + s < w.im := by linarith
  have hr : 0 ≤ s / τ := div_nonneg hs hτ.le
  have hnu : ‖-u‖ = 1 := by rw [norm_neg, hu]
  unfold fmPot
  rw [integral_fmMeas_eq hs (by rw [hv]; exact hτ) (by rw [hv]; exact hvs),
    integral_fmMeas_eq hs (by rw [hv']; exact hτ) (by rw [hv']; exact hvs)]
  have e2 : ∀ θ : ℝ, w + -((τ : ℂ) * u) * Complex.exp ((θ : ℂ) * Complex.I) =
      w + (τ : ℂ) * (-u) * Complex.exp ((θ : ℂ) * Complex.I) := fun θ => by ring
  simp_rw [e2]
  rw [arc_eq_fm hu w x hτ hs, arc_eq_fm hnu w x hτ hs]
  have n1 : conj (-u) * (x - w) / (τ : ℂ) = -(conj u * (x - w) / τ) := by rw [map_neg]; ring
  have n2 : conj (-u) * (conj x - w) / (τ : ℂ) = -(conj u * (conj x - w) / τ) := by
    rw [map_neg]; ring
  rw [n1, n2, arc_neg_fm, arc_neg_fm, fmPsiR_eq_arc _ hr, fmPsiR_eq_arc _ hr]
  ring

/-- **FM-POTLIP from FM-PSI.** -/
theorem fmPotLip_of_psi (hψ : FMPsiStmt) : FMPotLipStmt := by
  intro u w τ s hu hτ hs hsτ hw x _ x' _
  rw [fmPot_eq_fmPsiR hu w hτ hs hsτ hw x, fmPot_eq_fmPsiR hu w hτ hs hsτ hw x']
  have hr : 0 ≤ s / τ := div_nonneg hs hτ.le
  have hconj : ‖conj u‖ = 1 := by rw [Complex.norm_conj, hu]
  have d1 : ‖conj u * (x - w) / (τ : ℂ) - conj u * (x' - w) / τ‖ = ‖x - x'‖ / τ := by
    rw [← sub_div, ← mul_sub, norm_div, norm_mul, hconj, one_mul, Complex.norm_real,
      Real.norm_of_nonneg hτ.le, sub_sub_sub_cancel_right]
  have d2 : ‖conj u * (conj x - w) / (τ : ℂ) - conj u * (conj x' - w) / τ‖ = ‖x - x'‖ / τ := by
    rw [← sub_div, ← mul_sub, norm_div, norm_mul, hconj, one_mul, Complex.norm_real,
      Real.norm_of_nonneg hτ.le, sub_sub_sub_cancel_right, ← map_sub, Complex.norm_conj]
  have h1 := fmPsiR_lip hψ hr (conj u * (x - w) / τ) (conj u * (x' - w) / τ)
  have h2 := fmPsiR_lip hψ hr (conj u * (conj x - w) / τ) (conj u * (conj x' - w) / τ)
  rw [d1] at h1
  rw [d2] at h2
  calc |_ - _| ≤ |fmPsiR (s / τ) (conj u * (x - w) / τ) - fmPsiR (s / τ) (conj u * (x' - w) / τ)|
        + |fmPsiR (s / τ) (conj u * (conj x - w) / τ)
            - fmPsiR (s / τ) (conj u * (conj x' - w) / τ)| := by
        rw [show ∀ a b c d : ℝ, (a + b) - (c + d) = (a - c) + (b - d) from
          fun _ _ _ _ => by ring]
        exact abs_add_le _ _
    _ ≤ π * (‖x - x'‖ / τ) + π * (‖x - x'‖ / τ) := add_le_add h1 h2
    _ = 2 * π / τ * ‖x - x'‖ := by ring

end D3Plus
end QuantumZipper
