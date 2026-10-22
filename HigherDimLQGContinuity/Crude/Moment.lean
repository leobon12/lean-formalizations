import HigherDimLQGContinuity.Core.Interfaces
import LQGMetric.Papers.DG.Lemma25
import HigherDimLFPP.Field.LawTransfer
import HigherDimLFPP.Paths.Measurable
import GaussianLQG.Probability.Gaussian
import HigherDimLFPP.Exist.Scaling

/-!
# Path moment estimate for an independent band

The argument follows the Tonelli-first proof of `LQGMetric.DG.lintegral_coupled_length_le`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLFPP

/-- One-point exponential moment of a continuous band, expressed under its continuous-map law. -/
theorem crude_band_exp_lintegral {d : ℕ} {κ : Rd d → ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
    {a b : ℝ} {F : Rd d → Ω → ℝ} (hF : IsBandVersion P W κ a b F)
    (hW : IsWhiteNoise P W) (hκ : IsLFPPKernel κ) (ha : 0 < a)
    (hab : a ≤ b) (ξ : ℝ) (z : Rd d) :
    ∫⁻ f : C(Rd d, ℝ), ENNReal.ofReal (Real.exp (ξ * f z))
        ∂(P.map (contField F hF.continuous)) =
      ENNReal.ofReal (Real.exp (Real.log (b / a) * ξ ^ 2 / 2)) := by
  let f : Ω → C(Rd d, ℝ) := contField F hF.continuous
  have hmeas : Measurable f := measurable_contField hF.continuous hF.measurable
  have hX := hF.hasLaw_log hW hκ ha hab z
  have hInt := GaussianLQG.integrable_exp_mul_of_hasLaw_gaussianReal hX ξ
  have hfun : Measurable (fun g : C(Rd d, ℝ) => ENNReal.ofReal (Real.exp (ξ * g z))) :=
    ENNReal.measurable_ofReal.comp (((continuous_eval_const z).measurable.const_mul ξ).exp)
  calc
    ∫⁻ g : C(Rd d, ℝ), ENNReal.ofReal (Real.exp (ξ * g z)) ∂(P.map f)
        = ∫⁻ ω, ENNReal.ofReal (Real.exp (ξ * F z ω)) ∂P := by
            rw [lintegral_map' hfun.aemeasurable hmeas.aemeasurable]
            rfl
    _ = ENNReal.ofReal (∫ ω, Real.exp (ξ * F z ω) ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal hInt
            (ae_of_all _ fun _ => (Real.exp_pos _).le)).symm
    _ = _ := by
          rw [GaussianLQG.integral_exp_mul_of_hasLaw_gaussianReal hX ξ]
          congr 1
          congr 1
          rw [Real.coe_toNNReal _ (by
            have h : 0 ≤ Real.log (b / a) := Real.log_nonneg (by
              exact (le_div_iff₀ ha).2 (by simpa using hab))
            exact h)]

/-- A pointwise exponential moment bound integrates along any fixed piecewise `C¹` path. -/
theorem crude_length_lintegral_le {d : ℕ} {μ : Measure C(Rd d, ℝ)}
    [IsProbabilityMeasure μ] (φ : C(Rd d, ℝ)) (ξ K : ℝ) (hK : 0 ≤ K)
    (hmom : ∀ z : Rd d, ∫⁻ f : C(Rd d, ℝ), ENNReal.ofReal (Real.exp (ξ * f z)) ∂μ ≤
      ENNReal.ofReal K) {x y : Rd d} {γ : ℝ → Rd d} (hγ : IsPcwC1Path γ x y) :
    ∫⁻ f : C(Rd d, ℝ), ENNReal.ofReal
      (lfppLength ξ (fun z => φ z + f z) γ) ∂μ ≤
      ENNReal.ofReal (K * lfppLength ξ φ γ) := by
  let a : ℝ → ℝ := fun t => Real.exp (ξ * φ (γ t)) * ‖deriv γ t‖
  let b : ℝ → C(Rd d, ℝ) → ℝ := fun t f => Real.exp (ξ * f (γ t))
  have ha0 : ∀ t, 0 ≤ a t := fun t => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hfac : ∀ f t, Real.exp (ξ * (φ (γ t) + f (γ t))) * ‖deriv γ t‖ =
      a t * b t f := by
    intro f t
    dsimp [a, b]
    rw [mul_add, Real.exp_add]
    ring
  have hγm : AEMeasurable γ (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (hγ.continuousOn.mono Ioc_subset_Icc_self).aemeasurable measurableSet_Ioc
  have haM : AEMeasurable a (volume.restrict (Ioc (0 : ℝ) 1)) := by
    have hc : ContinuousOn (fun t => Real.exp (ξ * φ (γ t))) (Ioc 0 1) :=
      Real.continuous_exp.comp_continuousOn
        ((continuous_const.mul φ.continuous).comp_continuousOn
          (hγ.continuousOn.mono Ioc_subset_Icc_self))
    exact (hc.aemeasurable measurableSet_Ioc).mul (measurable_deriv γ).norm.aemeasurable
  have hbM : AEMeasurable (fun p : C(Rd d, ℝ) × ℝ => b p.2 p.1)
      (μ.prod (volume.restrict (Ioc 0 1))) := by
    have hp : AEMeasurable (fun p : C(Rd d, ℝ) × ℝ => (p.1, γ p.2))
        (μ.prod (volume.restrict (Ioc 0 1))) :=
      measurable_fst.aemeasurable.prodMk
        (hγm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
    exact Real.continuous_exp.measurable.comp_aemeasurable
      ((continuous_eval.measurable.comp_aemeasurable hp).const_mul ξ)
  have hF : AEMeasurable (Function.uncurry fun (f : C(Rd d, ℝ)) (t : ℝ) =>
      ENNReal.ofReal (a t) * ENNReal.ofReal (b t f))
      (μ.prod (volume.restrict (Ioc 0 1))) := by
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      (haM.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)).mul
        (ENNReal.measurable_ofReal.comp_aemeasurable hbM)
  have haI : IntegrableOn a (Ioc 0 1) := by
    have hc : ContinuousOn (fun t => Real.exp (ξ * φ (γ t))) (uIcc 0 1) := by
      rw [uIcc_of_le zero_le_one]
      exact Real.continuous_exp.comp_continuousOn
        ((continuous_const.mul φ.continuous).comp_continuousOn hγ.continuousOn)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      ((hγ.intervalIntegrable_deriv.norm).continuousOn_mul hc)
  calc
    ∫⁻ f : C(Rd d, ℝ), ENNReal.ofReal (lfppLength ξ (fun z => φ z + f z) γ) ∂μ
        ≤ ∫⁻ f : C(Rd d, ℝ), (∫⁻ t in Ioc 0 1,
          ENNReal.ofReal (a t) * ENNReal.ofReal (b t f)) ∂μ := by
            refine lintegral_mono fun f => ?_
            rw [lfppLength_eq_integral, intervalIntegral.integral_of_le zero_le_one]
            refine (LQGMetric.DG.ofReal_integral_le_lintegral
              (ae_of_all _ fun t => lfppIntegrand_nonneg ξ (fun z => φ z + f z) γ t)).trans
              (le_of_eq ?_)
            exact lintegral_congr fun t => by
              rw [show lfppIntegrand ξ (fun z => φ z + f z) γ t = a t * b t f from hfac f t,
                ENNReal.ofReal_mul (ha0 t)]
    _ = ∫⁻ t in Ioc 0 1, ∫⁻ f : C(Rd d, ℝ),
          ENNReal.ofReal (a t) * ENNReal.ofReal (b t f) ∂μ := lintegral_lintegral_swap hF
    _ = ∫⁻ t in Ioc 0 1, ENNReal.ofReal (a t) *
          ∫⁻ f : C(Rd d, ℝ), ENNReal.ofReal (b t f) ∂μ := by
            refine lintegral_congr fun t => ?_
            exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ∫⁻ t in Ioc 0 1, ENNReal.ofReal (a t) * ENNReal.ofReal K :=
      setLIntegral_mono' measurableSet_Ioc fun t _ => by
        exact mul_le_mul' le_rfl (hmom (γ t))
    _ = ENNReal.ofReal (∫ t in Ioc 0 1, a t) * ENNReal.ofReal K := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
          ofReal_integral_eq_lintegral_ofReal haI (ae_of_all _ ha0)]
    _ = ENNReal.ofReal (K * lfppLength ξ φ γ) := by
        rw [lfppLength_eq_integral, intervalIntegral.integral_of_le zero_le_one]
        change ENNReal.ofReal (∫ t in Ioc 0 1, a t) * ENNReal.ofReal K =
          ENNReal.ofReal (K * ∫ t in Ioc 0 1, a t)
        rw [ENNReal.ofReal_mul hK]
        exact mul_comm _ _

/-- Taking the path infimum after Tonelli gives the same moment bound for distance. -/
theorem crude_distance_lintegral_le {d : ℕ} {μ : Measure C(Rd d, ℝ)}
    [IsProbabilityMeasure μ] (φ : C(Rd d, ℝ)) (ξ K : ℝ) (hK : 0 ≤ K)
    (hmom : ∀ z : Rd d, ∫⁻ f : C(Rd d, ℝ), ENNReal.ofReal (Real.exp (ξ * f z)) ∂μ ≤
      ENNReal.ofReal K) :
    ∫⁻ f : C(Rd d, ℝ), ENNReal.ofReal
      (lfppDistance d ξ (fun z => φ z + f z)) ∂μ ≤
      ENNReal.ofReal (K * lfppDistance d ξ φ) := by
  let A : ℝ≥0∞ := ∫⁻ f : C(Rd d, ℝ), ENNReal.ofReal
    (lfppDistance d ξ (fun z => φ z + f z)) ∂μ
  have hpath : ∀ γ : {γ : ℝ → Rd d // IsAdmissiblePath d γ},
      A ≤ ENNReal.ofReal (K * lfppLength ξ φ γ.1) := by
    intro γ
    have hp : ∀ f : C(Rd d, ℝ),
        ENNReal.ofReal (lfppDistance d ξ (fun z => φ z + f z)) ≤
          ENNReal.ofReal (lfppLength ξ (fun z => φ z + f z) γ.1) := by
      intro f
      exact ENNReal.ofReal_le_ofReal
        (lfppDistance_le_lfppLength γ.2 ξ (fun z => φ z + f z))
    have hi : A ≤ ∫⁻ f : C(Rd d, ℝ),
        ENNReal.ofReal (lfppLength ξ (fun z => φ z + f z) γ.1) ∂μ := lintegral_mono hp
    exact hi.trans (crude_length_lintegral_le φ ξ K hK hmom γ.2.isPcwC1Path)
  have hpath0 : IsAdmissiblePath d (segPath (0 : Rd d) (e₁ d)) := by
    exact isAdmissiblePath_iff.2
      ⟨isPcwC1Path_segPath _ _,
        mapsTo_segPath (convex_cube d) (zero_mem_cube d) (e₁_mem_cube d)⟩
  have hAfin : A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hpath ⟨_, hpath0⟩)
  by_cases hKpos : 0 < K
  · have hle : A.toReal / K ≤ lfppDistance d ξ φ := by
      apply le_lfppDistance
      intro γ hγ
      rw [div_le_iff₀ hKpos]
      simpa only [mul_comm] using
        (ENNReal.toReal_le_of_le_ofReal
          (mul_nonneg hK (lfppLength_nonneg ξ φ γ)) (hpath ⟨γ, hγ⟩))
    rw [div_le_iff₀ hKpos] at hle
    calc A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hAfin).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by simpa only [mul_comm] using hle)
  · have hKzero : K = 0 := le_antisymm (le_of_not_gt hKpos) hK
    subst K
    have hAzero : A = 0 := by
      have := hpath ⟨_, hpath0⟩
      simpa using this
    simp [A, hAzero]

/-- Markov's inequality on the product law of independent coarse and fine fields. -/
theorem crude_product_bad_ratio {d : ℕ} {μ ν : Measure C(Rd d, ℝ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hd : 0 < d) (ξ K C : ℝ)
    (hK : 0 ≤ K) (hC : 0 < C)
    (hmom : ∀ z : Rd d, ∫⁻ f : C(Rd d, ℝ), ENNReal.ofReal (Real.exp (ξ * f z)) ∂ν ≤
      ENNReal.ofReal K) :
    (μ.prod ν) {p : C(Rd d, ℝ) × C(Rd d, ℝ) |
      C * lfppDistance d ξ p.1 < lfppDistance d ξ (p.1 + p.2)} ≤
      ENNReal.ofReal (K / C) := by
  let X : C(Rd d, ℝ) × C(Rd d, ℝ) → ℝ := fun p => lfppDistance d ξ p.1
  let Y : C(Rd d, ℝ) × C(Rd d, ℝ) → ℝ := fun p => lfppDistance d ξ (p.1 + p.2)
  let D : C(Rd d, ℝ) × C(Rd d, ℝ) → ℝ≥0∞ := fun p => ENNReal.ofReal (C * X p)
  let N : C(Rd d, ℝ) × C(Rd d, ℝ) → ℝ≥0∞ := fun p => ENNReal.ofReal (Y p)
  have hXpos : ∀ p : C(Rd d, ℝ) × C(Rd d, ℝ), 0 < X p :=
    fun p => lfppDistance_pos hd p.1.continuous
  have hDpos : ∀ p, 0 < C * X p := fun p => mul_pos hC (hXpos p)
  have hD0 : ∀ p, D p ≠ 0 := fun p => (ENNReal.ofReal_pos.2 (hDpos p)).ne'
  have hsub : {p | C * X p < Y p} ⊆ {p | 1 ≤ N p / D p} := by
    intro p hp
    simp only [mem_ofPred_eq] at hp ⊢
    rw [ENNReal.le_div_iff_mul_le (Or.inl (hD0 p)) (Or.inl ENNReal.ofReal_ne_top), one_mul]
    exact ENNReal.ofReal_le_ofReal hp.le
  have hXm : Measurable X := (measurable_lfppDistance_continuousMap ξ).comp measurable_fst
  have hYm : Measurable Y := by
    change Measurable (fun p : C(Rd d, ℝ) × C(Rd d, ℝ) =>
      lfppDistance d ξ (fun z => p.1 z + p.2 z))
    exact HigherDimLFPP.measurable_lfppDistance
      (fun p => p.1.continuous.add p.2.continuous)
      (fun z => ((continuous_eval_const z).measurable.comp measurable_fst).add
        ((continuous_eval_const z).measurable.comp measurable_snd)) ξ
  have hR : AEMeasurable (fun p => N p / D p) (μ.prod ν) :=
    (ENNReal.measurable_ofReal.comp hYm).aemeasurable.div
      (ENNReal.measurable_ofReal.comp (hXm.const_mul C)).aemeasurable
  have hMarkov := mul_meas_ge_le_lintegral₀ hR 1
  rw [one_mul] at hMarkov
  refine (measure_mono hsub).trans (hMarkov.trans ?_)
  rw [lintegral_prod _ hR]
  have hinner : ∀ g : C(Rd d, ℝ), ∫⁻ f : C(Rd d, ℝ), N (g, f) / D (g, f) ∂ν ≤
      ENNReal.ofReal (K / C) := by
    intro g
    have hDg : ∀ f, D (g, f) = D (g, g) := fun _ => rfl
    simp only [hDg, div_eq_mul_inv]
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (hD0 (g, g)))]
    have hN : ∫⁻ f : C(Rd d, ℝ), N (g, f) ∂ν ≤
        ENNReal.ofReal (K * lfppDistance d ξ g) := by
      exact crude_distance_lintegral_le g ξ K hK hmom
    refine (mul_le_mul' hN le_rfl).trans (le_of_eq ?_)
    rw [← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos (hDpos (g, g))]
    congr 1
    have hx := hXpos (g, g)
    dsimp [D, X]
    have hx' : lfppDistance d ξ g ≠ 0 := ne_of_gt hx
    field_simp [hx', ne_of_gt hC]
  calc
    ∫⁻ g : C(Rd d, ℝ), ∫⁻ f : C(Rd d, ℝ), N (g, f) / D (g, f) ∂ν ∂μ
        ≤ ∫⁻ _g : C(Rd d, ℝ), ENNReal.ofReal (K / C) ∂μ := lintegral_mono hinner
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

end HigherDimLQGContinuity
