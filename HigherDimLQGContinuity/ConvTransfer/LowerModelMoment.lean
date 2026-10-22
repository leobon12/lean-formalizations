import HigherDimLQGContinuity.ConvTransfer.LowerMoment
import HigherDimLQGMetric.LfppTight.MetricIdent
import HigherDimLQGMetric.LfppTight.CrossGeom
import HigherDimLQGMetric.LfppTight.CrossMeas

/-! Centered convolution crossing moments through the white-noise model. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Real
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLQGMetric.DGZ
open HigherDimLFPP (Rd WN)

/-- The continuous-map observable is the global LFPP distance functional. -/
theorem convCross_metricOfFieldC_apply {d : ℕ} (ξ : ℝ)
    (φ : C(Rd d, ℝ)) (x y : Rd d) :
    l6a_metricOfFieldC ξ 1 φ (x, y) = lfppMetric ξ φ x y := by
  have h := l6a_metricOfFieldC_eq_normMetricC ξ 1 φ
  simp only [inv_one] at h
  rw [h, normMetricC_apply φ.continuous]
  simp

/-- The centered convolution crossing has a uniform inverse moment of any
order. This retains its own median factor for the scalar restoration. -/
theorem convCross_centered_inverse_moment {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hW2 : WNInvCrossShape d κ)
    (hT : UHolderTightShape d κ) (hN : UNondegShape d κ)
    {b μ : ℝ} (hb : 0 < b) (hμ : 0 < μ)
    (z : Rd d) {a c q : ℝ} (ha : 0 < a) (hac : a < c) (hq : 0 < q) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ξ : ℝ, UHyp d κ b μ ξ → ∀ ε ∈ Ioo (0 : ℝ) 1,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d),
        IsNormalizedLGF h P →
        ∫⁻ ω, ((ENNReal.ofReal (aEps κ ξ ε))⁻¹ *
          infPairs (l6a_metricOfFieldC ξ 1
            (l6a_toFieldCMap (convMollifyNorm κ ε (h ω))))
            (sphere z a) (sphere z c))⁻¹ ^ (2 * q) ∂P ≤ ENNReal.ofReal C := by
  classical
  let ρ : ℝ := (c - a) / (8 * (Real.sqrt d + 1))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  obtain ⟨Y, hY, hcover⟩ := adapter_sphere_cover ha hρ (c := z)
  have hYne : Y.Nonempty := by
    have hsphere : (sphere z a).Nonempty := by
      refine ⟨z + a • HigherDimLFPP.e₁ d, ?_⟩
      change dist (z + a • HigherDimLFPP.e₁ d) z = a
      rw [dist_eq_norm]
      have he : z + a • HigherDimLFPP.e₁ d - z = a • HigherDimLFPP.e₁ d := by abel
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos ha,
        HigherDimLFPP.norm_e₁ (by omega : 0 < d), mul_one]
    obtain ⟨x, hx⟩ := hsphere
    obtain ⟨v, hv, _⟩ := hcover (by norm_num : (1 / 2 : ℝ) < 1) hx
    exact ⟨v, hv⟩
  let R : ℝ := 2 * (‖z‖ + a) + Real.sqrt d * (2 * ρ + 1) + 1
  have hR : 1 ≤ R := by
    dsimp [R]
    have hbase : 0 ≤ 2 * (‖z‖ + a) := by positivity
    have hprod : 0 ≤ Real.sqrt d * (2 * ρ + 1) := by positivity
    linarith
  obtain ⟨cm, CM, hcm, hCM, hmodel⟩ :=
    aEps_comparable_model_unif hd hκ hT hN hb hμ
  obtain ⟨Cg, Ag, hCg, hAg, hGammaMom⟩ :=
    convModelGamma_poly_moment hd hκ (show 0 < 4 * q * b by positivity)
  obtain ⟨Cy, hCy, hMinMom⟩ :=
    convCross_finite_min_moment hW2 hb hμ hρ
      (show 0 < 4 * q by positivity) Y hYne
  let Bg : ℝ := Cg * (1 + R) ^ Ag
  let C : ℝ := CM ^ (2 * q) * (Bg + Cy)
  have hBg : 0 ≤ Bg := mul_nonneg hCg.le
    (Real.rpow_nonneg (by linarith : 0 ≤ 1 + R) _)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ξ hU ε hε Ω _ P _ h hh
  obtain ⟨N, r, hr, hr1, hεeq, Ω', inst', P', W₀, W', H, T, I, m,
    hP', hW₀, hH, hBand, hIc, hIm, hmm, hIeq, hm, hZc,
    Φ, hΦc, hΦeq, hLaw, hmedLo, hmedHi⟩ :=
      hmodel ξ hU ε hε P h hh
  letI : MeasurableSpace Ω' := inst'
  letI : IsProbabilityMeasure P' := hP'
  have hr0 : 0 < r := by linarith
  have haQ : 0 < aQ P' H ξ N 2⁻¹ :=
    tight_aQ_pos (by omega : 0 < d) hH ξ N (by norm_num) (by norm_num)
  have haeps : 0 < aEps κ ξ ε := l6a_aEps_pos hd κ hκ ξ hε.1
  let F : C(Rd d, ℝ) → ℝ≥0∞ := fun φ =>
    ((ENNReal.ofReal (aEps κ ξ ε))⁻¹ *
      infPairs (l6a_metricOfFieldC ξ 1 φ) (sphere z a) (sphere z c))⁻¹ ^ (2 * q)
  have hFm : Measurable F :=
    ((measurable_const.mul
      ((l6a_measurable_infPairs (sphere z a) (sphere z c)).comp
        (l6a_measurable_metricOfFieldC ξ 1))).inv.pow_const _)
  have hOrigM : AEMeasurable
      (fun ω => l6a_toFieldCMap (convMollifyNorm κ ε (h ω))) P :=
    convEnv_aemeasurable_toFieldCMap P
      (fun x ω => convMollifyNorm κ ε (h ω) x)
      (fun x => convEnv_aemeasurable_convMollifyNorm_coord hd hκ hε.1 P h hh x)
      hZc
  have hModelM : AEMeasurable
      (fun ω => (⟨fun x => Φ x ω, hΦc ω⟩ : C(Rd d, ℝ))) P' :=
    convEnv_aemeasurable_modelField hH hr0 N hBand hIm m hmm hΦc hΦeq
  have hLawInt := convEnv_lintegral_of_field_law P P'
    (fun ω => l6a_toFieldCMap (convMollifyNorm κ ε (h ω)))
    (fun ω => (⟨fun x => Φ x ω, hΦc ω⟩ : C(Rd d, ℝ)))
    hOrigM hModelM hLaw F hFm
  rw [show (∫⁻ ω, ((ENNReal.ofReal (aEps κ ξ ε))⁻¹ *
      infPairs (l6a_metricOfFieldC ξ 1
        (l6a_toFieldCMap (convMollifyNorm κ ε (h ω))))
        (sphere z a) (sphere z c))⁻¹ ^ (2 * q) ∂P) =
      ∫⁻ ω, F (l6a_toFieldCMap (convMollifyNorm κ ε (h ω))) ∂P by rfl,
    hLawInt]
  let M : Ω' → ℝ := fun ω => Y.inf' hYne
    (fun v => acrossDist ξ (fun x => H N x ω) v (2 * ρ) ρ)
  have hMpos (ω : Ω') : 0 < M ω := by
    obtain ⟨v, hv, hvM⟩ := Finset.exists_mem_eq_inf' hYne
      (fun v => acrossDist ξ (fun x => H N x ω) v (2 * ρ) ρ)
    rw [show M ω = acrossDist ξ (fun x => H N x ω) v (2 * ρ) ρ from hvM]
    exact acrossDist_pos (by omega : 0 < d) ((hH.band N).continuous ω)
      hρ.le (by linarith)
  let X : Ω' → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (Real.exp (b * convModelGamma R T I m ω))
  let V : Ω' → ℝ≥0∞ := fun ω =>
    (ENNReal.ofReal (M ω / aQ P' H ξ N 2⁻¹))⁻¹
  have hXm : AEMeasurable X P' := by
    have hGm := convModelGamma_aemeasurable hd hκ hr hr1 hW₀ hH.whiteNoise
      hBand hIc hIeq m hmm hR
    exact (Real.measurable_exp.comp_aemeasurable
      (hGm.const_mul b)).ennreal_ofReal
  have hXmom : ∫⁻ ω, X ω ^ (4 * q) ∂P' ≤ ENNReal.ofReal Bg := by
    have hh := hGammaMom hε hr hr1 hW₀ hH.whiteNoise hBand hIc hIeq
      m hmm hm hR
    have heq (ω : Ω') : X ω ^ (4 * q) =
        ENNReal.ofReal (Real.exp ((4 * q * b) * convModelGamma R T I m ω)) := by
      dsimp [X]
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le
        (show 0 ≤ 4 * q by positivity), ← Real.exp_mul]
      congr 1
      ring_nf
    simpa only [heq, Bg] using hh
  have hVmom : ∫⁻ ω, V ω ^ (4 * q) ∂P' ≤ ENNReal.ofReal Cy :=
    hMinMom ξ hU P' W' H hH N
  have hpoint (ω : Ω') :
      ((ENNReal.ofReal (aEps κ ξ ε))⁻¹ *
        infPairs (l6a_metricOfFieldC ξ 1
          (⟨fun x => Φ x ω, hΦc ω⟩ : C(Rd d, ℝ)))
          (sphere z a) (sphere z c))⁻¹ ≤
      ENNReal.ofReal CM * X ω * V ω := by
    have hLower := convCross_model_infPairs_lower hH N m hBand.continuous hIc
      hΦc hr hr1 hU.base.xi_pos hU.le_b ha hac (rfl : ρ = _)
      (rfl : R = _) hΦeq Y hYne hY hcover ω
    have hMetric : infPairs (l6a_metricOfFieldC ξ 1
        (⟨fun x => Φ x ω, hΦc ω⟩ : C(Rd d, ℝ)))
        (sphere z a) (sphere z c) =
        infPairs (fun p : Rd d × Rd d => lfppMetric ξ (fun x => Φ x ω) p.1 p.2)
          (sphere z a) (sphere z c) := by
      congr 1
      funext p
      exact convCross_metricOfFieldC_apply ξ _ p.1 p.2
    dsimp [X, V]
    rw [hMetric]
    simpa only [ENNReal.ofReal_mul hCM.le] using
      (convCross_ratio_inverse_bound hr0 haQ haeps hCM (hMpos ω)
        hmedHi hLower)
  have hbound := convCross_lintegral_product_bound (P := P')
    (Z := fun ω => ((ENNReal.ofReal (aEps κ ξ ε))⁻¹ *
      infPairs (l6a_metricOfFieldC ξ 1
        (⟨fun x => Φ x ω, hΦc ω⟩ : C(Rd d, ℝ)))
        (sphere z a) (sphere z c))⁻¹)
    (X := X) (Y := V) (q := 2 * q) (C := CM)
    (show 0 < 2 * q by positivity) hCM.le hBg hCy hXm
    (Filter.Eventually.of_forall hpoint) (by simpa only [show 2 * (2 * q) = 4 * q by ring] using hXmom)
    (by simpa only [show 2 * (2 * q) = 4 * q by ring] using hVmom)
  simpa only [F, C] using hbound

end HigherDimLQGContinuity
