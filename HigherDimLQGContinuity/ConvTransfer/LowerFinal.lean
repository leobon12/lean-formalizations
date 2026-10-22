import HigherDimLQGContinuity.ConvTransfer.LowerModelMoment

/-! C2: inverse moments for convolution LFPP across Euclidean annuli. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Real
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- Appendix A C2: a fixed annular crossing retains all inverse moments
under the real-cutoff convolution and median normalization. -/
theorem convInvCross {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hW2 : WNInvCrossShape d κ) (hT : UHolderTightShape d κ)
    (hN : UNondegShape d κ) (_hQ : UQuantCompShape d κ) :
    ConvInvCrossShape d κ := by
  intro b μ hb hμ z a c ha hac q hq
  obtain ⟨Bc, hBc, hCentered⟩ :=
    convCross_centered_inverse_moment hd hκ hW2 hT hN hb hμ z ha hac hq
  obtain ⟨V, hV, hXmom⟩ := convUniform_sphereMean_exp_moment hd hκ
  let BX : ℝ := 2 * Real.exp (V * (2 * q * b) ^ 2 / 2)
  let C : ℝ := BX + Bc
  have hBX : 0 ≤ BX := by dsimp [BX]; positivity
  refine ⟨C, ?_⟩
  intro ξ hU ε hε Ω _ P _ h hh
  have haeps : 0 < aEps κ ξ ε := l6a_aEps_pos hd κ hκ ξ hε.1
  have hFullC := l10a_ae_continuous_convMollify hd κ hκ P h hh hε.1
  have hZc : ∀ᵐ ω ∂P, Continuous (convMollifyNorm κ ε (h ω)) := by
    filter_upwards [hFullC] with ω hc
    exact hc.sub continuous_const
  let G : Ω → ℝ≥0∞ := fun ω =>
    infPairs (l6a_metricOfFieldC ξ 1
      (l6a_toFieldCMap (convMollifyNorm κ ε (h ω))))
      (sphere z a) (sphere z c)
  let X : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (Real.exp (b * |l6a_convSphereMean κ ε (h ω)|))
  let Y : Ω → ℝ≥0∞ := fun ω =>
    ((ENNReal.ofReal (aEps κ ξ ε))⁻¹ * G ω)⁻¹
  let Z : Ω → ℝ≥0∞ := fun ω =>
    ((ENNReal.ofReal (aEps κ ξ ε))⁻¹ *
      infPairs (lfppDist κ ξ ε (h ω)) (sphere z a) (sphere z c))⁻¹
  obtain ⟨hGaussian, hMean⟩ :=
    l6a_hasGaussianLaw_sphereMean hd κ hκ P h hh hε.1
  have hXm : AEMeasurable X P :=
    (Real.measurable_exp.comp_aemeasurable
      ((continuous_abs.measurable.comp_aemeasurable
        hGaussian.aemeasurable).const_mul b)).ennreal_ofReal
  have hXmom2 : ∫⁻ ω, X ω ^ (2 * q) ∂P ≤ ENNReal.ofReal BX := by
    have hm := hXmom P h hh ε hε (2 * q * b)
    have heq (ω : Ω) : X ω ^ (2 * q) =
        ENNReal.ofReal (Real.exp ((2 * q * b) *
          |l6a_convSphereMean κ ε (h ω)|)) := by
      dsimp [X]
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le
        (show 0 ≤ 2 * q by positivity), ← Real.exp_mul]
      congr 1
      ring_nf
    simpa only [heq, BX] using hm
  have hYmom2 : ∫⁻ ω, Y ω ^ (2 * q) ∂P ≤ ENNReal.ofReal Bc :=
    hCentered ξ hU ε hε P h hh
  have hpoint : ∀ᵐ ω ∂P, Z ω ≤ X ω * Y ω := by
    filter_upwards [hZc] with ω hZω
    let F : C(Rd d, ℝ) := ⟨convMollifyNorm κ ε (h ω), hZω⟩
    have hmap : l6a_toFieldCMap (convMollifyNorm κ ε (h ω)) = F := by
      ext u
      simp only [l6a_toFieldCMap]
      split_ifs
      rfl
    have hmetric : infPairs (lfppDist κ ξ ε (h ω))
        (sphere z a) (sphere z c) =
        ENNReal.ofReal (Real.exp (ξ * l6a_convSphereMean κ ε (h ω))) * G ω := by
      have heq : (lfppDist κ ξ ε (h ω) : Rd d × Rd d → ℝ) =
          fun p => Real.exp (ξ * l6a_convSphereMean κ ε (h ω)) *
            l6a_metricOfFieldC ξ 1 F p := by
        funext p
        rw [l6a_lfppDist_sphereMean_split]
        congr 1
        exact (convCross_metricOfFieldC_apply ξ F p.1 p.2).symm
      rw [heq, l6a_infPairs_mul _ _ _ (Real.exp_pos _)]
      simp only [G, hmap]
    have hfac0 : ENNReal.ofReal
        (Real.exp (ξ * l6a_convSphereMean κ ε (h ω))) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    have hfacTop : ENNReal.ofReal
        (Real.exp (ξ * l6a_convSphereMean κ ε (h ω))) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    have hExp : Real.exp (-(ξ * l6a_convSphereMean κ ε (h ω))) ≤
        Real.exp (b * |l6a_convSphereMean κ ε (h ω)|) := by
      apply Real.exp_le_exp.mpr
      have hh : |ξ * l6a_convSphereMean κ ε (h ω)| ≤
          b * |l6a_convSphereMean κ ε (h ω)| := by
        rw [abs_mul, abs_of_pos hU.base.xi_pos]
        exact mul_le_mul_of_nonneg_right hU.le_b (abs_nonneg _)
      linarith [neg_le_of_abs_le hh]
    dsimp [Z, X, Y]
    rw [hmetric]
    have heq : (ENNReal.ofReal (aEps κ ξ ε))⁻¹ *
        (ENNReal.ofReal (Real.exp (ξ * l6a_convSphereMean κ ε (h ω))) * G ω) =
        ENNReal.ofReal (Real.exp (ξ * l6a_convSphereMean κ ε (h ω))) *
          ((ENNReal.ofReal (aEps κ ξ ε))⁻¹ * G ω) := by ac_rfl
    rw [heq, ENNReal.mul_inv (Or.inl hfac0) (Or.inl hfacTop),
      ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal hExp) zero_le
  have hbound := convCross_lintegral_product_bound (Z := Z) (X := X) (Y := Y)
    (q := q) (C := 1) hq (by norm_num) hBX hBc hXm
    (by simpa only [ENNReal.ofReal_one, one_mul] using hpoint)
    hXmom2 hYmom2
  simpa only [Z, C, one_rpow, one_mul,
    ENNReal.ofReal_inv_of_pos haeps] using hbound

end HigherDimLQGContinuity
