import HigherDimLQGContinuity.ConvTransfer.UpperMoment

/-!
# C1: upper modulus with moments for convolution LFPP
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Real
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd WN e₁)

/-- Appendix A C1, using W1 at order `4p` and the uniform real-cutoff
median comparison. -/
theorem convUpperMoment {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hW1 : WNUpperMomentShape d κ) (hT : UHolderTightShape d κ)
    (hN : UNondegShape d κ) (_hQ : UQuantCompShape d κ) :
    ConvUpperMomentShape d κ := by
  intro b μ hb hμ hμ1 σ hσ hσμ p hp hbound
  obtain ⟨Bc, Ac, hBc, hAc, hCentered⟩ :=
    convCenteredEnvelopeMoment hd hκ hW1 hT hN hb hμ hμ1 hσ hσμ hp hbound
  obtain ⟨V, hV, hXmom⟩ := convUniform_sphereMean_exp_moment hd hκ
  let BX : ℝ := 2 * Real.exp (V * (2 * p * b) ^ 2 / 2)
  let C : ℝ := 1 + (2 : ℝ) ^ p * (BX + Bc)
  have hBX : 0 ≤ BX := by dsimp [BX]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, Ac, ?_⟩
  intro ξ hU ε hε Ω _ P _ h hh R hR
  obtain ⟨hFinite, hBmom⟩ := hCentered ξ hU ε hε P h hh R hR
  have haeps : 0 < aEps κ ξ ε := l6a_aEps_pos hd κ hκ ξ hε.1
  have hFullC := l10a_ae_continuous_convMollify hd κ hκ P h hh hε.1
  have hZc : ∀ᵐ ω ∂P, Continuous (convMollifyNorm κ ε (h ω)) := by
    filter_upwards [hFullC] with ω hc
    exact hc.sub continuous_const
  let E : Ω → ℝ := fun ω =>
    (ratEnvelope ξ σ R (l6a_toFieldCMap (convMollifyNorm κ ε (h ω)))).toReal /
      aEps κ ξ ε
  let X : Ω → ℝ := fun ω => l6a_convSphereMean κ ε (h ω)
  let A : Ω → ℝ := fun ω => Real.exp (b * |X ω|)
  let U : Ω → ℝ := fun ω => 2 * A ω * E ω
  have hE0 : ∀ ω, 0 ≤ E ω := fun ω =>
    div_nonneg ENNReal.toReal_nonneg haeps.le
  have hA0 : ∀ ω, 0 ≤ A ω := fun ω => (Real.exp_pos _).le
  have hU0 : ∀ ω, 0 ≤ U ω := fun ω => by dsimp [U]; positivity
  obtain ⟨hG, hX0⟩ := l6a_hasGaussianLaw_sphereMean hd κ hκ P h hh hε.1
  have hXm : AEMeasurable X P := hG.aemeasurable
  have hAm : AEMeasurable A P :=
    Real.measurable_exp.comp_aemeasurable
      ((continuous_abs.measurable.comp_aemeasurable hXm).const_mul b)
  have hFieldm : AEMeasurable
      (fun ω => l6a_toFieldCMap (convMollifyNorm κ ε (h ω))) P :=
    convEnv_aemeasurable_toFieldCMap P
      (fun z ω => convMollifyNorm κ ε (h ω) z)
      (fun z => convEnv_aemeasurable_convMollifyNorm_coord hd hκ hε.1 P h hh z)
      hZc
  have hEm : AEMeasurable E P :=
    ((measurable_ratEnvelope ξ σ R).ennreal_toReal.comp_aemeasurable hFieldm).div_const _
  have hUm : AEMeasurable U P := by
    convert (hAm.mul hEm).const_mul 2 using 1
    funext ω
    dsimp [U]
    ring
  let Hr : Ω → ℝ := fun ω => max 1 (hUm.mk U ω)
  have hHrm : Measurable Hr := measurable_const.max hUm.measurable_mk
  have hHr1 : ∀ ω, 1 ≤ Hr ω := fun ω => le_max_left _ _
  have hUeq : U =ᵐ[P] hUm.mk U := hUm.ae_eq_mk
  have hA2mom : ∫⁻ ω, ENNReal.ofReal (A ω ^ (2 * p)) ∂P ≤ ENNReal.ofReal BX := by
    have h := hXmom P h hh ε hε (2 * p * b)
    have heq (ω : Ω) : A ω ^ (2 * p) =
        Real.exp ((2 * p * b) * |X ω|) := by
      dsimp [A]
      rw [← Real.exp_mul]
      congr 1
      ring
    simpa only [heq, BX, X] using h
  have hUmom : ∫⁻ ω, ENNReal.ofReal (U ω ^ p) ∂P ≤
      ENNReal.ofReal ((2 : ℝ) ^ p * (BX + Bc * (1 + R) ^ Ac)) := by
    apply convEnv_lintegral_rpow_product_bound hp (by norm_num)
      hBX (mul_nonneg hBc (Real.rpow_nonneg (by linarith) _))
      hAm hA0 hE0 hU0
    · filter_upwards [] with ω
      rfl
    · exact hA2mom
    · exact hBmom
  have hHrmom : ∫⁻ ω, ENNReal.ofReal (Hr ω ^ p) ∂P ≤
      ENNReal.ofReal (1 + (2 : ℝ) ^ p * (BX + Bc * (1 + R) ^ Ac)) := by
    have hsub : ∀ᵐ ω ∂P, ENNReal.ofReal (Hr ω ^ p) ≤
        ENNReal.ofReal 1 + ENNReal.ofReal (U ω ^ p) := by
      filter_upwards [hUeq] with ω heq
      have hpow : (max 1 (U ω)) ^ p ≤ 1 + U ω ^ p := by
        rw [Real.rpow_max (by norm_num : (0 : ℝ) ≤ 1) (hU0 ω) hp.le,
          one_rpow]
        exact max_le (le_add_of_nonneg_right (Real.rpow_nonneg (hU0 ω) _))
          (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))
      change ENNReal.ofReal ((max 1 (hUm.mk U ω)) ^ p) ≤
        ENNReal.ofReal 1 + ENNReal.ofReal (U ω ^ p)
      rw [← heq, ← ENNReal.ofReal_add (by norm_num)
        (Real.rpow_nonneg (hU0 ω) _)]
      exact ENNReal.ofReal_le_ofReal hpow
    calc
      ∫⁻ ω, ENNReal.ofReal (Hr ω ^ p) ∂P ≤
          ∫⁻ ω, (ENNReal.ofReal 1 + ENNReal.ofReal (U ω ^ p)) ∂P :=
            lintegral_mono_ae hsub
      _ = ENNReal.ofReal 1 + ∫⁻ ω, ENNReal.ofReal (U ω ^ p) ∂P := by
        rw [lintegral_add_left' (measurable_const.aemeasurable)]
        simp
      _ ≤ ENNReal.ofReal 1 +
          ENNReal.ofReal ((2 : ℝ) ^ p * (BX + Bc * (1 + R) ^ Ac)) :=
            add_le_add le_rfl hUmom
      _ = ENNReal.ofReal (1 + (2 : ℝ) ^ p *
          (BX + Bc * (1 + R) ^ Ac)) := by
            rw [ENNReal.ofReal_add (by norm_num)
              (mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
                (add_nonneg hBX (mul_nonneg hBc (Real.rpow_nonneg (by linarith) _))))]
  have hpoly : 1 + (2 : ℝ) ^ p * (BX + Bc * (1 + R) ^ Ac) ≤
      C * (1 + R) ^ Ac := by
    have hbase : 1 ≤ (1 + R) ^ Ac := Real.one_le_rpow (by linarith) hAc
    have hpow : 0 ≤ (2 : ℝ) ^ p := Real.rpow_nonneg (by norm_num) _
    dsimp [C]
    nlinarith [mul_nonneg (add_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      (mul_nonneg hpow hBX)) (sub_nonneg.2 hbase)]
  refine ⟨Hr, hHrm, hHr1, hHrmom.trans (ENNReal.ofReal_le_ofReal hpoly), ?_⟩
  filter_upwards [hFinite, hZc, hFullC, hUeq] with ω hFin hZω hFullω hEqω
  intro z hz s hs x hx y hy
  let Z : Rd d → ℝ := convMollifyNorm κ ε (h ω)
  let F : C(Rd d, ℝ) := ⟨Z, hZω⟩
  have hfield : convMollify κ ε (h ω) =
      fun u => Z u + X ω := by
    funext u
    dsimp [Z, X, convMollifyNorm, l6a_convSphereMean]
    ring
  have henv : ratEnvelope ξ σ R F =
      ratEnvelope ξ σ R (l6a_toFieldCMap Z) := by
    have hmap : l6a_toFieldCMap Z = F := by
      ext u
      simp only [l6a_toFieldCMap]
      split_ifs with hc
      · rfl
      · exact (hc hZω).elim
    rw [hmap]
  have hEfin : ratEnvelope ξ σ R F ≠ ⊤ := by
    rwa [henv]
  have hEnvBound := lfppDistOn_le_ratEnvelope (ξ := ξ) hσ.le (by linarith [hσμ, hμ1])
    hz hs hx hy F
  have hDcenter : HigherDimLFPP.lfppDistOn ξ Z (ball z (3 / 2 * s)) x y ≤
      2 * (ratEnvelope ξ σ R F).toReal * s ^ σ := by
    have hEnn : ratEnvelope ξ σ R F =
        ENNReal.ofReal (ratEnvelope ξ σ R F).toReal :=
      (ENNReal.ofReal_toReal hEfin).symm
    rw [hEnn] at hEnvBound
    have hE0 : 0 ≤ (ratEnvelope ξ σ R F).toReal := ENNReal.toReal_nonneg
    have hsPow : 0 ≤ s ^ σ := Real.rpow_nonneg hs.1.le _
    have heq : ENNReal.ofReal 2 *
        ENNReal.ofReal (ratEnvelope ξ σ R F).toReal * ENNReal.ofReal (s ^ σ) =
        ENNReal.ofReal (2 * (ratEnvelope ξ σ R F).toReal * s ^ σ) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hE0)]
    rw [heq] at hEnvBound
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (mul_nonneg (by norm_num) hE0) hsPow)).mp hEnvBound
  have hExp : Real.exp (ξ * X ω) ≤ Real.exp (b * |X ω|) := by
    apply Real.exp_le_exp.mpr
    have hmul : |ξ * X ω| ≤ b * |X ω| := by
      rw [abs_mul, abs_of_pos hU.base.xi_pos]
      exact mul_le_mul_of_nonneg_right hU.le_b (abs_nonneg _)
    exact (le_abs_self _).trans hmul
  have hD : HigherDimLFPP.lfppDistOn ξ
      (convMollify κ ε (h ω)) (ball z (3 / 2 * s)) x y ≤
      2 * A ω * (ratEnvelope ξ σ R F).toReal * s ^ σ := by
    rw [hfield, HigherDimLFPP.lfppDistOn_add_const]
    have hD0 : 0 ≤ HigherDimLFPP.lfppDistOn ξ Z (ball z (3 / 2 * s)) x y :=
      HigherDimLFPP.lfppDistOn_nonneg _ _ _ _ _
    calc
      Real.exp (ξ * X ω) * HigherDimLFPP.lfppDistOn ξ Z
          (ball z (3 / 2 * s)) x y ≤
        Real.exp (b * |X ω|) * HigherDimLFPP.lfppDistOn ξ Z
          (ball z (3 / 2 * s)) x y :=
            mul_le_mul_of_nonneg_right hExp hD0
      _ ≤ Real.exp (b * |X ω|) *
          (2 * (ratEnvelope ξ σ R F).toReal * s ^ σ) :=
            mul_le_mul_of_nonneg_left hDcenter (Real.exp_pos _).le
      _ = 2 * A ω * (ratEnvelope ξ σ R F).toReal * s ^ σ := by
        dsimp [A]
        ring
  have hUbound : 2 * A ω * (ratEnvelope ξ σ R F).toReal ≤
      aEps κ ξ ε * Hr ω := by
    have hUV : U ω ≤ Hr ω := by
      rw [hEqω]
      exact le_max_right _ _
    have hEeq : E ω = (ratEnvelope ξ σ R F).toReal / aEps κ ξ ε := by
      dsimp [E]
      rw [← henv]
    have hUeq : U ω = (2 * A ω * (ratEnvelope ξ σ R F).toReal) /
        aEps κ ξ ε := by
      rw [show U ω = 2 * A ω * E ω by rfl, hEeq]
      ring
    rw [hUeq] at hUV
    simpa only [mul_comm] using (div_le_iff₀ haeps).mp hUV
  calc
    HigherDimLFPP.lfppDistOn ξ (convMollify κ ε (h ω))
        (ball z (3 / 2 * s)) x y ≤
          2 * A ω * (ratEnvelope ξ σ R F).toReal * s ^ σ := hD
    _ ≤ aEps κ ξ ε * Hr ω * s ^ σ :=
      mul_le_mul_of_nonneg_right hUbound (Real.rpow_nonneg hs.1.le _)

end HigherDimLQGContinuity
