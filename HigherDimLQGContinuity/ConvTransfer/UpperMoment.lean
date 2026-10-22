import HigherDimLQGContinuity.ConvTransfer.LawMoments

/-!
# Upper moments of the centered convolution envelope
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
open HigherDimLQGMetric.DGZ

/-- The centered convolution envelope, divided by the pinned lower median,
has the moment needed for the final C1 factorization. -/
theorem convCenteredEnvelopeMoment {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hW1 : WNUpperMomentShape d κ) (hT : UHolderTightShape d κ)
    (hN : UNondegShape d κ)
    {b μ σ p : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hσ : 0 < σ) (hσμ : σ < μ) (hp : 0 < p)
    (hbound : 32 * p * b ≤ Real.sqrt (2 * d)) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
      ∀ (ξ : ℝ), UHyp d κ b μ ξ → ∀ ε ∈ Ioo (0 : ℝ) 1,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ R : ℝ, 1 ≤ R →
        (∀ᵐ ω ∂P, ratEnvelope ξ σ R
          (l6a_toFieldCMap (convMollifyNorm κ ε (h ω))) ≠ ⊤) ∧
        ∫⁻ ω, ENNReal.ofReal (((ratEnvelope ξ σ R
          (l6a_toFieldCMap (convMollifyNorm κ ε (h ω)))).toReal /
          aEps κ ξ ε) ^ (2 * p)) ∂P ≤ ENNReal.ofReal (C * (1 + R) ^ A) := by
  obtain ⟨c, Cmed, hc, hCmed, hmodel⟩ :=
    aEps_comparable_model_unif hd hκ hT hN hb hμ
  obtain ⟨CW, AW, hWmom⟩ := hW1 b μ hb hμ hμ1 σ hσ hσμ (4 * p)
    (by positivity) (by nlinarith [hbound])
  obtain ⟨CG, AG, hCG, hAG, hGmom⟩ :=
    convModelGamma_poly_moment hd hκ (show 0 < 4 * p * b by positivity)
  let q : ℝ := 2 * p
  let K : ℝ := 20 / c
  let BWcoef : ℝ := max 1 CW * (8 : ℝ) ^ |AW|
  let A : ℝ := AG + |AW|
  let C : ℝ := K ^ q * (CG + BWcoef)
  have hK : 0 < K := div_pos (by norm_num) hc
  have hBWcoef : 0 ≤ BWcoef := by dsimp [BWcoef]; positivity
  have hA : 0 ≤ A := add_nonneg hAG (abs_nonneg AW)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, A, hC, hA, ?_⟩
  intro ξ hU ε hε Ω _ P _ h hh R hR
  obtain ⟨N, r, hr, hr1, hεeq, Ω', inst', P', W₀, W', H, T, I, m,
    hP', hW₀, hH, hBand, hIc, hIm, hmm, hIeq, hm,
    hZc, Φ, hΦc, hΦeq, hLaw, hmedlo, hmedhi⟩ :=
      hmodel ξ hU ε hε P h hh
  letI : MeasurableSpace Ω' := inst'
  letI : IsProbabilityMeasure P' := hP'
  let S : ℝ := 2 * R + 6
  have hS : 1 ≤ S := by dsimp [S]; linarith
  have hS8 : 1 + S ≤ 8 * (1 + R) := by dsimp [S]; linarith
  obtain ⟨Hr, hHrm, hHr1, hHrMom, hGood⟩ :=
    hWmom ξ hU Ω' P' W' H hH N S hS
  have hRatio := convEnv_model_ratio_bound hd hU.base.xi_pos hU.le_b hσ.le
    hR hr hr1 hc hH N hmedlo hBand.continuous hIc hΦc m hΦeq
    Hr hHr1 hGood
  have hΓm : AEMeasurable (convModelGamma R T I m) P' :=
    convModelGamma_aemeasurable hd hκ hr hr1 hW₀ hH.whiteNoise hBand
      hIc hIeq m hmm hR
  have hXm : AEMeasurable
      (fun ω => Real.exp (b * convModelGamma R T I m ω)) P' :=
    Real.measurable_exp.comp_aemeasurable (hΓm.const_mul b)
  have hXmom : ∫⁻ ω, ENNReal.ofReal
      ((Real.exp (b * convModelGamma R T I m ω)) ^ (2 * q)) ∂P' ≤
      ENNReal.ofReal (CG * (1 + R) ^ AG) := by
    have hg := hGmom hε hr hr1 hW₀ hH.whiteNoise hBand hIc hIeq m hmm hm hR
    have heq : ∀ ω, (Real.exp (b * convModelGamma R T I m ω)) ^ (2 * q) =
        Real.exp ((4 * p * b) * convModelGamma R T I m ω) := by
      intro ω
      rw [← Real.exp_mul]
      congr 1
      dsimp [q]
      ring
    simpa only [heq] using hg
  have hBW : 0 ≤ BWcoef * (1 + R) ^ |AW| :=
    mul_nonneg hBWcoef (Real.rpow_nonneg (by linarith) _)
  have hWreal : CW * (1 + S) ^ AW ≤ BWcoef * (1 + R) ^ |AW| := by
    have hpow₁ : (1 + S) ^ AW ≤ (1 + S) ^ |AW| :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (le_abs_self AW)
    have hpow₂ : (1 + S) ^ |AW| ≤
        (8 : ℝ) ^ |AW| * (1 + R) ^ |AW| := by
      have hh := Real.rpow_le_rpow (by linarith : 0 ≤ 1 + S) hS8 (abs_nonneg AW)
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8)
        (by linarith : 0 ≤ 1 + R)] at hh
      exact hh
    have hCW : CW ≤ max 1 CW := le_max_right _ _
    have hmax : 0 ≤ max 1 CW :=
      (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
    calc
      CW * (1 + S) ^ AW ≤ max 1 CW * (1 + S) ^ AW :=
        mul_le_mul_of_nonneg_right hCW (Real.rpow_nonneg (by linarith) _)
      _ ≤ max 1 CW * (1 + S) ^ |AW| :=
        mul_le_mul_of_nonneg_left hpow₁ hmax
      _ ≤ BWcoef * (1 + R) ^ |AW| := by
        dsimp [BWcoef]
        nlinarith [mul_le_mul_of_nonneg_left hpow₂ hmax]
  have hYmom : ∫⁻ ω, ENNReal.ofReal (Hr ω ^ (2 * q)) ∂P' ≤
      ENNReal.ofReal (BWcoef * (1 + R) ^ |AW|) := by
    have heq : 2 * q = 4 * p := by dsimp [q]; ring
    rw [heq]
    exact hHrMom.trans (ENNReal.ofReal_le_ofReal (by simpa only [S] using hWreal))
  let EY : Ω' → ℝ := fun ω =>
    (ratEnvelope ξ σ R ⟨fun z => Φ z ω, hΦc ω⟩).toReal / aEps κ ξ ε
  have haeps : 0 < aEps κ ξ ε :=
    lt_of_lt_of_le (mul_pos (mul_pos hc (by linarith : 0 < r))
      (tight_aQ_pos (by omega : 0 < d) hH ξ N (by norm_num) (by norm_num))) hmedlo
  have hEY0 : ∀ ω, 0 ≤ EY ω := fun ω =>
    div_nonneg ENNReal.toReal_nonneg haeps.le
  have hEYmom : ∫⁻ ω, ENNReal.ofReal (EY ω ^ q) ∂P' ≤
      ENNReal.ofReal (K ^ q *
        (CG * (1 + R) ^ AG + BWcoef * (1 + R) ^ |AW|)) := by
    exact convEnv_lintegral_rpow_product_bound (by dsimp [q]; positivity)
      hK.le (mul_nonneg hCG.le (Real.rpow_nonneg (by linarith) _)) hBW
      hXm (fun ω => (Real.exp_pos _).le)
      (fun ω => (show (0 : ℝ) ≤ 1 by norm_num).trans (hHr1 ω)) hEY0
      (by simpa only [EY, K] using hRatio) hXmom hYmom
  let X : Ω → C(Rd d, ℝ) := fun ω =>
    l6a_toFieldCMap (convMollifyNorm κ ε (h ω))
  let Y : Ω' → C(Rd d, ℝ) := fun ω => ⟨fun z => Φ z ω, hΦc ω⟩
  let F : C(Rd d, ℝ) → ℝ≥0∞ := fun φ =>
    ENNReal.ofReal (((ratEnvelope ξ σ R φ).toReal / aEps κ ξ ε) ^ q)
  have hFm : Measurable F := by
    dsimp [F]
    exact ENNReal.measurable_ofReal.comp
      ((Real.continuous_rpow_const (by dsimp [q]; positivity)).measurable.comp
        ((measurable_ratEnvelope ξ σ R).ennreal_toReal.div_const _))
  have hXmField : AEMeasurable X P :=
    convEnv_aemeasurable_toFieldCMap P
      (fun z ω => convMollifyNorm κ ε (h ω) z)
      (fun z => convEnv_aemeasurable_convMollifyNorm_coord hd hκ hε.1 P h hh z)
      hZc
  have hYmField : AEMeasurable Y P' :=
    convEnv_aemeasurable_modelField hH (by linarith : 0 < r) N hBand
      hIm m hmm hΦc hΦeq
  have hLawMom := convEnv_lintegral_of_field_law P P' X Y hXmField hYmField
    hLaw F hFm
  have hFinite : ∀ᵐ ω ∂P, ratEnvelope ξ σ R
      (l6a_toFieldCMap (convMollifyNorm κ ε (h ω))) ≠ ⊤ := by
    let B : Set C(Rd d, ℝ) := {φ | ratEnvelope ξ σ R φ = ⊤}
    have hBm : MeasurableSet B :=
      (measurable_ratEnvelope ξ σ R) (measurableSet_singleton ⊤)
    have hModelBound := convEnv_model_bound hd hU.base.xi_pos hU.le_b
      hσ.le hR hr hr1 hH N hBand.continuous hIc hΦc m hΦeq Hr hHr1 hGood
    have hModelZero : P' {ω | Y ω ∈ B} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hModelBound] with ω hω
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hω
    have hOrigZero : P {ω | X ω ∈ B} = 0 := by
      rw [hLaw B hBm]
      exact hModelZero
    simpa only [B, X, Set.mem_ofPred_eq] using
      (measure_eq_zero_iff_ae_notMem.mp hOrigZero)
  have hreal : K ^ q *
      (CG * (1 + R) ^ AG + BWcoef * (1 + R) ^ |AW|) ≤
        C * (1 + R) ^ A := by
    have hbase : 1 ≤ 1 + R := by linarith
    have hpowAG : (1 + R) ^ AG ≤ (1 + R) ^ A :=
      Real.rpow_le_rpow_of_exponent_le hbase (by dsimp [A]; linarith [abs_nonneg AW])
    have hpowAW : (1 + R) ^ |AW| ≤ (1 + R) ^ A :=
      Real.rpow_le_rpow_of_exponent_le hbase (by dsimp [A]; linarith)
    have hKq : 0 ≤ K ^ q := Real.rpow_nonneg hK.le _
    dsimp [C]
    nlinarith [mul_le_mul_of_nonneg_left hpowAG hCG.le,
      mul_le_mul_of_nonneg_left hpowAW hBWcoef]
  refine ⟨hFinite, ?_⟩
  calc
    ∫⁻ ω, ENNReal.ofReal (((ratEnvelope ξ σ R
        (l6a_toFieldCMap (convMollifyNorm κ ε (h ω)))).toReal /
        aEps κ ξ ε) ^ (2 * p)) ∂P = ∫⁻ ω, F (X ω) ∂P := rfl
    _ = ∫⁻ ω, F (Y ω) ∂P' := hLawMom
    _ ≤ ENNReal.ofReal (K ^ q *
        (CG * (1 + R) ^ AG + BWcoef * (1 + R) ^ |AW|)) := hEYmom
    _ ≤ ENNReal.ofReal (C * (1 + R) ^ A) := ENNReal.ofReal_le_ofReal hreal

end HigherDimLQGContinuity
