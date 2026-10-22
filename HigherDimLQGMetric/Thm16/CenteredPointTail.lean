import HigherDimLQGMetric.LfppTight.CoupledLaw
import HigherDimLQGMetric.LfppTight.CoupledPointTail
import HigherDimLQGMetric.LfppTight.MetricIdent
import HigherDimLQGMetric.Law.Main
import HigherDimLQGMetric.Main.ExponentBridge

/-! Uniform point tails for centered convolution LFPP in adapter median units. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN e₁)

private theorem metricOfFieldC_one_apply {d : ℕ} (ξ : ℝ)
    (φ : Rd d → ℝ) (hφ : Continuous φ) (p : Rd d × Rd d) :
    l6a_metricOfFieldC ξ 1 (l6a_toFieldCMap φ) p =
      DGZ.lfppMetric ξ φ p.1 p.2 := by
  rw [show l6a_toFieldCMap φ = (⟨φ, hφ⟩ : C(Rd d, ℝ)) from dite_eq_left hφ,
    l6a_metricOfFieldC]
  change (toCMapRd (1 • fieldLfpp ξ φ)) p = _
  rw [toCMapRd_apply_of_continuous ((continuous_fieldLfpp hφ).const_smul 1)]
  simp only [one_smul, fieldLfpp_eq_lfppDistOn hφ, DGZ.lfppMetric]

theorem l9c_centered_point_tails {d : ℕ} (hd : 3 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hsub : Real.sqrt (2 * d) < distExp d ξ)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ),
      DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WN d → Ω → ℝ) (hW : HigherDimLFPP.IsWhiteNoise P W)
    (G : ℝ → Rd d → Ω → ℝ)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1, HigherDimLFPP.IsBandVersion P W κ ε 1 (G ε)) :
    ∃ m M ε₀ : ℝ, 0 < m ∧ 0 ≤ M ∧ 0 < ε₀ ∧
      ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        (normLGFLaw d) {H |
          DGZ.lfppMetric ξ (convMollifyNorm κ ε H) 0 (e₁ d) <
            m * DGZ.aHat P G ξ ε ∨
          M * DGZ.aHat P G ξ ε <
            DGZ.lfppMetric ξ (convMollifyNorm κ ε H) 0 (e₁ d)} ≤
          (8⁻¹ : ℝ≥0∞) := by
  have hd2 : 2 ≤ d := by omega
  letI : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d hd2).1
  have hn : IsNormalizedLGF id (normLGFLaw d) := (normLGFLaw_spec_holds d hd2).2.1
  obtain ⟨Ψ, hΨc, hΨm, hlaw⟩ :=
    l6a_coupled_metric_law l1e_law hd2 hκ (normLGFLaw d) id hn
      P W hW G hG
  let β : ℝ := ξ * (distExp d ξ - Real.sqrt (2 * d)) / 2
  have hβ0 : 0 < β := by dsimp [β]; positivity
  have hβ : β < ξ * (distExp d ξ - Real.sqrt (2 * d)) := by
    dsimp [β]
    have hpos : 0 < ξ * (distExp d ξ - Real.sqrt (2 * d)) :=
      mul_pos hξ (sub_pos.mpr hsub)
    linarith
  have hDGZ := l10a_dgzHyp hd2 hκ hξ hsub
  obtain ⟨m, M, ε₀, hm, hM, hε₀, htail⟩ :=
    l6a_coupled_point_tails hDGZ (hB2 d κ ξ (distExp d ξ))
      hβ0 hβ P W hW G hG Ψ hΨc hΨm
      (by norm_num : (0 : ℝ) < 1 / 8)
  refine ⟨m, M, min ε₀ (1 / 2), hm, hM,
    lt_min hε₀ (by norm_num), ?_⟩
  intro ε hε
  have hε₀' : ε ∈ Ioo (0 : ℝ) ε₀ :=
    ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
  have hε1 : ε ∈ Ioo (0 : ℝ) 1 :=
    ⟨hε.1, hε.2.trans_le ((min_le_right _ _).trans (by norm_num))⟩
  let p : Rd d × Rd d := (0, e₁ d)
  let S : Set C(Rd d × Rd d, ℝ) :=
    {F | F p < m * DGZ.aHat P G ξ ε ∨
      M * DGZ.aHat P G ξ ε < F p}
  have hS : MeasurableSet S := by
    have heval : Measurable (fun F : C(Rd d × Rd d, ℝ) => F p) :=
      (continuous_eval_const p).measurable
    exact (heval measurableSet_Iio).union (heval measurableSet_Ioi)
  have hnormC : ∀ᵐ H ∂(normLGFLaw d),
      Continuous (convMollifyNorm κ ε H) := by
    filter_upwards [l10a_ae_continuous_convMollify hd2 κ hκ
      (normLGFLaw d) id hn hε.1] with H hH
    exact hH.sub continuous_const
  have hΦc (ω : Ω) : Continuous (l6a_coupledPhi κ W G Ψ ε · ω) :=
    (((hG ε hε1).continuous ω).sub continuous_const).add (hΨc ω)
  have heqL : (normLGFLaw d) {H |
      DGZ.lfppMetric ξ (convMollifyNorm κ ε H) 0 (e₁ d) <
        m * DGZ.aHat P G ξ ε ∨
      M * DGZ.aHat P G ξ ε <
        DGZ.lfppMetric ξ (convMollifyNorm κ ε H) 0 (e₁ d)} =
      (normLGFLaw d) {H |
        l6a_metricOfFieldC ξ 1 (l6a_toFieldCMap (convMollifyNorm κ ε H)) ∈ S} := by
    apply measure_congr
    filter_upwards [hnormC] with H hH
    simp only [S, Set.mem_ofPred_eq, metricOfFieldC_one_apply ξ _ hH p, p]
  have heqR : P {ω |
      l6a_metricOfFieldC ξ 1
        (l6a_toFieldCMap (l6a_coupledPhi κ W G Ψ ε · ω)) ∈ S} =
      P {ω | DGZ.lfppMetric ξ (l6a_coupledPhi κ W G Ψ ε · ω) 0 (e₁ d) <
          m * DGZ.aHat P G ξ ε ∨
        M * DGZ.aHat P G ξ ε <
          DGZ.lfppMetric ξ (l6a_coupledPhi κ W G Ψ ε · ω) 0 (e₁ d)} := by
    congr 1
    ext ω
    simp only [S, Set.mem_ofPred_eq, metricOfFieldC_one_apply ξ _ (hΦc ω) p, p]
  calc
    (normLGFLaw d) {H |
        DGZ.lfppMetric ξ (convMollifyNorm κ ε H) 0 (e₁ d) <
          m * DGZ.aHat P G ξ ε ∨
        M * DGZ.aHat P G ξ ε <
          DGZ.lfppMetric ξ (convMollifyNorm κ ε H) 0 (e₁ d)} =
        (normLGFLaw d) {H |
          l6a_metricOfFieldC ξ 1 (l6a_toFieldCMap (convMollifyNorm κ ε H)) ∈ S} := heqL
    _ = P {ω | l6a_metricOfFieldC ξ 1
        (l6a_toFieldCMap (l6a_coupledPhi κ W G Ψ ε · ω)) ∈ S} := by
          simpa only [Function.id_def] using hlaw ε hε1 ξ 1 S hS
    _ = P {ω | DGZ.lfppMetric ξ (l6a_coupledPhi κ W G Ψ ε · ω) 0 (e₁ d) <
          m * DGZ.aHat P G ξ ε ∨
        M * DGZ.aHat P G ξ ε <
          DGZ.lfppMetric ξ (l6a_coupledPhi κ W G Ψ ε · ω) 0 (e₁ d)} := heqR
    _ ≤ (8⁻¹ : ℝ≥0∞) := by
      have he : ENNReal.ofReal (1 / 8 : ℝ) = (8⁻¹ : ℝ≥0∞) := by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 8)]
        norm_num
      simpa only [l6a_coupledPhi, he] using htail ε hε₀'

end HigherDimLQGMetric
