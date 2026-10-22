import HigherDimLQGMetric.LfppTight.CoupledPointTail
import HigherDimLQGMetric.LfppTight.CoupledLaw
import HigherDimLQGMetric.LfppTight.MetricIdent

/-! The coupled two-sided point estimate, transferred to a normalized LGF. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN e₁)

theorem l6a_centered_point_tails (hL1e : L1e_law)
    {d : ℕ} {κ : Rd d → ℝ} {ξ Q β : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    (hβ0 : 0 < β) (hβ : β < ξ * (Q - Real.sqrt (2 * d)))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (W : WN d → Ω' → ℝ) (hW : HigherDimLFPP.IsWhiteNoise P' W)
    (G : ℝ → Rd d → Ω' → ℝ)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1,
      HigherDimLFPP.IsBandVersion P' W κ ε 1 (G ε))
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ m M ε₀ : ℝ, 0 < m ∧ 0 ≤ M ∧ 0 < ε₀ ∧
      ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        P {ω | l6a_metricOfFieldC ξ (DGZ.aHat P' G ξ ε)⁻¹
            (l6a_toFieldCMap (convMollifyNorm κ ε (h ω))) (0, e₁ d) < m ∨
          M < l6a_metricOfFieldC ξ (DGZ.aHat P' G ξ ε)⁻¹
            (l6a_toFieldCMap (convMollifyNorm κ ε (h ω))) (0, e₁ d)} ≤
          ENNReal.ofReal θ := by
  obtain ⟨Ψ, hΨc, hΨm, hlaw⟩ :=
    l6a_coupled_metric_law hL1e hDGZ.dim hDGZ.kernel P h hh P' W hW G hG
  obtain ⟨m, M, ε₀, hm, hM, hε₀, htail⟩ :=
    l6a_coupled_point_tails hDGZ hAdapter hβ0 hβ P' W hW G hG
      Ψ hΨc hΨm hθ
  refine ⟨m, M, min ε₀ (1 / 2), hm, hM, lt_min hε₀ (by norm_num), ?_⟩
  intro ε hε
  have hε1 : ε ∈ Ioo (0 : ℝ) 1 := by
    exact ⟨hε.1, hε.2.trans_le ((min_le_right _ _).trans (by norm_num))⟩
  let S : Set C(Rd d × Rd d, ℝ) :=
    {D | D (0, e₁ d) < m ∨ M < D (0, e₁ d)}
  have hS : MeasurableSet S := by
    let ev : C(Rd d × Rd d, ℝ) → ℝ := fun D => D (0, e₁ d)
    have hev : Measurable ev := (continuous_eval_const (0, e₁ d)).measurable
    exact (hev measurableSet_Iio).union (hev measurableSet_Ioi)
  change P {ω | l6a_metricOfFieldC ξ (DGZ.aHat P' G ξ ε)⁻¹
      (l6a_toFieldCMap (convMollifyNorm κ ε (h ω))) ∈ S} ≤ ENNReal.ofReal θ
  rw [hlaw ε hε1 ξ (DGZ.aHat P' G ξ ε)⁻¹ S hS]
  have ha : 0 < DGZ.aHat P' G ξ ε :=
    DGZ.aHat_pos (by have := hDGZ.dim; omega) hW (hG ε hε1) ξ
  have hsub : {ω' | l6a_metricOfFieldC ξ (DGZ.aHat P' G ξ ε)⁻¹
        (l6a_toFieldCMap (fun z => l6a_coupledPhi κ W G Ψ ε z ω')) ∈ S} ⊆
      {ω' | DGZ.lfppMetric ξ (l6a_coupledPhi κ W G Ψ ε · ω') 0 (e₁ d) <
          m * DGZ.aHat P' G ξ ε ∨
        M * DGZ.aHat P' G ξ ε <
          DGZ.lfppMetric ξ (l6a_coupledPhi κ W G Ψ ε · ω') 0 (e₁ d)} := by
    intro ω' hw
    have hΦ : Continuous fun z => l6a_coupledPhi κ W G Ψ ε z ω' :=
      ((hG ε hε1).continuous ω').sub continuous_const |>.add (hΨc ω')
    have heq := l6a_metricOfFieldC_eq_normMetricC ξ
      (DGZ.aHat P' G ξ ε)
      (⟨fun z => l6a_coupledPhi κ W G Ψ ε z ω', hΦ⟩ : C(Rd d, ℝ))
    change _ < m ∨ M < _ at hw
    rw [show l6a_toFieldCMap (fun z => l6a_coupledPhi κ W G Ψ ε z ω') =
      (⟨fun z => l6a_coupledPhi κ W G Ψ ε z ω', hΦ⟩ : C(Rd d, ℝ)) from
        dite_eq_left hΦ, heq] at hw
    change (DGZ.normMetricC ξ (l6a_coupledPhi κ W G Ψ ε · ω')
      (DGZ.aHat P' G ξ ε)) (0, e₁ d) < m ∨
      M < (DGZ.normMetricC ξ (l6a_coupledPhi κ W G Ψ ε · ω')
        (DGZ.aHat P' G ξ ε)) (0, e₁ d) at hw
    rw [DGZ.normMetricC_apply hΦ] at hw
    rcases hw with hw | hw
    · left
      simpa only [Prod.fst, Prod.snd, mul_comm] using (inv_mul_lt_iff₀ ha).1 hw
    · right
      simpa only [Prod.fst, Prod.snd, mul_comm] using (lt_inv_mul_iff₀ ha).1 hw
  exact (measure_mono hsub).trans (htail ε
    ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩)

theorem l6a_centered_point_tails_dist (hL1e : L1e_law)
    {d : ℕ} {κ : Rd d → ℝ} {ξ Q β : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    (hβ0 : 0 < β) (hβ : β < ξ * (Q - Real.sqrt (2 * d)))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (W : WN d → Ω' → ℝ) (hW : HigherDimLFPP.IsWhiteNoise P' W)
    (G : ℝ → Rd d → Ω' → ℝ)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1,
      HigherDimLFPP.IsBandVersion P' W κ ε 1 (G ε))
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ m M ε₀ : ℝ, 0 < m ∧ 0 ≤ M ∧ 0 < ε₀ ∧
      ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        P {ω | (DGZ.aHat P' G ξ ε)⁻¹ * HigherDimLFPP.lfppDistOn ξ
            (convMollifyNorm κ ε (h ω)) univ 0 (e₁ d) < m ∨
          M < (DGZ.aHat P' G ξ ε)⁻¹ * HigherDimLFPP.lfppDistOn ξ
            (convMollifyNorm κ ε (h ω)) univ 0 (e₁ d)} ≤
          ENNReal.ofReal θ := by
  obtain ⟨m, M, ε₀, hm, hM, hε₀, htail⟩ :=
    l6a_centered_point_tails hL1e hDGZ hAdapter hβ0 hβ
      P h hh P' W hW G hG hθ
  refine ⟨m, M, ε₀, hm, hM, hε₀, ?_⟩
  intro ε hε
  have hc := l10a_ae_continuous_convMollify hDGZ.dim κ hDGZ.kernel
    P h hh hε.1
  have hevent : P {ω | (DGZ.aHat P' G ξ ε)⁻¹ *
        HigherDimLFPP.lfppDistOn ξ (convMollifyNorm κ ε (h ω))
          univ 0 (e₁ d) < m ∨
      M < (DGZ.aHat P' G ξ ε)⁻¹ *
        HigherDimLFPP.lfppDistOn ξ (convMollifyNorm κ ε (h ω))
          univ 0 (e₁ d)} =
    P {ω | l6a_metricOfFieldC ξ (DGZ.aHat P' G ξ ε)⁻¹
        (l6a_toFieldCMap (convMollifyNorm κ ε (h ω))) (0, e₁ d) < m ∨
      M < l6a_metricOfFieldC ξ (DGZ.aHat P' G ξ ε)⁻¹
        (l6a_toFieldCMap (convMollifyNorm κ ε (h ω))) (0, e₁ d)} := by
    apply measure_congr
    filter_upwards [hc] with ω hω
    have hZ : Continuous (convMollifyNorm κ ε (h ω)) :=
      hω.sub continuous_const
    have heq := l6a_metricOfFieldC_eq_normMetricC ξ
      (DGZ.aHat P' G ξ ε)
      (⟨convMollifyNorm κ ε (h ω), hZ⟩ : C(Rd d, ℝ))
    rw [show l6a_toFieldCMap (convMollifyNorm κ ε (h ω)) =
      (⟨convMollifyNorm κ ε (h ω), hZ⟩ : C(Rd d, ℝ)) from
        dite_eq_left hZ, heq]
    apply propext
    change _ ↔
      (DGZ.normMetricC ξ (convMollifyNorm κ ε (h ω))
        (DGZ.aHat P' G ξ ε)) (0, e₁ d) < m ∨
      M < (DGZ.normMetricC ξ (convMollifyNorm κ ε (h ω))
        (DGZ.aHat P' G ξ ε)) (0, e₁ d)
    rw [DGZ.normMetricC_apply hZ]
    rfl
  rw [hevent]
  exact htail ε hε

end HigherDimLQGMetric
