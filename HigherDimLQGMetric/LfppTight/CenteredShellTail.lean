import HigherDimLQGMetric.LfppTight.CoupledShellGeneral
import HigherDimLQGMetric.LfppTight.CoupledLaw
import HigherDimLQGMetric.LfppTight.MetricIdent
import HigherDimLQGMetric.DGZ.NondegCompactObs

/-! Uniform lower tails of compact shell distance for the centered LGF metric. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN)

theorem l6a_centered_shell_tail (hL1e : L1e_law)
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
    (c : Rd d) {r₁ r₂ θ : ℝ} (hr₂ : 0 < r₂) (hr : r₂ < r₁) (hθ : 0 < θ) :
    ∃ m ε₀ : ℝ, 0 < m ∧ 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀,
      P {ω | DGZ.nd_setInf (sphere c r₂) (sphere c r₁)
        (l6a_metricOfFieldC ξ (DGZ.aHat P' G ξ ε)⁻¹
          (l6a_toFieldCMap (convMollifyNorm κ ε (h ω)))) ≤ m} ≤
            ENNReal.ofReal θ := by
  obtain ⟨Ψ, hΨc, hΨm, hlaw⟩ :=
    l6a_coupled_metric_law hL1e hDGZ.dim hDGZ.kernel P h hh
      P' W hW G hG
  obtain ⟨m, εs, hm, hεs, htail⟩ :=
    l6a_coupled_shell_tail_general hDGZ hAdapter hβ0 hβ
      P' W hW G hG Ψ hΨc hΨm c hr₂ hr hθ
  let ε₀ : ℝ := min εs (1 / 2)
  refine ⟨m, ε₀, hm, lt_min hεs (by norm_num), ?_⟩
  intro ε hε
  have hε1 : ε ∈ Ioo (0 : ℝ) 1 :=
    ⟨hε.1, hε.2.trans_le ((min_le_right _ _).trans (by norm_num))⟩
  let S : Set C(Rd d × Rd d, ℝ) :=
    {D | DGZ.nd_setInf (sphere c r₂) (sphere c r₁) D ≤ m}
  have hS : MeasurableSet S :=
    (isClosed_le (DGZ.nd_continuous_setInf (isCompact_sphere _ _)
      (isCompact_sphere _ _)) continuous_const).measurableSet
  change P {ω | l6a_metricOfFieldC ξ (DGZ.aHat P' G ξ ε)⁻¹
      (l6a_toFieldCMap (convMollifyNorm κ ε (h ω))) ∈ S} ≤ ENNReal.ofReal θ
  rw [hlaw ε hε1 ξ (DGZ.aHat P' G ξ ε)⁻¹ S hS]
  have ha : 0 < DGZ.aHat P' G ξ ε :=
    DGZ.aHat_pos (by have := hDGZ.dim; omega) hW (hG ε hε1) ξ
  have hsub : {ω' | l6a_metricOfFieldC ξ (DGZ.aHat P' G ξ ε)⁻¹
      (l6a_toFieldCMap (fun z => l6a_coupledPhi κ W G Ψ ε z ω')) ∈ S} ⊆
      {ω' | DGZ.lfppSetDist ξ (l6a_coupledPhi κ W G Ψ ε · ω') univ
        (sphere c r₂) (sphere c r₁) ≤ m * DGZ.aHat P' G ξ ε} := by
    intro ω' hw
    have hΦ : Continuous fun z => l6a_coupledPhi κ W G Ψ ε z ω' :=
      ((hG ε hε1).continuous ω').sub continuous_const |>.add (hΨc ω')
    have heq : l6a_toFieldCMap
        (fun z => l6a_coupledPhi κ W G Ψ ε z ω') =
        (⟨fun z => l6a_coupledPhi κ W G Ψ ε z ω', hΦ⟩ : C(Rd d, ℝ)) :=
      dite_eq_left hΦ
    change DGZ.nd_setInf (sphere c r₂) (sphere c r₁)
      (l6a_metricOfFieldC ξ (DGZ.aHat P' G ξ ε)⁻¹
        (l6a_toFieldCMap (l6a_coupledPhi κ W G Ψ ε · ω'))) ≤ m at hw
    rw [heq, l6a_metricOfFieldC_eq_normMetricC] at hw
    change DGZ.nd_setInf (sphere c r₂) (sphere c r₁)
      (DGZ.normMetricC ξ (l6a_coupledPhi κ W G Ψ ε · ω')
        (DGZ.aHat P' G ξ ε)) ≤ m at hw
    rw [DGZ.nd_setInf_normMetricC hΦ ha] at hw
    change DGZ.lfppSetDist ξ (l6a_coupledPhi κ W G Ψ ε · ω') univ
      (sphere c r₂) (sphere c r₁) ≤ m * DGZ.aHat P' G ξ ε
    simpa only [mul_comm (DGZ.aHat P' G ξ ε) m] using (inv_mul_le_iff₀ ha).1 hw
  exact (measure_mono hsub).trans (htail ε
    ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩)

end HigherDimLQGMetric
