import HigherDimLQGMetric.LfppTight.CrossSphereSplit
import HigherDimLQGMetric.LfppTight.CrossMeas
import HigherDimLQGMetric.LfppTight.LawInput
import HigherDimLQGMetric.LfppTight.CoupledLaw

/-! L1e transfers crossing probabilities from the normalized LGF to the coupled field. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN)

theorem l6a_cross_coupled_law (hL1e : L1e_law)
    {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (W : WN d → Ω' → ℝ) (hW : HigherDimLFPP.IsWhiteNoise P' W)
    (G : ℝ → Rd d → Ω' → ℝ)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1,
      HigherDimLFPP.IsBandVersion P' W κ ε 1 (G ε)) :
    ∃ Ψ : Rd d → Ω' → ℝ,
      (∀ ω', Continuous fun z => Ψ z ω') ∧
      (∀ z, Measurable (Ψ z)) ∧
      ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ (A B C : Set (Rd d)) (c : ℝ),
        P {ω | supPairs (lfppDist κ ξ ε (h ω)) A ≤
          ENNReal.ofReal c * infPairs (lfppDist κ ξ ε (h ω)) B C} =
        P' {ω' | supPairs
          (fun p : Rd d × Rd d => DGZ.lfppMetric ξ
            (l6a_coupledPhi κ W G Ψ ε · ω') p.1 p.2) A ≤
          ENNReal.ofReal c * infPairs
            (fun p : Rd d × Rd d => DGZ.lfppMetric ξ
              (l6a_coupledPhi κ W G Ψ ε · ω') p.1 p.2) B C} := by
  obtain ⟨Ψ, hΨc, hΨm, hlaw⟩ :=
    l6a_coupled_metric_law hL1e hd hκ P h hh P' W hW G hG
  refine ⟨Ψ, hΨc, hΨm, ?_⟩
  intro ε hε A B C c
  let S : Set C(Rd d × Rd d, ℝ) :=
    {D | supPairs D A ≤ ENNReal.ofReal c * infPairs D B C}
  have hS : MeasurableSet S := l6a_measurableSet_cross A B C c
  have hc := l10a_ae_continuous_convMollify hd κ hκ P h hh hε.1
  have hleft : P {ω | supPairs (lfppDist κ ξ ε (h ω)) A ≤
        ENNReal.ofReal c * infPairs (lfppDist κ ξ ε (h ω)) B C} =
      P {ω | l6a_metricOfFieldC ξ 1
        (l6a_toFieldCMap (convMollifyNorm κ ε (h ω))) ∈ S} := by
    apply measure_congr
    filter_upwards [hc] with ω hω
    exact propext (l6a_cross_sphereMean_iff κ ξ ε (h ω) hω A B C c)
  have hright : P' {ω' | l6a_metricOfFieldC ξ 1
        (l6a_toFieldCMap (fun z => l6a_coupledPhi κ W G Ψ ε z ω')) ∈ S} =
      P' {ω' | supPairs
          (fun p : Rd d × Rd d => DGZ.lfppMetric ξ
            (l6a_coupledPhi κ W G Ψ ε · ω') p.1 p.2) A ≤
          ENNReal.ofReal c * infPairs
            (fun p : Rd d × Rd d => DGZ.lfppMetric ξ
              (l6a_coupledPhi κ W G Ψ ε · ω') p.1 p.2) B C} := by
    apply measure_congr
    apply Filter.Eventually.of_forall
    intro ω'
    have hΦ : Continuous fun z => l6a_coupledPhi κ W G Ψ ε z ω' :=
      ((hG ε hε).continuous ω').sub continuous_const |>.add (hΨc ω')
    have heq : (l6a_metricOfFieldC ξ 1
        (l6a_toFieldCMap (fun z => l6a_coupledPhi κ W G Ψ ε z ω')) :
        Rd d × Rd d → ℝ) =
        fun p => DGZ.lfppMetric ξ
          (l6a_coupledPhi κ W G Ψ ε · ω') p.1 p.2 := by
      funext p
      rw [show l6a_toFieldCMap (fun z => l6a_coupledPhi κ W G Ψ ε z ω') =
        (⟨fun z => l6a_coupledPhi κ W G Ψ ε z ω', hΦ⟩ : C(Rd d, ℝ)) from
          dite_eq_left hΦ]
      have hm := l6a_metricOfFieldC_eq_normMetricC ξ 1
        (⟨fun z => l6a_coupledPhi κ W G Ψ ε z ω', hΦ⟩ : C(Rd d, ℝ))
      simp only [inv_one] at hm
      rw [hm]
      change (DGZ.normMetricC ξ (l6a_coupledPhi κ W G Ψ ε · ω') 1) p = _
      rw [DGZ.normMetricC_apply hΦ]
      simp only [inv_one, one_mul]
    exact propext (by simp only [S, heq, Set.mem_ofPred_eq])
  rw [hleft, hlaw ε hε ξ 1 S hS, hright]

end HigherDimLQGMetric
