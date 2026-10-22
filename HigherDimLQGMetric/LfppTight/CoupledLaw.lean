import HigherDimLQGMetric.LfppTight.CoupledVec
import HigherDimLQGMetric.LfppTight.LawTransfer

/-! The L1e law on the same white-noise space as the DGZ real-cutoff field. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN bandVecM)

def l6a_coupledPhi {d : ℕ} (κ : Rd d → ℝ)
    {Ω : Type*} (W : WN d → Ω → ℝ)
    (G : ℝ → Rd d → Ω → ℝ) (Ψ : Rd d → Ω → ℝ)
    (ε : ℝ) (x : Rd d) (ω : Ω) : ℝ :=
  G ε x ω - W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ x ω

/-- The centered convolution metric has the law of the explicitly coupled
finite-band plus fixed high-band field. -/
theorem l6a_coupled_metric_law (hL1e : L1e_law)
    {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (W : WN d → Ω' → ℝ) (hW : HigherDimLFPP.IsWhiteNoise P' W)
    (G : ℝ → Rd d → Ω' → ℝ)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1, HigherDimLFPP.IsBandVersion P' W κ ε 1 (G ε)) :
    ∃ Ψ : Rd d → Ω' → ℝ,
      (∀ ω', Continuous fun x => Ψ x ω') ∧
      (∀ x, Measurable (Ψ x)) ∧
      ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ (ξ a : ℝ) (S : Set C(Rd d × Rd d, ℝ)),
        MeasurableSet S →
        P {ω | l6a_metricOfFieldC ξ a
          (l6a_toFieldCMap (convMollifyNorm κ ε (h ω))) ∈ S} =
        P' {ω' | l6a_metricOfFieldC ξ a
          (l6a_toFieldCMap (fun x => l6a_coupledPhi κ W G Ψ ε x ω')) ∈ S} := by
  obtain ⟨Ψ, hΨc, hΨm, hΨhigh, hΨsplit⟩ :=
    l6a_exists_coupled_centered_version hd hκ hW G hG
  refine ⟨Ψ, hΨc, hΨm, ?_⟩
  intro ε hε ξ a S hS
  have hΦc (ω' : Ω') :
      Continuous fun x => l6a_coupledPhi κ W G Ψ ε x ω' := by
    exact ((hG ε hε).continuous ω').sub continuous_const |>.add (hΨc ω')
  have hΦeq (x : Rd d) :
      (fun ω' => l6a_coupledPhi κ W G Ψ ε x ω') =ᵐ[P']
        W (bandVecM κ (Ioi ε) (Measure.dirac x) (unitSphereProb d)) :=
    hΨsplit ε hε x
  obtain ⟨hCc, hlaw⟩ := hL1e d hd κ hκ ε hε.1 P h hh P' W
    (l6a_coupledPhi κ W G Ψ ε) hW hΦc hΦeq
  have h := l6a_aeContinuousFunctional_law P P'
    (fun x ω => convMollifyNorm κ ε (h ω) x)
    (l6a_coupledPhi κ W G Ψ ε) hCc hΦc hlaw
    (l6a_metricOfFieldC ξ a) (l6a_measurable_metricOfFieldC ξ a) hS
  simpa only [l6a_toFieldCMap, dite_eq_left (hΦc _)] using h

end HigherDimLQGMetric
