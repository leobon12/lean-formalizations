import HigherDimLQGMetric.Locality.MarkovSigma

/-! The open-set Markov theorem with the full-field reconstruction expressed
as an inclusion of sigma algebras. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open LQGMetric.GM.Bilip

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_markov_ready {d : ℕ} (hd : 2 ≤ d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    (hDM : DMarkovRd) (V : TopologicalSpace.Opens (Rd d))
    (hV : IsNiceOpen V) (z₀ : Rd d) {ρ : ℝ} (hρ : 0 < ρ)
    (hsph : Metric.sphere z₀ ρ ⊆ V) :
    let g : Ω → DistRd d := fun ω => addConst (h ω) (-sphereAvg (h ω) ρ z₀)
    ∃ H : Ω → Rd d → ℝ,
      (∀ ω, ContinuousOn (H ω) (extOpen V)) ∧
      (∃ G : Ω → Rd d → ℝ, Measurable[fieldSigmaRd g V] G ∧ H =ᵐ[P] G) ∧
      let R : Ω → DistOn (extOpen V) := fun ω =>
        restrictTo (extOpen V) (g ω) - ofFunOn (extOpen V) (H ω)
      Indep (MeasurableSpace.comap R inferInstance) (fieldSigmaRd g V) P ∧
      fullSigmaRd g ≤ aeClosure P
        (fieldSigmaRd g V ⊔ MeasurableSpace.comap R inferInstance) := by
  dsimp only
  obtain ⟨H, hHcont, hHmeas, hind, hdet⟩ :=
    hDM d hd P h hh V z₀ ρ hV.1 hρ hsph
  refine ⟨H, hHcont, hHmeas, ?_⟩
  refine ⟨hind, ?_⟩
  exact l7a_fullSigma_le_markovSigma _ V _ (hdet hV.2) _ (le_refl _)

end HigherDimLQGMetric
