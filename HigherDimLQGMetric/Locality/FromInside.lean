import HigherDimLQGMetric.Locality.NormalizeCI

/-! Reduction of ξ-additive locality to a normalization sphere inside each test domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_additive_of_inside_locality {d : ℕ} (hd : 2 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (D : Ω → ContMetric d)
    (hh : IsNormalizedLGF h P) (hD : Measurable D)
    (hlen : ∀ᵐ ω ∂P, (D ω).IsLength) (ξ : ℝ)
    (hinside : ∀ (V : TopologicalSpace.Opens (Rd d)), IsNiceOpen V →
      ∀ (z₀ : Rd d) (r₀ : ℝ), 0 < r₀ → sphere z₀ r₀ ⊆ V →
      LQGMetric.CondIndepEv
        (fieldSigmaRd (fun ω => l7b_recenter (h ω) r₀ z₀) V)
        (famSigmaRd (rescFam ξ h D z₀ r₀) V)
        (fullSigmaRd (fun ω => l7b_recenter (h ω) r₀ z₀) ⊔
          famSigmaRd (rescFam ξ h D z₀ r₀) (extOpen V)) P) :
    IsXiAdditiveRd ξ P h D D := by
  refine ⟨hD, hD, ?_, ?_⟩
  · filter_upwards [hlen] with ω hω
    exact ⟨hω, hω⟩
  intro z r hr V hV
  have hlocal : LQGMetric.CondIndepEv
      (fieldSigmaRd (fun ω => l7b_recenter (h ω) r z) V)
      (famSigmaRd (rescFam ξ h D z r) V)
      (fullSigmaRd (fun ω => l7b_recenter (h ω) r z) ⊔
        famSigmaRd (rescFam ξ h D z r) (extOpen V)) P := by
    rcases (V : Set (Rd d)).eq_empty_or_nonempty with hempty | ⟨z₀, hz₀⟩
    · exact l7a_condIndep_empty hh.1 D hD hlen ξ V hempty r z
    obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.1 V.isOpen z₀ hz₀
    let r₀ : ℝ := R / 2
    have hr₀ : 0 < r₀ := by dsimp [r₀]; positivity
    have hsph : sphere z₀ r₀ ⊆ V :=
      (sphere_subset_ball (show r₀ < R by dsimp [r₀]; linarith)).trans hball
    exact l7a_condIndep_recenter_transfer hd hh.1 D hD hlen ξ V hr₀ z₀ hsph
      hr z (hinside V hV z₀ r₀ hr₀ hsph)
  change LQGMetric.CondIndepEv
    (fieldSigmaRd (fun ω => l7b_recenter (h ω) r z) V)
    (famSigmaRd (rescFam ξ h D z r) V ⊔ famSigmaRd (rescFam ξ h D z r) V)
    (fullSigmaRd (fun ω => l7b_recenter (h ω) r z) ⊔
      famSigmaRd (rescFam ξ h D z r) (extOpen V) ⊔
      famSigmaRd (rescFam ξ h D z r) (extOpen V)) P
  simpa only [sup_idem, sup_assoc] using hlocal

end HigherDimLQGMetric
