import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.WeylMonotone
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.GapChecks.Gapc2




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer
open LQGMetric (DistC IsGFFPlusCont)

 

theorem ebl_of_weyl_monotonicity
    (hW : ∀ (ξ : ℝ) (f : C(ℂ, ℝ)) (d e : LSCMetric)
      (C : ℝ), 0 < C →
      (∀ p : ℂ × ℂ, e p ≤ ENNReal.ofReal C * d p) →
      ∀ p : ℂ × ℂ,
        weylScale ξ f e p ≤ ENNReal.ofReal C * weylScale ξ f d p)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D') :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsGFFPlusCont h P →
        ∀ᵐ ω ∂P, ∀ z w : ℂ,
          (D' (h ω)) (z,w) ≤ ENNReal.ofReal C * (D (h ω)) (z,w) ∧
          (D (h ω)) (z,w) ≤ ENNReal.ofReal C * (D' (h ω)) (z,w) := by
  obtain ⟨C, hC, hnorm⟩ := normalized_ebl ξ Q D D' hD hD'
  refine ⟨C, hC, ?_⟩
  intro Ω _ P _ h hh
  obtain ⟨k, F, hk, hkplus, -, hrep⟩ := TwoScale.GapChecks.exists_normalized_decomposition hh
  have hN := hnorm P k hk
  have hWeyl := hD.2.2.2.1 P k hkplus
  have hWeyl' := hD'.2.2.2.1 P k hkplus
  filter_upwards [hN, hWeyl, hWeyl'] with ω hcmp hw hw'
  intro z w
  rw [hrep ω, ← hw (F ω), ← hw' (F ω)]
  constructor
  · exact hW (ξ : ℝ) (F ω) (D (k ω)) (D' (k ω)) C (lt_of_lt_of_le zero_lt_one hC)
      (fun p => (hcmp p.1 p.2).1) (z,w)
  · exact hW (ξ : ℝ) (F ω) (D' (k ω)) (D (k ω)) C (lt_of_lt_of_le zero_lt_one hC)
      (fun p => (hcmp p.1 p.2).2) (z,w)

end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer
