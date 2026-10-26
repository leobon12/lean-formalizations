import SupercriticalConformalCovariance.BiLip.Step2Tight
import SupercriticalConformalCovariance.BiLip.Local
import SupercriticalConformalCovariance.BiLip.Lengths

/-!
# Lemma 2.1 (bi-Lipschitz comparison), with no inputs

Paper l. 90–148, under ruling A11 D3 (`C = C(ξ)`, independent of `U` and `φ`): the two open inputs of
`lemma21_of_seq_inputs` / `lemma21_lengths_of_seq_inputs` are discharged by
* `targetTightSeq_proved` (step 2, l. 112–125: Koebe, GM Lemma 2.4 (2.6), affine covariance, Weyl);
* `goodEventsLocal_proved` (step 4, l. 136–138: transported locality of the good events).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology MeasureTheory TopologicalSpace
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip

open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric IsLFPPExponent)
open SupercriticalConformalCovariance (IsConformalBijection domainMetric)
open LQGMetric (DistC)
open HigherDimLQGMetric (curveLengthWith)

/-- **Lemma 2.1** (l. 90–148): there is `C = C(ξ) ≥ 1` such that for every conformal bijection
`φ : U → V` and every instance (`h` a normalized whole-plane GFF, `(g₀, k)` a realization on `V` of the
pulled-back field `h ∘ φ⁻¹ + Q log |(φ⁻¹)′|`), almost surely for all `u, v ∈ U`,
`C⁻¹ D_h(u, v; U) ≤ D_V(φ u, φ v) ≤ C D_h(u, v; U)`. -/
theorem lemma21 (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (U V : Opens ℂ) (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V)
        {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h g₀ : Ω → DistC) (k : Ω → C(V, ℝ)), IsInstance Q U V hφ P h g₀ k →
        ∀ᵐ ω ∂P, ∀ u v : U,
          ENNReal.ofReal C⁻¹ * (D (h ω)).internal U (u, v) ≤
              domainMetric (ξ : ℝ) D V (g₀ ω) (k ω)
                (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) ∧
            domainMetric (ξ : ℝ) D V (g₀ ω) (k ω)
                (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) ≤
              ENNReal.ofReal C * (D (h ω)).internal U (u, v) :=
  lemma21_of_seq_inputs ξ Q hQ D hD (targetTightSeq_proved hQ hD) (goodEventsLocal_proved hD)

/-- **Lemma 2.1 with the length clause** (l. 90–96): the same `C` compares the pointwise metrics and the
lengths of every path in `U`. -/
theorem lemma21_lengths (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (U V : Opens ℂ) (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V)
        {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h g₀ : Ω → DistC) (k : Ω → C(V, ℝ)), IsInstance Q U V hφ P h g₀ k →
        ∀ᵐ ω ∂P,
          (∀ u ∈ (U : Set ℂ), ∀ v ∈ (U : Set ℂ),
            eT (D (g₀ ω)) ξ (k ω) φ u v ≤ ENNReal.ofReal C * pathInf (D (h ω)) U u v ∧
            pathInf (D (h ω)) U u v ≤ ENNReal.ofReal C * eT (D (g₀ ω)) ξ (k ω) φ u v) ∧
          ∀ (γ : ℝ → ℂ) (a b : ℝ), (∀ t ∈ Icc a b, γ t ∈ (U : Set ℂ)) →
            curveLengthWith (eT (D (g₀ ω)) ξ (k ω) φ) γ a b ≤
                ENNReal.ofReal C * curveLengthWith (pathInf (D (h ω)) U) γ a b ∧
              curveLengthWith (pathInf (D (h ω)) U) γ a b ≤
                ENNReal.ofReal C * curveLengthWith (eT (D (g₀ ω)) ξ (k ω) φ) γ a b :=
  lemma21_lengths_of_seq_inputs ξ Q hQ D hD (targetTightSeq_proved hQ hD) (goodEventsLocal_proved hD)


end SupercriticalConformalCovariance.BiLip
