import SupercriticalConformalCovariance.Domain.Axioms

/-! A common locality functional for countably many domain-field laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
open LQGMetric (DistC DistOn IsGFFPlusCont addFun restrictTo)
open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric)
open SupercriticalConformalCovariance (IsDomainRealization domainMetric)

namespace SupercriticalConformalCovariance.Transport

/-- One measurable functional on the domain field for every law in a countable family. -/
theorem universal_domain_locality {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D) (V : Opens ℂ)
    (ι : Type) [Countable ι] (Ω : ι → Type) [∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)]
    (h : ∀ i, Ω i → DistOn V) (h₀ : ∀ i, Ω i → DistC)
    (f : ∀ i, Ω i → C(V, ℝ))
    (hR : ∀ i, IsDomainRealization V (P i) (h i) (h₀ i) (f i)) :
    ∃ G : DistOn V → (V × V → ℝ≥0∞), Measurable G ∧
      ∀ i, ∀ᵐ ω ∂(P i), domainMetric (ξ : ℝ) D V (h₀ i ω) (f i ω) = G (h i ω) := by
  have hloc := fun n : ℕ => SupercriticalConformalCovariance.Domain.universalLocality_lsc hD (SupercriticalConformalCovariance.Domain.exWO V n)
    ι Ω P (fun i ω => addFun (h₀ i ω) (SupercriticalConformalCovariance.Domain.cutF V n (f i ω)))
    (fun i => SupercriticalConformalCovariance.Domain.isGFFPlusCont_addFun_of_measurable (hR i).2.1
      (SupercriticalConformalCovariance.Domain.measurable_cutExt V.isOpen _ (hR i).2.2.1))
  choose F hFm hFae using hloc
  refine ⟨fun k p => ⨅ (n : ℕ) (hx : (p.1 : ℂ) ∈ SupercriticalConformalCovariance.Domain.exW V n)
    (hy : (p.2 : ℂ) ∈ SupercriticalConformalCovariance.Domain.exW V n),
    F n (SupercriticalConformalCovariance.Domain.restrictOn (SupercriticalConformalCovariance.Domain.exWO_le V n) k)
      (⟨p.1, hx⟩, ⟨p.2, hy⟩), ?_, ?_⟩
  · refine Measurable.of_eval fun p => ?_
    refine Measurable.iInf fun n => SupercriticalConformalCovariance.Domain.measurable_iInf_dprop fun hx =>
      SupercriticalConformalCovariance.Domain.measurable_iInf_dprop fun hy => ?_
    exact (measurable_pi_apply _).comp ((hFm n).comp
      (SupercriticalConformalCovariance.Domain.measurable_restrictOn _))
  · intro i
    have hres : ∀ n, ∀ᵐ ω ∂(P i),
        restrictTo (SupercriticalConformalCovariance.Domain.exWO V n)
          (addFun (h₀ i ω) (SupercriticalConformalCovariance.Domain.cutF V n (f i ω))) =
        SupercriticalConformalCovariance.Domain.restrictOn (SupercriticalConformalCovariance.Domain.exWO_le V n) (h i ω) := by
      intro n
      filter_upwards [SupercriticalConformalCovariance.Domain.ae_restrictTo_cutF (hR i) n] with ω hω
      ext φ
      exact hω φ
    filter_upwards [SupercriticalConformalCovariance.Domain.ae_domainMetric_eq_iInf_internal hD V (P i)
      (h i) (h₀ i) (f i) (hR i), ae_all_iff.2 (fun n => hFae n i), ae_all_iff.2 hres]
      with ω e1 e2 e3
    funext p
    rw [e1 p]
    refine iInf_congr fun n => iInf_congr fun hx => iInf_congr fun hy => ?_
    change (D (addFun (h₀ i ω) (SupercriticalConformalCovariance.Domain.cutF V n (f i ω)))).internal
      ((SupercriticalConformalCovariance.Domain.exWO V n : Opens ℂ) : Set ℂ) _ = _
    rw [e2 n, e3 n]
    rfl

end SupercriticalConformalCovariance.Transport
