import SupercriticalConformalCovariance.Transport.ConfinedMeasurable
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.InternalOfInternal

/-! Realization independence of the closed-disk confined domain metric. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
open LQGMetric (DistC DistOn addFun)
open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric)
open SupercriticalConformalCovariance (IsDomainRealization domainMetric weylScaleOn)

namespace SupercriticalConformalCovariance.Transport

/-- Two realizations of one domain field give the same closed-disk confined metric almost surely.
This equality includes infinity outside the disk and is uniform in the endpoints. -/
theorem ae_confined_eq_of_realisations {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D)
    (V : Opens ℂ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    {h : Ω → DistOn V} {h₀ h₀' : Ω → DistC}
    {f f' : Ω → C(V, ℝ)}
    (hR : IsDomainRealization V P h h₀ f)
    (hR' : IsDomainRealization V P h h₀' f')
    (c : ℂ) (R : ℝ) (hKV : Metric.closedBall c R ⊆ V) :
    ∀ᵐ ω ∂P,
      SupercriticalConformalCovariance.Domain.confined (ξ : ℝ) (D (h₀ ω)) hKV (f ω) =
        SupercriticalConformalCovariance.Domain.confined (ξ : ℝ) (D (h₀' ω)) hKV (f' ω) := by
  obtain ⟨n, hn⟩ := SupercriticalConformalCovariance.Domain.exists_subset_exW V.isOpen (isCompact_closedBall c R) hKV
  let W := SupercriticalConformalCovariance.Domain.exWO V n
  have hWV : W ≤ V := SupercriticalConformalCovariance.Domain.exWO_le V n
  have hKW : Metric.closedBall c R ⊆ W := hn
  have hR1 := SupercriticalConformalCovariance.Domain.isDomainRealization_restrictOn hWV hR
  have hR2 := SupercriticalConformalCovariance.Domain.isDomainRealization_restrictOn hWV hR'
  have hEqW := SupercriticalConformalCovariance.Domain.ae_domainMetric_eq_of_isDomainRealization hD W hR1 hR2
  have hI1 := SupercriticalConformalCovariance.Domain.ae_domainMetric_eq_internal hD W P hR.2.1
  have hI2 := SupercriticalConformalCovariance.Domain.ae_domainMetric_eq_internal hD W P hR'.2.1
  have hK1 := SupercriticalConformalCovariance.Domain.ae_weylScaleOn_eq_internal hD P hR.2.1
  have hK2 := SupercriticalConformalCovariance.Domain.ae_weylScaleOn_eq_internal hD P hR'.2.1
  filter_upwards [hEqW, hI1, hI2, hK1, hK2] with ω eW eI1 eI2 eK1 eK2
  have hIntW : (D (addFun (h₀ ω) (SupercriticalConformalCovariance.Domain.cutF V n (f ω)))).internal W =
      (D (addFun (h₀' ω) (SupercriticalConformalCovariance.Domain.cutF V n (f' ω)))).internal W := by
    funext p
    calc
      (D (addFun (h₀ ω) (SupercriticalConformalCovariance.Domain.cutF V n (f ω)))).internal W p
          = domainMetric (ξ : ℝ) D W (h₀ ω)
              (SupercriticalConformalCovariance.Domain.resC (SetLike.coe_subset_coe.2 hWV) (f ω)) p :=
            (eI1 _ _ (fun z hz => SupercriticalConformalCovariance.Domain.cutF_eq V n (f ω) z hz) p).symm
      _ = domainMetric (ξ : ℝ) D W (h₀' ω)
            (SupercriticalConformalCovariance.Domain.resC (SetLike.coe_subset_coe.2 hWV) (f' ω)) p := congrFun eW p
      _ = (D (addFun (h₀' ω) (SupercriticalConformalCovariance.Domain.cutF V n (f' ω)))).internal W p :=
            eI2 _ _ (fun z hz => SupercriticalConformalCovariance.Domain.cutF_eq V n (f' ω) z hz) p
  have hIntK := SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.internal_eq_of_internal_eq
    (D (addFun (h₀ ω) (SupercriticalConformalCovariance.Domain.cutF V n (f ω))))
    (D (addFun (h₀' ω) (SupercriticalConformalCovariance.Domain.cutF V n (f' ω)))) hKW hIntW
  funext q
  unfold SupercriticalConformalCovariance.Domain.confined
  split_ifs with hq
  · rw [eK1 _ _ _ (fun z hz => SupercriticalConformalCovariance.Domain.cutF_eq V n (f ω) z (hn hz)) _,
      eK2 _ _ _ (fun z hz => SupercriticalConformalCovariance.Domain.cutF_eq V n (f' ω) z (hn hz)) _]
    exact congrFun hIntK _
  · rfl

end SupercriticalConformalCovariance.Transport
