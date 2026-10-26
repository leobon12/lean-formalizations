import SupercriticalConformalCovariance.Transport.LawTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory TopologicalSpace Set
open scoped ENNReal
open LQGMetric (DistC DistOn addFun)
open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric LSCFun)
open SupercriticalConformalCovariance (IsDomainRealization)
namespace SupercriticalConformalCovariance.Transport

/-- A fixed cutoff representation of the confined metric, as a pointwise equality of LSC
functions on one almost-sure event. -/
theorem ae_closedDiskFun_eq_confined {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D)
    (V : Opens ℂ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {h : Ω → DistOn V}
    {h₀ : Ω → DistC} {f : Ω → C(V, ℝ)}
    (hR : IsDomainRealization V P h h₀ f)
    (c : ℂ) (R : ℝ) (hKV : Metric.closedBall c R ⊆ V)
    (n : ℕ) (hn : Metric.closedBall c R ⊆ SupercriticalConformalCovariance.Domain.exW V n) :
    ∀ᵐ ω ∂P, ∀ q : ℂ × ℂ,
      (closedDiskFun c R (D (addFun (h₀ ω) (SupercriticalConformalCovariance.Domain.cutF V n (f ω))))).1 q =
        ((SupercriticalConformalCovariance.Domain.confined (ξ : ℝ) (D (h₀ ω)) hKV (f ω) q : ℝ≥0∞) : EReal) := by
  filter_upwards [SupercriticalConformalCovariance.Domain.ae_weylScaleOn_eq_internal hD P hR.2.1] with ω hω q
  have heq : SupercriticalConformalCovariance.Domain.confined (ξ : ℝ) (D (h₀ ω)) hKV (f ω) q =
      SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.closedBallPathInf
        (D (addFun (h₀ ω) (SupercriticalConformalCovariance.Domain.cutF V n (f ω)))) c R q.1 q.2 := by
    unfold SupercriticalConformalCovariance.Domain.confined
    split_ifs with hq
    · rw [hω _ (SupercriticalConformalCovariance.Domain.resC hKV (f ω))
        (SupercriticalConformalCovariance.Domain.cutF V n (f ω))
        (fun z hz => SupercriticalConformalCovariance.Domain.cutF_eq V n (f ω) z (hn hz))]
      rfl
    · symm
      refine eq_top_iff.2 (le_iInf fun P => le_iInf fun a => le_iInf fun b =>
        le_iInf fun hP => le_iInf fun hK => le_iInf fun ha => le_iInf fun hb => ?_)
      exfalso
      refine hq ⟨?_, ?_⟩
      · rw [← ha]; exact hK a (left_mem_Icc.2 hP.1)
      · rw [← hb]; exact hK b (right_mem_Icc.2 hP.1)
  exact congrArg (fun x : ℝ≥0∞ => (x : EReal)) heq.symm

end SupercriticalConformalCovariance.Transport
