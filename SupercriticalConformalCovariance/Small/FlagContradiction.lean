import SupercriticalConformalCovariance.Small.PathwiseContradiction
import SupercriticalConformalCovariance.Small.ConfinedLawGeometry

set_option autoImplicit false
noncomputable section
open Filter Topology Set
open scoped ENNReal
namespace SupercriticalConformalCovariance.Small
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.B2.PfeAxioms

/-- The pathwise contradiction after the Skorokhod marks have converged.
Only metric-valued ambient samples are lifted; the off-locus branch of the
total Borel lift is never used. -/
theorem no_eventual_ambient_failure
    (F G : ℕ → LSCFun) (d : LSCMetric)
    (hF : Tendsto F atTop (𝓝 d.toLSCFun))
    (hG : Tendsto G atTop (𝓝 d.toLSCFun))
    (c : NNReal) (hc : 0 < c)
    (hFm : ∀ n, IsMetricLSCFun (F n))
    (hGm : ∀ n, IsMetricLSCFun (G n))
    (hFlen : ∀ n, (ambientMetricLift (F n)).IsLengthSpace)
    (hGlen : ∀ n, (ambientMetricLift (G n)).IsLengthSpace)
    (hFreg : ∀ n (P : ℝ → ℂ) (a b : ℝ),
      (ambientMetricLift (F n)).IsCurve P a b →
      (ambientMetricLift (F n)).len P a b < ⊤ →
      ContinuousOn P (Icc a b))
    (hGreg : ∀ n (P : ℝ → ℂ) (a b : ℝ),
      (ambientMetricLift (G n)).IsCurve P a b →
      (ambientMetricLift (G n)).len P a b < ⊤ →
      ContinuousOn P (Icc a b))
    (hcomp : ∀ n : ℕ, ∀ x y : ℂ,
      ambientMetricLift (F n) (x,y) ≤
          (c : ℝ≥0∞) * ambientMetricLift (G n) (x,y) ∧
      ambientMetricLift (G n) (x,y) ≤
          (c : ℝ≥0∞) * ambientMetricLift (F n) (x,y))
    (u v : ℕ → ℂ) (K : Set ℂ) (hK : IsCompact K)
    (hKend : ∀ n, u n ∈ K ∧ v n ∈ K)
    (α θ m : ℝ) (hα : α < 1) (hθ : 0 < θ)
    (M : NNReal) (η : ℝ) (hη : 0 < η)
    (hbad : ∀ᶠ n in atTop,
      SupercriticalConformalCovariance.Regular.SourceFailure
        (ambientMetricLift (F n)) (ambientMetricLift (G n))
        0 (u n) (v n) 1 α θ m (M : ℝ) (1 - α) η) : False := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hbad
  let t : ℕ → ℕ := fun n => n + N
  have ht : Tendsto t atTop atTop := tendsto_add_atTop_nat N
  have hFt : Tendsto (fun n => ambientMetricLift (F (t n)))
      atTop (𝓝 d) := by
    rw [LSCMetric.isInducing_toLSCFun.tendsto_nhds_iff]
    have heq : (fun n => (ambientMetricLift (F (t n))).toLSCFun) = F ∘ t := by
      funext n
      exact ambientMetricLift_toLSCFun _ (hFm _)
    change Tendsto (fun n => (ambientMetricLift (F (t n))).toLSCFun)
      atTop (𝓝 d.toLSCFun)
    rw [heq]
    exact hF.comp ht
  have hGt : Tendsto (fun n => ambientMetricLift (G (t n)))
      atTop (𝓝 d) := by
    rw [LSCMetric.isInducing_toLSCFun.tendsto_nhds_iff]
    have heq : (fun n => (ambientMetricLift (G (t n))).toLSCFun) = G ∘ t := by
      funext n
      exact ambientMetricLift_toLSCFun _ (hGm _)
    change Tendsto (fun n => (ambientMetricLift (G (t n))).toLSCFun)
      atTop (𝓝 d.toLSCFun)
    rw [heq]
    exact hG.comp ht
  exact no_persistent_source_failure
    (fun n => ambientMetricLift (F (t n)))
    (fun n => ambientMetricLift (G (t n))) d hFt hGt c hc
    (fun n => hFlen (t n)) (fun n => hGlen (t n))
    (fun n => hFreg (t n)) (fun n => hGreg (t n))
    (fun n => hcomp (t n))
    (u ∘ t) (v ∘ t) K hK (fun n => hKend (t n))
    α θ m hα hθ M η hη (fun n => hN (t n) (by simp only [t]; omega))

end SupercriticalConformalCovariance.Small
