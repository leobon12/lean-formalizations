import SupercriticalLQGUniqueness.Uniqueness.Objects.ClauseMeasurability.CostMeas
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Barrier




 


set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3

theorem acr_le_internal (D : LSCMetric) (w : ℂ) (a b : ℝ)
    (p : Objects.CorrectedEvent.cann w a b × Objects.CorrectedEvent.cann w a b)
    (hp : (p.1 : ℂ) ∈ sphere w a) (hq : (p.2 : ℂ) ∈ sphere w b) :
    Objects.CorrectedEvent.acr D w a b ≤ D.internal (Objects.CorrectedEvent.cann w a b) p := by
  unfold LSCMetric.internal
  refine le_iInf fun P => le_iInf fun t => le_iInf fun u =>
    le_iInf fun hcurve => le_iInf fun htrace => le_iInf fun hstart =>
      le_iInf fun hend => ?_
  unfold Objects.CorrectedEvent.acr
  apply iInf_le_of_le P
  apply iInf_le_of_le t
  apply iInf_le_of_le u
  apply iInf_le_of_le hcurve
  have htrace' : P '' Icc t u ⊆ Objects.CorrectedEvent.cann w a b := by
    rintro x ⟨v, hv, rfl⟩
    exact htrace v hv
  apply iInf_le_of_le htrace'
  exact iInf_le_of_le (hstart.symm ▸ hp) (iInf_le_of_le (hend.symm ▸ hq) le_rfl)

theorem acr_eq_ambientAcross_of_barrier (D : LSCMetric)
    (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    (w : ℂ) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Objects.CorrectedEvent.acr D w a b = Objects.CorrectedEvent.ambientAcross D w a b := by
  let A : EuclideanAnnulus := ⟨(w, a, b), ha, hab⟩
  have hY : BiLipschitz.Barrier.closedAnn A.center A.innerRadius A.outerRadius ⊆
      Objects.CorrectedEvent.cann w a b := by
    intro x hx
    simpa only [A, EuclideanAnnulus.center, EuclideanAnnulus.innerRadius,
      EuclideanAnnulus.outerRadius, BiLipschitz.Barrier.closedAnn, Objects.CorrectedEvent.cann,
      mem_ofPred_eq, dist_eq_norm] using hx
  have hshape : acrossDist D A = Objects.CorrectedEvent.ambientAcross D w a b := by
    rfl
  have heq := BiLipschitz.Barrier.acrossDist_eq_iInf_internal D hB hL A hY
  have hle : Objects.CorrectedEvent.acr D w a b ≤ acrossDist D A := by
    rw [heq]
    refine le_iInf fun p => le_iInf fun hp => le_iInf fun hq => ?_
    exact acr_le_internal D w a b p (by simpa only [A, EuclideanAnnulus.center,
      EuclideanAnnulus.innerRadius, mem_sphere_iff_norm] using hp)
      (by simpa only [A, EuclideanAnnulus.center,
        EuclideanAnnulus.outerRadius, mem_sphere_iff_norm] using hq)
  rw [hshape] at hle
  exact le_antisymm hle (Objects.ProbabilityS1S2.ambientAcross_le_acr D w a b)

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3
