import SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent.EventPredicate
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation.PathHit




 





set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS1S2

 
theorem ambientAcross_le_acr (D : LSCMetric) (w : ℂ) (a b : ℝ) :
    Objects.CorrectedEvent.ambientAcross D w a b ≤ Objects.CorrectedEvent.acr D w a b := by
  unfold Objects.CorrectedEvent.acr
  refine le_iInf fun P => le_iInf fun t => le_iInf fun u =>
    le_iInf fun hcurve => le_iInf fun _ => le_iInf fun ht => le_iInf fun hu => ?_
  have hdist : D (P t, P u) ≤ D.len P t u := apply_le_len D P hcurve.1
  exact (iInf₂_le_of_le (P t) ht (iInf₂_le (P u) hu)).trans hdist

 
theorem around_le_aroundDist (D : LSCMetric) (w : ℂ) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) :
    Objects.CorrectedEvent.around D w a b ≤
      aroundDist D ⟨(w, a, b), ha, hab⟩ := by
  let A : EuclideanAnnulus := ⟨(w, a, b), ha, hab⟩
  change Objects.CorrectedEvent.around D w a b ≤ aroundDist D A
  unfold aroundDist
  refine le_iInf fun P => le_iInf fun t => le_iInf fun u =>
    le_iInf fun hcurve => le_iInf fun htrace => le_iInf fun hsep => ?_
  have htrace' : P '' Icc t u ⊆ Objects.CorrectedEvent.ann w a b := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := hx
    have hmem := htrace v hv
    change P v ∈ ball w b \ closure (ball w a) at hmem
    change P v ∈ Objects.CorrectedEvent.ann w a b
    rw [closure_ball _ ha.ne'] at hmem
    simpa only [Objects.CorrectedEvent.ann, mem_sdiff, mem_ball, mem_closedBall,
      mem_ofPred_eq, not_le, and_comm] using hmem
  have hsep' : LQGMetric.Disconnects (P '' Icc t u) (sphere w a) (sphere w b) := by
    change Disconnects (P '' Icc t u) (sphere w a) (sphere w b) at hsep
    exact Toolkit.PlanarSeparation.candidate_disconnects_implies_path_hit hsep
  exact iInf_le_of_le P (iInf_le_of_le t (iInf_le_of_le u
    (iInf_le_of_le hcurve (iInf_le_of_le htrace'
      (iInf_le_of_le hsep' le_rfl)))))

 
def crossingShape (a b : ℝ) (ha : 0 < a) (hab : a < b) : EuclideanAnnulus :=
  ⟨(0, a, b), ha, hab⟩

theorem acrossDist_shape_eq (D : LSCMetric) (a b r : ℝ)
    (ha : 0 < a) (hab : a < b) (hr : 0 < r) :
    acrossDist D ((crossingShape a b ha hab).dilate r hr) =
      Objects.CorrectedEvent.ambientAcross D 0 (a*r) (b*r) := by
  unfold acrossDist Objects.CorrectedEvent.ambientAcross
  simp only [crossingShape, EuclideanAnnulus.dilate,
    EuclideanAnnulus.innerBoundary, EuclideanAnnulus.outerBoundary,
    EuclideanAnnulus.center, EuclideanAnnulus.innerRadius,
    EuclideanAnnulus.outerRadius, smul_zero]
  rw [mul_comm r a, mul_comm r b]

theorem aroundDist_shape_ge (D : LSCMetric) (a b r : ℝ)
    (ha : 0 < a) (hab : a < b) (hr : 0 < r) :
    Objects.CorrectedEvent.around D 0 (a*r) (b*r) ≤
      aroundDist D ((crossingShape a b ha hab).dilate r hr) := by
  have har : 0 < a*r := mul_pos ha hr
  have hbr : a*r < b*r := mul_lt_mul_of_pos_right hab hr
  have hShape : (crossingShape a b ha hab).dilate r hr =
      (⟨(0, a*r, b*r), har, hbr⟩ : EuclideanAnnulus) := by
    apply Subtype.ext
    simp only [crossingShape, EuclideanAnnulus.dilate,
      EuclideanAnnulus.center, EuclideanAnnulus.innerRadius,
      EuclideanAnnulus.outerRadius, smul_zero]
    rw [mul_comm r a, mul_comm r b]
  rw [hShape]
  exact around_le_aroundDist D 0 (a*r) (b*r) har hbr

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS1S2
