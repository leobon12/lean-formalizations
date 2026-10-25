import SupercriticalLQGUniqueness.Uniqueness.Objects.CentreZero.Shape
import SupercriticalLQGUniqueness.Uniqueness.Objects.T58Assembly.Assembly




 






set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.CentreZero

open SupercriticalLQGUniqueness
open Set Metric
open scoped ENNReal

 

theorem aroundDist_le_around (D : LSCMetric) (hForget : Continuous (BiLipschitz.Barrier.forget D))
    (r s : ℝ) (hr : 0 < r) (hrs : r < s) :
    aroundDist D ⟨((0 : ℂ), (r, s)), hr, hrs⟩ ≤ Objects.CorrectedEvent.around D 0 r s := by
  let A : EuclideanAnnulus := ⟨((0 : ℂ), (r, s)), hr, hrs⟩
  have hA : A.toSet = Objects.CorrectedEvent.ann 0 r s := by
    ext x
    simp only [EuclideanAnnulus.toSet, Objects.CorrectedEvent.ann, A,
      EuclideanAnnulus.center, EuclideanAnnulus.innerRadius, EuclideanAnnulus.outerRadius]
    rw [closure_ball _ hr.ne']
    simp only [mem_sdiff, mem_ball, mem_closedBall, mem_ofPred_eq, not_le]
    exact and_comm
  change aroundDist D A ≤ Objects.CorrectedEvent.around D 0 r s
  unfold Objects.CorrectedEvent.around
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
    le_iInf fun hCurve => le_iInf fun hTrace => le_iInf fun hSep => ?_
  have hCont : ContinuousOn P (Icc a b) := hForget.comp_continuousOn hCurve.2
  have hClosed : IsClosed (P '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hCont).isClosed
  have hSep' : Disconnects (P '' Icc a b) A.innerBoundary A.outerBoundary := by
    apply Objects.T58Assembly.pathHit_imp_disconnects_of_isClosed hClosed
    change LQGMetric.Disconnects (P '' Icc a b) (sphere 0 r) (sphere 0 s)
    exact hSep
  have hTrace' : ∀ t ∈ Icc a b, P t ∈ A.toSet := by
    intro t ht
    rw [hA]
    exact hTrace ⟨t, ht, rfl⟩
  exact iInf_le_of_le P (iInf_le_of_le a (iInf_le_of_le b
    (iInf_le_of_le hCurve (iInf_le_of_le hTrace' (iInf_le_of_le hSep' le_rfl)))))

 

theorem around_bound_of_corrected_event {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {par : EndSaving.Interfaces.Parameters ξ} {r : Set.Ioi (0 : ℝ)}
    {C : Objects.CorrectedEvent.Constants} {T : Objects.CorrectedEvent.TubeData} {hData : Objects.CorrectedEvent.DataMatch C T}
    {F : ℂ → LQGMetric.DistC → Prop}
    {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (hEvent : Objects.CorrectedEvent.correctedEvent C T hData F D D' g)
    (hForget : Continuous (BiLipschitz.Barrier.forget (D g)))
    (hXi : C.ξ = ξ) (hQ : C.Q = Q) (hR : C.r = r)
    (hAround : par.Caround = C.A_around)
    {c : ℝ} (hc : IsCircleAverage g r 0 c) :
    ∃ A : EuclideanAnnulus,
      A.center = 0 ∧ A.innerRadius = 3 * (r : ℝ) ∧
      A.outerRadius = 4 * (r : ℝ) ∧
      aroundDist (D g) A ≤ ENNReal.ofReal par.Caround *
        ENNReal.ofReal ((r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * c)) := by
  have hr : 0 < (r : ℝ) := r.2
  have h3 : 0 < 3 * (r : ℝ) := by positivity
  have h34 : 3 * (r : ℝ) < 4 * (r : ℝ) := by linarith
  let A : EuclideanAnnulus := ⟨((0 : ℂ), (3 * (r : ℝ), 4 * (r : ℝ))), h3, h34⟩
  have hAvg := Objects.Producer.circleAvg_eq_of_isCircleAverage hc
  have hN : Objects.CorrectedEvent.normalizer C g C.r 0 =
      ENNReal.ofReal ((r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * c)) := by
    simp only [Objects.CorrectedEvent.normalizer, hXi, hQ, hR, hAvg]
  have hS2 := Objects.CorrectedEvent.event_around hEvent
  rw [hN, ← hAround, hR] at hS2
  refine ⟨A, rfl, rfl, rfl, ?_⟩
  exact (aroundDist_le_around (D g) hForget _ _ h3 h34).trans hS2

end SupercriticalLQGUniqueness.Uniqueness.Objects.CentreZero
