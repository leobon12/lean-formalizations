import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.LocalDet
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.LocalEvents.LocalEventToolkit




 






set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open LQGMetric.Blueprint
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3

def regWindow (w : ℂ) (s : ℝ) : TopologicalSpace.Opens ℂ :=
  annulus w ((7/8)*s) ((17/8)*s)

theorem closedAnn_subset_regWindow (w : ℂ) (s : ℝ) (hs : 0 < s) :
    BiLipschitz.Barrier.closedAnn w s (2*s) ⊆ (regWindow w s : Set ℂ) := by
  intro x hx
  change s ≤ ‖x-w‖ ∧ ‖x-w‖ ≤ 2*s at hx
  change (7/8)*s < ‖x-w‖ ∧ ‖x-w‖ < (17/8)*s
  constructor <;> nlinarith only [hs, hx.1, hx.2]

theorem annulus_subset_regWindow (w : ℂ) (s : ℝ) (hs : 0 < s) :
    EuclideanAnnulus.toSet
      (⟨(w, s, 2*s), hs, by linarith⟩ : EuclideanAnnulus) ⊆
        (regWindow w s : Set ℂ) := by
  intro x hx
  change x ∈ ball w (2*s) \ closure (ball w s) at hx
  rw [closure_ball w hs.ne'] at hx
  simp only [mem_sdiff, mem_ball, mem_closedBall, not_le, dist_eq_norm] at hx
  exact closedAnn_subset_regWindow w s hs ⟨hx.2.le, hx.1.le⟩

private def regRelation (C : Objects.CorrectedEvent.Constants) (w : ℂ) (s : ℝ)
    (U : TopologicalSpace.Opens ℂ)
    (J : ↥(U : Set ℂ) × ↥(U : Set ℂ) → ℝ≥0∞)
    (_ : LQGMetric.DistOn U) : Prop :=
  ∃ E : LSCMetric, BiLipschitz.Barrier.Barrier E ∧ E.IsLengthSpace ∧
    E.internal (U : Set ℂ) = J ∧ Objects.CorrectedEvent.regGood C E s w

theorem aeEventIn_regGood_open
    (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (C : Objects.CorrectedEvent.Constants)
    (w : ℂ) (s : ℝ) (hs : 0 < s) :
    AEEventIn μ (fieldSigma id (regWindow w s))
      {g | Objects.CorrectedEvent.regGood C (D g) s w} := by
  let U := regWindow w s
  let F : Fin 1 → LQGMetric.DistC → LSCMetric := fun _ => D
  let Φ : (Fin 1 → ↥(U : Set ℂ) × ↥(U : Set ℂ) → ℝ≥0∞) →
      LQGMetric.DistOn U → Prop := fun J R => regRelation C w s U (J 0) R
  let B : Set LQGMetric.DistC :=
    {g | Φ (fun i => (F i g).internal (U : Set ℂ)) (LQGMetric.restrictTo U g)}
  let E : Set LQGMetric.DistC := {g | Objects.CorrectedEvent.regGood C (D g) s w}
  have hQ : 0 < Q := Positivity.FromAxioms.axpos ξ Q D hD
  have hB := BiLipschitz.Barrier.ae_barrier hD hQ μ id hμ
  have hwhole : LQGMetric.IsGFFPlusCont
      (id : LQGMetric.DistC → LQGMetric.DistC) μ :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hμ.1
  have hL := hD.length μ id hwhole
  have hEq : B =ᵐ[μ] E := by
    filter_upwards [hB, hL] with g hgB hgL
    change (∃ X : LSCMetric, BiLipschitz.Barrier.Barrier X ∧ X.IsLengthSpace ∧
      X.internal (U : Set ℂ) = (D g).internal (U : Set ℂ) ∧
      Objects.CorrectedEvent.regGood C X s w) = Objects.CorrectedEvent.regGood C (D g) s w
    apply propext
    constructor
    · rintro ⟨X, hXB, hXL, hXint, hXgood⟩
      exact (regGood_iff_of_internal_eq C (D g) X hgB hXB hgL hXL w s hs U
        (closedAnn_subset_regWindow w s hs)
        (annulus_subset_regWindow w s hs) hXint.symm).mpr hXgood
    · intro hgood
      exact ⟨D g, hgB, hgL, rfl, hgood⟩
  have hBm : NullMeasurableSet B μ :=
    (Objects.ClauseMeasurability.measurableSet_regGood C D hD.measurable s hs w).nullMeasurableSet.congr
      hEq.symm
  have hlocal : AEEventIn μ (fieldSigma id U) B :=
    Toolkit.LocalEvents.aeEventIn_internal_family μ hwhole ξ Q F (fun _ => hD)
      U Φ hBm
  obtain ⟨R, hRm, hBR⟩ := hlocal
  exact ⟨R, hRm, hEq.symm.trans hBR⟩

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3
