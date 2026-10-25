import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.LiteralAcross
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Prob
import SupercriticalLQGUniqueness.Uniqueness.Positivity.FromAxioms.AXPOSComplete




 


set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3

theorem ae_acr_eq_ambientAcross
    (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D)
    (w : ℂ) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∀ᵐ g ∂μ, Objects.CorrectedEvent.acr (D g) w a b = Objects.CorrectedEvent.ambientAcross (D g) w a b := by
  have hQ : 0 < Q := Positivity.FromAxioms.axpos ξ Q D hD
  have hB := BiLipschitz.Barrier.ae_barrier hD hQ μ id hμ
  have hwhole : LQGMetric.IsGFFPlusCont (id : LQGMetric.DistC → LQGMetric.DistC) μ :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hμ.1
  have hL := hD.length μ id hwhole
  filter_upwards [hB, hL] with g hgB hgL
  exact acr_eq_ambientAcross_of_barrier (D g) hgB hgL w a b ha hab

 

theorem ae_regGood_iff_standard_costs
    (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (C : Objects.CorrectedEvent.Constants)
    (w : ℂ) (s : ℝ) (hs : 0 < s) :
    ∀ᵐ g ∂μ, Objects.CorrectedEvent.regGood C (D g) s w ↔
      0 < aroundDist (D g) (⟨(w, s, 2*s), hs, by linarith⟩ : EuclideanAnnulus) ∧
      aroundDist (D g) (⟨(w, s, 2*s), hs, by linarith⟩ : EuclideanAnnulus) < ⊤ ∧
      0 < acrossDist (D g) (⟨(w, s, 2*s), hs, by linarith⟩ : EuclideanAnnulus) ∧
      acrossDist (D g) (⟨(w, s, 2*s), hs, by linarith⟩ : EuclideanAnnulus) < ⊤ ∧
      aroundDist (D g) (⟨(w, s, 2*s), hs, by linarith⟩ : EuclideanAnnulus) ≤
        ENNReal.ofReal C.c_reg⁻¹ *
          acrossDist (D g) (⟨(w, s, 2*s), hs, by linarith⟩ : EuclideanAnnulus) := by
  have hs2 : s < 2*s := by linarith
  filter_upwards [ae_acr_eq_ambientAcross μ hμ ξ Q D hD w s (2*s) hs hs2] with g heq
  rw [Objects.CorrectedEvent.regGood, Objects.ClauseMeasurability.around_eq_aroundDist (D g) w s (2*s) hs hs2, heq]
  rfl

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3
