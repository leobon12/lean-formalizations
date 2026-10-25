import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.RegMarginal
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.AroundLocality




 


set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3

theorem regGood_iff_of_internal_eq
    (C : Objects.CorrectedEvent.Constants) (D E : LSCMetric)
    (hBD : BiLipschitz.Barrier.Barrier D) (hBE : BiLipschitz.Barrier.Barrier E)
    (hLD : D.IsLengthSpace) (hLE : E.IsLengthSpace)
    (w : ℂ) (s : ℝ) (hs : 0 < s)
    (U : Set ℂ)
    (hK : BiLipschitz.Barrier.closedAnn w s (2*s) ⊆ U)
    (hA : EuclideanAnnulus.toSet
      (⟨(w, s, 2*s), hs, by linarith⟩ : EuclideanAnnulus) ⊆ U)
    (hint : D.internal U = E.internal U) :
    Objects.CorrectedEvent.regGood C D s w ↔ Objects.CorrectedEvent.regGood C E s w := by
  have hs2 : s < 2*s := by linarith
  let A : EuclideanAnnulus := ⟨(w, s, 2*s), hs, hs2⟩
  have hcross : acrossDist D A = acrossDist E A := by
    rw [BiLipschitz.Barrier.acrossDist_eq_iInf_internal D hBD hLD A hK,
      BiLipschitz.Barrier.acrossDist_eq_iInf_internal E hBE hLE A hK, hint]
  have haround : aroundDist D A = aroundDist E A :=
    BiLipschitz.EqualNormalizer.aroundDist_eq_of_internal_eq D E U hint A hA
  have hacr : Objects.CorrectedEvent.acr D w s (2*s) = Objects.CorrectedEvent.acr E w s (2*s) := by
    rw [acr_eq_ambientAcross_of_barrier D hBD hLD w s (2*s) hs hs2,
      acr_eq_ambientAcross_of_barrier E hBE hLE w s (2*s) hs hs2]
    exact hcross
  have har : Objects.CorrectedEvent.around D w s (2*s) = Objects.CorrectedEvent.around E w s (2*s) := by
    rw [Objects.ClauseMeasurability.around_eq_aroundDist D w s (2*s) hs hs2,
      Objects.ClauseMeasurability.around_eq_aroundDist E w s (2*s) hs hs2]
    exact haround
  simp only [Objects.CorrectedEvent.regGood, har, hacr]

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3
