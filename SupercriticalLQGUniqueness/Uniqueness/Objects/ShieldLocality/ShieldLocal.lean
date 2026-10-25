import SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.Block
import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.LocalDet




 






set_option autoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ShieldLocality

 
theorem shieldAt_iff_of_internal_eq (C : Objects.CorrectedEvent.Constants) (D E : LSCMetric)
    (hBD : BiLipschitz.Barrier.Barrier D) (hBE : BiLipschitz.Barrier.Barrier E)
    (hLD : D.IsLengthSpace) (hLE : E.IsLengthSpace)
    (t : ℝ) (ht : 0 < t) (U : Set ℂ)
    (hK : BiLipschitz.Barrier.closedAnn 0 (2 * t) (3 * t) ⊆ U)
    (hA : EuclideanAnnulus.toSet
      (⟨(0, t, 2 * t), ht, by linarith⟩ : EuclideanAnnulus) ⊆ U)
    (hint : D.internal U = E.internal U) :
    Objects.Excursions.shieldAt C D t ↔ Objects.Excursions.shieldAt C E t := by
  have ht2 : t < 2 * t := by linarith
  have ht3 : 2 * t < 3 * t := by linarith
  let A : EuclideanAnnulus := ⟨(0, t, 2 * t), ht, ht2⟩
  let B : EuclideanAnnulus := ⟨(0, 2 * t, 3 * t), by linarith, ht3⟩
  have hcross : acrossDist D B = acrossDist E B := by
    rw [BiLipschitz.Barrier.acrossDist_eq_iInf_internal D hBD hLD B hK,
      BiLipschitz.Barrier.acrossDist_eq_iInf_internal E hBE hLE B hK, hint]
  have haround : aroundDist D A = aroundDist E A :=
    BiLipschitz.EqualNormalizer.aroundDist_eq_of_internal_eq D E U hint A hA
  have hacr : Objects.CorrectedEvent.acr D 0 (2 * t) (3 * t) =
      Objects.CorrectedEvent.acr E 0 (2 * t) (3 * t) := by
    rw [Objects.ProbabilityS3.acr_eq_ambientAcross_of_barrier D hBD hLD 0 (2 * t) (3 * t)
        (by linarith) ht3,
      Objects.ProbabilityS3.acr_eq_ambientAcross_of_barrier E hBE hLE 0 (2 * t) (3 * t)
        (by linarith) ht3]
    exact hcross
  have har : Objects.CorrectedEvent.around D 0 t (2 * t) = Objects.CorrectedEvent.around E 0 t (2 * t) := by
    rw [Objects.ClauseMeasurability.around_eq_aroundDist D 0 t (2 * t) ht ht2,
      Objects.ClauseMeasurability.around_eq_aroundDist E 0 t (2 * t) ht ht2]
    exact haround
  simp only [Objects.Excursions.shieldAt, har, hacr]

 
theorem shield_iff_of_internal_eq (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData)
    (Ksh : ℕ) (D E : LSCMetric)
    (hBD : BiLipschitz.Barrier.Barrier D) (hBE : BiLipschitz.Barrier.Barrier E)
    (hLD : D.IsLengthSpace) (hLE : E.IsLengthSpace)
    (hρr : 0 < T.rho * T.r) (U : Set ℂ)
    (hK : ∀ k ∈ Finset.Icc 1 Ksh,
      BiLipschitz.Barrier.closedAnn 0 (2 * (3 * 8 ^ (Ksh - k) * (T.rho * T.r)))
        (3 * (3 * 8 ^ (Ksh - k) * (T.rho * T.r))) ⊆ U)
    (hA : ∀ k ∈ Finset.Icc 1 Ksh,
      EuclideanAnnulus.toSet
        (⟨(0, 3 * 8 ^ (Ksh - k) * (T.rho * T.r),
          2 * (3 * 8 ^ (Ksh - k) * (T.rho * T.r))),
          by exact mul_pos (mul_pos (by norm_num) (pow_pos (by norm_num) _)) hρr,
          by
            have ht : 0 < 3 * 8 ^ (Ksh - k) * (T.rho * T.r) :=
              mul_pos (mul_pos (by norm_num) (pow_pos (by norm_num) _)) hρr
            linarith⟩ : EuclideanAnnulus) ⊆ U)
    (hint : D.internal U = E.internal U) :
    Objects.Excursions.shield C T Ksh D ↔ Objects.Excursions.shield C T Ksh E := by
  simp only [Objects.Excursions.shield]
  exact exists_congr fun k => and_congr_right fun hk => by
    have ht : 0 < 3 * 8 ^ (Ksh - k) * (T.rho * T.r) :=
      mul_pos (mul_pos (by norm_num) (pow_pos (by norm_num) _)) hρr
    exact shieldAt_iff_of_internal_eq C D E hBD hBE hLD hLE _ ht U
      (hK k hk) (hA k hk) hint

end SupercriticalLQGUniqueness.Uniqueness.Objects.ShieldLocality
