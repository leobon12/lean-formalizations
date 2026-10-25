import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.E1eVersioned
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale.CenteredEvent




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.GridCover

private theorem e1e_radius_pos (n j : ℕ) : 0 < e1eRadius n j := by
  unfold e1eRadius e1eEps
  positivity

private theorem crossing_shape_eq (x : ℂ) (r : Set.Ioi (0 : ℝ)) :
    BiLipschitz.OneScale.crossingAt x r = BiLipschitz.PaidSeparators.eblAcrossAnn x r r.2 := by
  apply Subtype.ext
  simp only [BiLipschitz.OneScale.crossingAt, BiLipschitz.OneScale.crossingShape, Positivity.Witnesses.annulusTranslate,
    EuclideanAnnulus.dilate, BiLipschitz.PaidSeparators.eblAcrossAnn, EuclideanAnnulus.center,
    EuclideanAnnulus.innerRadius, EuclideanAnnulus.outerRadius, smul_zero, zero_add]
  congr 1 <;> ring

theorem separator_shape_eq (x : ℂ) (r : Set.Ioi (0 : ℝ)) :
    BiLipschitz.OneScale.separatorAt x r = BiLipschitz.PaidSeparators.sepAnn x r r.2 := by
  apply Subtype.ext
  simp only [BiLipschitz.OneScale.separatorAt, BiLipschitz.OneScale.separatorShape, Positivity.Witnesses.annulusTranslate,
    EuclideanAnnulus.dilate, BiLipschitz.PaidSeparators.sepAnn, EuclideanAnnulus.center,
    EuclideanAnnulus.innerRadius, EuclideanAnnulus.outerRadius, smul_zero, zero_add]
  congr 1 <;> ring

theorem raw_event_eq (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric) (A : ℝ) {Ω : Type} (h : Ω → DistC)
    (n : ℕ) (x : ℂ) (j : ℕ) :
    e1eGood ξ Q D D' A h n x j =
      h ⁻¹' BiLipschitz.OneScale.pairedRawEvent ξ Q D D' x ⟨e1eRadius n j, e1e_radius_pos n j⟩ A := by
  ext ω
  simp only [e1eGood, BiLipschitz.OneScale.pairedRawEvent, Set.mem_setOf_eq, Set.mem_preimage,
    BiLipschitz.PaidSeparators.GoodScalar, e1eNormalizer]
  rw [← crossing_shape_eq x ⟨e1eRadius n j, e1e_radius_pos n j⟩,
    ← separator_shape_eq x ⟨e1eRadius n j, e1e_radius_pos n j⟩]
  constructor
  · rintro ⟨-, hlow, hhigh⟩
    constructor
    · convert hlow using 1
      congr 1
      ring
    · convert hhigh using 1
      congr 1
      ring
  · rintro ⟨hlow, hhigh⟩
    refine ⟨?_, ?_, ?_⟩
    · have hr : 0 < e1eRadius n j := e1e_radius_pos n j
      exact mul_pos (Real.rpow_pos_of_pos hr _) (Real.exp_pos _)
    · convert hlow using 1
      congr 1
      ring
    · convert hhigh using 1
      congr 1
      ring

end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer
