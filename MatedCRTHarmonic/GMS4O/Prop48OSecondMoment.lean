import MatedCRTHarmonic.GMS4.Prop48CanonicalNear
import MatedCRTHarmonic.GMS4.Prop48SecondMoment
import MatedCRTHarmonic.GMS4.Prop48Rate
import MatedCRTHarmonic.GMS4O.Prop48OCondMean

/-!
# The (4.30)–(4.38) second moment with the jointly measurable conditional mean

[18] bounds the second moment of the centred
spatial integral `∫_D f (1_F u_* − m)` by splitting the pair integral into near pairs
`|z − w| ≤ 2 ε^{q−4ζ}` and far pairs. This file assembles that bound for the canonical zero-cone
coupling with `m = p48oCondMeanJoint` (`GMS4O/Prop48OCondMean.lean`):

* near pairs (4.32)–(4.34): the `Lemma49ConditionalMoments.near_pair` (the masked density is at
  most `ε^{-ζ}` times the masked area ratio, plus Lemma 4.9's area moments), and the a.s. bound
  `m ≤ A`, give the centred covariance bound `ε^{-2ζ} K + A²` on a pair set of measure
  `≲ ε^{2q−8ζ}`;
* far pairs (4.35)–(4.37): the pointwise covariance bound `≤ C ε^ζ` is the single named input
  `P48OFarPairCovarianceBound` (the corrected, unconditional form of (4.36));
* joint integrability of the pair kernel (needed by Fubini) is proved here from the same moments.

The result is the **unconditional** bound `E[(∫_D f (X' − m))²] ≤ C ε^{min(2q−10ζ, ζ)} ‖f‖²_∞`
(`p48o_secondMoment_of_farPair`), which implies the source's (4.38) on the good event.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4O

open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4.Canonical

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **The far-pair input** ([18] (4.35)–(4.36), in the corrected unconditional form): for every
radius, centred all-visit densities at centres farther apart than `2 ε^{q−4ζ}` have covariance at most
`C ε^ζ`, with the jointly measurable conditional mean. -/
def P48OFarPairCovarianceBound
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (q ζ : ℝ) : Prop :=
  ∀ ρ ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 ≤ C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ z ∈ ball (0 : ℂ) ρ, ∀ w ∈ ball (0 : ℂ) ρ, 2 * ε ^ (q - 4 * ζ) < dist z w →
      ∫ ω, (maskedUStarPrime D hγ ε q ζ z ω - p48oCondMeanJoint D hγ ε q ζ ω z) *
        (maskedUStarPrime D hγ ε q ζ w ω - p48oCondMeanJoint D hγ ε q ζ ω w) ∂P ≤ C * ε ^ ζ

/-! ### Auxiliary facts -/

lemma p48o_ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g : α → ℝ) : ENNReal.ofReal (∫ a, g a ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (g a) ∂μ := by
  by_cases hg : Integrable g μ
  · rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg]
    calc ENNReal.ofReal ((∫⁻ a, ENNReal.ofReal (g a) ∂μ).toReal -
          (∫⁻ a, ENNReal.ofReal (-g a) ∂μ).toReal)
        ≤ ENNReal.ofReal (∫⁻ a, ENNReal.ofReal (g a) ∂μ).toReal :=
          ENNReal.ofReal_le_ofReal (sub_le_self _ ENNReal.toReal_nonneg)
      _ ≤ ∫⁻ a, ENNReal.ofReal (g a) ∂μ := ENNReal.ofReal_toReal_le
  · rw [integral_undef hg, ENNReal.ofReal_zero]
    exact zero_le

/-- The jointly measurable centred integrand `f(z) (X̃(ω, z) − m(ω, z))`, with the test extended by
zero off `B_ρ(0)`. -/
def p48oCentredJoint
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ ρ : ℝ) (f : ℂ → ℝ) (ω : Ω) (z : ℂ) : ℝ :=
  p48oTestExt ρ f z * (p48oMaskedVersion D hγ ε q ζ ω z - p48oCondMeanJoint D hγ ε q ζ ω z)

lemma measurable_p48oCentredJoint
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε) (q ζ ρ : ℝ) {f : ℂ → ℝ}
    (hfm : P48OTestMeasurable ρ f) :
    Measurable fun p : Ω × ℂ => p48oCentredJoint D hγ ε q ζ ρ f p.1 p.2 :=
  ((measurable_p48oTestExt hfm).comp measurable_snd).mul
    ((measurable_p48oMaskedVersion D hγ hε q ζ).sub (measurable_p48oCondMeanJoint D hγ ε q ζ))

/-- A.s., the centred all-visit integral is the integral of the jointly measurable integrand. -/
lemma p48o_ae_primedFluctuationJoint_eq
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) {ρ : ℝ} {domain : Set ℂ} {f : ℂ → ℝ}
    (hadm : GMS4.Prop48TestPairAdmissible ρ domain f) :
    ∀ᵐ ω ∂P, p48oPrimedFluctuationJoint D hγ ε q ζ domain f ω =
      ∫ z, p48oCentredJoint D hγ ε q ζ ρ f ω z ∂(volume.restrict domain) := by
  filter_upwards [p48o_ae_maskedVersion_eq D hγ ε q ζ,
    p48o_ae_ae_maskedPrime_eq_masked D hγ ε q ζ] with ω h1 h2
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae h2, ae_restrict_mem hadm.domain_borel] with z hz hzD
  simp only [p48oCentredJoint]
  rw [p48oTestExt_eq_of_mem (hadm.domain_subset_ball hzD), h1 z, hz]

/-- The masked version has first moment at most `A` at every centre of `B_ρ(0)`. -/
lemma p48o_lintegral_maskedVersion_le
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) {A : ℝ} {z : ℂ}
    (hmean : Integrable (maskedUStar D hγ ε q ζ z) P ∧
      ∀ᵐ ω ∂P, conditionalMean D hγ ε q ζ ω z ≤ A) :
    ∫⁻ ω, ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) ∂P ≤ ENNReal.ofReal A := by
  let _ := D.isProbabilityMeasure
  obtain ⟨hi, hb⟩ := hmean
  have heq' : (fun ω => ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z)) =ᵐ[P]
      fun ω => ENNReal.ofReal (maskedUStar D hγ ε q ζ z ω) := by
    filter_upwards [p48o_ae_maskedVersion_eq D hγ ε q ζ] with ω h
    rw [h z]
  have hm : MeasurableSpace.comap (circleObservation D hγ ε q ζ z) inferInstance ≤
      ‹MeasurableSpace Ω› := (measurable_circleObservation D hγ ε q ζ z).comap_le
  rw [lintegral_congr_ae heq', ← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun ω => maskedUStar_nonneg D hγ ε q ζ z ω)]
  apply ENNReal.ofReal_le_ofReal
  calc ∫ ω, maskedUStar D hγ ε q ζ z ω ∂P = ∫ ω, conditionalMean D hγ ε q ζ ω z ∂P :=
        (integral_condExp hm).symm
    _ ≤ ∫ _ω, A ∂P := integral_mono_ae integrable_condExp (integrable_const A) hb
    _ = A := by simp

lemma p48o_ofReal_rpow_half_mul_self {K : ℝ} (hK : 0 ≤ K) :
    ENNReal.ofReal K ^ (1 / (2 : ℝ)) * ENNReal.ofReal K ^ (1 / (2 : ℝ)) = ENNReal.ofReal K := by
  rw [ENNReal.ofReal_rpow_of_nonneg hK (by norm_num), ← ENNReal.ofReal_mul (by positivity),
    ← Real.rpow_add' hK (by norm_num)]
  norm_num

lemma p48o_ofReal_rpow_neg_sq {ε ζ : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal (ε ^ (-ζ)) ^ 2 = ENNReal.ofReal (ε ^ (-(2 * ζ))) := by
  rw [← ENNReal.ofReal_pow (Real.rpow_nonneg hε.le _), ← Real.rpow_natCast,
    ← Real.rpow_mul hε.le]
  norm_num
  ring_nf

/-! ### The uncentred pair moments -/

section Pair

variable (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
  (hγ : γ ∈ Ioo (0 : ℝ) 2)

/-- The uncentred product moment of the masked versions (from the `near_pair`). -/
lemma p48o_lintegral_maskedVersion_mul_le {q ζ ρ : ℝ} (H : Lemma49ConditionalMoments D hγ q ζ ρ)
    {K : ℝ} (hK : 0 ≤ K)
    (hpair : ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) H.epsilonStar →
      ∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ w ∈ Metric.ball (0 : ℂ) ρ,
        (∫⁻ ω, ENNReal.ofReal (maskedUStar D hγ ε q ζ z ω) *
          ENNReal.ofReal (maskedUStar D hγ ε q ζ w ω) ∂P) ≤
            ENNReal.ofReal (ε ^ (-ζ)) ^ 2 *
              (ENNReal.ofReal K ^ (1 / (2 : ℝ)) * ENNReal.ofReal K ^ (1 / (2 : ℝ))))
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) H.epsilonStar) {z w : ℂ} (hz : z ∈ ball (0 : ℂ) ρ)
    (hw : w ∈ ball (0 : ℂ) ρ) :
    ∫⁻ ω, ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) *
      ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω w) ∂P ≤
        ENNReal.ofReal (ε ^ (-(2 * ζ)) * K) := by
  have heq : (fun ω => ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) *
      ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω w)) =ᵐ[P]
      fun ω => ENNReal.ofReal (maskedUStar D hγ ε q ζ z ω) *
        ENNReal.ofReal (maskedUStar D hγ ε q ζ w ω) := by
    filter_upwards [p48o_ae_maskedVersion_eq D hγ ε q ζ] with ω h
    rw [h z, h w]
  rw [lintegral_congr_ae heq]
  refine (hpair ε hε z hz w hw).trans (le_of_eq ?_)
  rw [p48o_ofReal_rpow_half_mul_self hK, p48o_ofReal_rpow_neg_sq hε.1,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hε.1.le _)]

/-- The a.s. bound `0 ≤ m ≤ A` gives `E[m_z m_w] ≤ A²` at centres of `B_ρ(0)`. -/
lemma p48o_lintegral_condMeanJoint_mul_le {ε q ζ ρ A : ℝ} (hε : 0 ≤ ε) (hA : 0 ≤ A)
    (hmean : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      Integrable (maskedUStar D hγ ε q ζ z) P ∧ ∀ᵐ ω ∂P, conditionalMean D hγ ε q ζ ω z ≤ A)
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) ρ) (hw : w ∈ ball (0 : ℂ) ρ) :
    ∫⁻ ω, ENNReal.ofReal (p48oCondMeanJoint D hγ ε q ζ ω z * p48oCondMeanJoint D hγ ε q ζ ω w) ∂P
      ≤ ENNReal.ofReal (A ^ 2) := by
  let _ := D.isProbabilityMeasure
  have hle := p48o_condMeanJoint_le_of_mean D hγ hε hmean
  calc ∫⁻ ω, ENNReal.ofReal (p48oCondMeanJoint D hγ ε q ζ ω z *
        p48oCondMeanJoint D hγ ε q ζ ω w) ∂P ≤ ∫⁻ _ω, ENNReal.ofReal (A ^ 2) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hle z hz, hle w hw] with ω h1 h2
        refine ENNReal.ofReal_le_ofReal ?_
        rw [sq]
        exact mul_le_mul h1 h2 (p48oCondMeanJoint_nonneg D hγ ε q ζ ω w) hA
    _ = ENNReal.ofReal (A ^ 2) := by rw [lintegral_const, measure_univ, mul_one]

end Pair

/-! ### Near and far pointwise bounds -/

section Bounds

variable (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
  (hγ : γ ∈ Ioo (0 : ℝ) 2)

lemma p48o_testExt_bounds {ρ : ℝ} {domain : Set ℂ} {f : ℂ → ℝ}
    (hadm : GMS4.Prop48TestPairAdmissible ρ domain f) {z : ℂ} (hz : z ∈ ball (0 : ℂ) ρ) :
    0 ≤ p48oTestExt ρ f z ∧ p48oTestExt ρ f z ≤ GMS4.prop48TestSupNorm ρ f := by
  rw [p48oTestExt_eq_of_mem hz]
  exact ⟨hadm.test_nonnegative z hz, (le_abs_self _).trans (p48o_abs_test_le hadm hz)⟩

/-- **Near pairs** (4.32)–(4.33): the centred pair moment is at most `N² (ε^{-2ζ} K + A²)`. -/
lemma p48o_ofReal_integral_centred_near_le {q ζ ρ : ℝ} (H : Lemma49ConditionalMoments D hγ q ζ ρ)
    {K : ℝ} (hK : 0 ≤ K)
    (hpair : ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) H.epsilonStar →
      ∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ w ∈ Metric.ball (0 : ℂ) ρ,
        (∫⁻ ω, ENNReal.ofReal (maskedUStar D hγ ε q ζ z ω) *
          ENNReal.ofReal (maskedUStar D hγ ε q ζ w ω) ∂P) ≤
            ENNReal.ofReal (ε ^ (-ζ)) ^ 2 *
              (ENNReal.ofReal K ^ (1 / (2 : ℝ)) * ENNReal.ofReal K ^ (1 / (2 : ℝ))))
    {A : ℝ} (hA : 0 ≤ A) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) H.epsilonStar)
    (hmean : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      Integrable (maskedUStar D hγ ε q ζ z) P ∧ ∀ᵐ ω ∂P, conditionalMean D hγ ε q ζ ω z ≤ A)
    {domain : Set ℂ} {f : ℂ → ℝ} (hadm : GMS4.Prop48TestPairAdmissible ρ domain f)
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) ρ) (hw : w ∈ ball (0 : ℂ) ρ) :
    ENNReal.ofReal (∫ ω, p48oCentredJoint D hγ ε q ζ ρ f ω z *
        p48oCentredJoint D hγ ε q ζ ρ f ω w ∂P) ≤
      ENNReal.ofReal (GMS4.prop48TestSupNorm ρ f ^ 2 * (ε ^ (-(2 * ζ)) * K + A ^ 2)) := by
  set N := GMS4.prop48TestSupNorm ρ f with hN
  obtain ⟨hfz0, hfzN⟩ := p48o_testExt_bounds hadm hz
  obtain ⟨hfw0, hfwN⟩ := p48o_testExt_bounds hadm hw
  have hXm := measurable_p48oMaskedVersion D hγ hε.1.le q ζ
  have hmm := measurable_p48oCondMeanJoint D hγ ε q ζ
  have hXz : Measurable fun ω => p48oMaskedVersion D hγ ε q ζ ω z := by
    have h := hXm.comp (measurable_id.prodMk (measurable_const (a := z)) :
      Measurable fun ω : Ω => (ω, z))
    exact h
  have hXw : Measurable fun ω => p48oMaskedVersion D hγ ε q ζ ω w := by
    have h := hXm.comp (measurable_id.prodMk (measurable_const (a := w)) :
      Measurable fun ω : Ω => (ω, w))
    exact h
  have hpt : ∀ ω, p48oCentredJoint D hγ ε q ζ ρ f ω z * p48oCentredJoint D hγ ε q ζ ρ f ω w ≤
      N ^ 2 * (p48oMaskedVersion D hγ ε q ζ ω z * p48oMaskedVersion D hγ ε q ζ ω w +
        p48oCondMeanJoint D hγ ε q ζ ω z * p48oCondMeanJoint D hγ ε q ζ ω w) := by
    intro ω
    have hx := p48oMaskedVersion_nonneg D hγ ε q ζ ω z
    have hy := p48oMaskedVersion_nonneg D hγ ε q ζ ω w
    have hmx := p48oCondMeanJoint_nonneg D hγ ε q ζ ω z
    have hmy := p48oCondMeanJoint_nonneg D hγ ε q ζ ω w
    have hc := prop48_centered_near_pair_le _ _ _ _ hx hy hmx hmy
    have hbr : 0 ≤ p48oMaskedVersion D hγ ε q ζ ω z * p48oMaskedVersion D hγ ε q ζ ω w +
        p48oCondMeanJoint D hγ ε q ζ ω z * p48oCondMeanJoint D hγ ε q ζ ω w := by positivity
    have hff : p48oTestExt ρ f z * p48oTestExt ρ f w ≤ N ^ 2 := by
      rw [sq]; exact mul_le_mul hfzN hfwN hfw0 ((hfz0).trans hfzN)
    calc p48oCentredJoint D hγ ε q ζ ρ f ω z * p48oCentredJoint D hγ ε q ζ ρ f ω w
        = (p48oTestExt ρ f z * p48oTestExt ρ f w) *
            ((p48oMaskedVersion D hγ ε q ζ ω z - p48oCondMeanJoint D hγ ε q ζ ω z) *
              (p48oMaskedVersion D hγ ε q ζ ω w - p48oCondMeanJoint D hγ ε q ζ ω w)) := by
          simp only [p48oCentredJoint]; ring
      _ ≤ (p48oTestExt ρ f z * p48oTestExt ρ f w) *
            (p48oMaskedVersion D hγ ε q ζ ω z * p48oMaskedVersion D hγ ε q ζ ω w +
              p48oCondMeanJoint D hγ ε q ζ ω z * p48oCondMeanJoint D hγ ε q ζ ω w) :=
          mul_le_mul_of_nonneg_left hc (mul_nonneg hfz0 hfw0)
      _ ≤ N ^ 2 * (p48oMaskedVersion D hγ ε q ζ ω z * p48oMaskedVersion D hγ ε q ζ ω w +
              p48oCondMeanJoint D hγ ε q ζ ω z * p48oCondMeanJoint D hγ ε q ζ ω w) :=
          mul_le_mul_of_nonneg_right hff hbr
  have hmz : Measurable fun ω => p48oCondMeanJoint D hγ ε q ζ ω z := by
    have h := hmm.comp (measurable_id.prodMk (measurable_const (a := z)) :
      Measurable fun ω : Ω => (ω, z))
    exact h
  have hmw : Measurable fun ω => p48oCondMeanJoint D hγ ε q ζ ω w := by
    have h := hmm.comp (measurable_id.prodMk (measurable_const (a := w)) :
      Measurable fun ω : Ω => (ω, w))
    exact h
  calc ENNReal.ofReal (∫ ω, p48oCentredJoint D hγ ε q ζ ρ f ω z *
        p48oCentredJoint D hγ ε q ζ ρ f ω w ∂P)
      ≤ ∫⁻ ω, ENNReal.ofReal (p48oCentredJoint D hγ ε q ζ ρ f ω z *
          p48oCentredJoint D hγ ε q ζ ρ f ω w) ∂P := p48o_ofReal_integral_le_lintegral _
    _ ≤ ∫⁻ ω, ENNReal.ofReal (N ^ 2) *
          (ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) *
              ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω w) +
            ENNReal.ofReal (p48oCondMeanJoint D hγ ε q ζ ω z *
              p48oCondMeanJoint D hγ ε q ζ ω w)) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_mul (p48oMaskedVersion_nonneg D hγ ε q ζ ω z),
          ← ENNReal.ofReal_add
            (mul_nonneg (p48oMaskedVersion_nonneg D hγ ε q ζ ω z)
              (p48oMaskedVersion_nonneg D hγ ε q ζ ω w))
            (mul_nonneg (p48oCondMeanJoint_nonneg D hγ ε q ζ ω z)
              (p48oCondMeanJoint_nonneg D hγ ε q ζ ω w)),
          ← ENNReal.ofReal_mul (sq_nonneg N)]
        exact ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal (N ^ 2) *
          ((∫⁻ ω, ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) *
              ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω w) ∂P) +
            ∫⁻ ω, ENNReal.ofReal (p48oCondMeanJoint D hγ ε q ζ ω z *
              p48oCondMeanJoint D hγ ε q ζ ω w) ∂P) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left]
        exact (ENNReal.measurable_ofReal.comp hXz).mul (ENNReal.measurable_ofReal.comp hXw)
    _ ≤ ENNReal.ofReal (N ^ 2) * (ENNReal.ofReal (ε ^ (-(2 * ζ)) * K) + ENNReal.ofReal (A ^ 2)) := by
        gcongr
        · exact p48o_lintegral_maskedVersion_mul_le D hγ H hK hpair hε hz hw
        · exact p48o_lintegral_condMeanJoint_mul_le D hγ hε.1.le hA hmean hz hw
    _ = ENNReal.ofReal (N ^ 2 * (ε ^ (-(2 * ζ)) * K + A ^ 2)) := by
        rw [← ENNReal.ofReal_add (mul_nonneg (Real.rpow_nonneg hε.1.le _) hK) (sq_nonneg A),
          ← ENNReal.ofReal_mul (sq_nonneg N)]

/-- **Far pairs**: the named covariance input, weighted by the test. -/
lemma p48o_ofReal_integral_centred_far_le {q ζ ρ ε Cf : ℝ} (hCf : 0 ≤ Cf) (hε : 0 ≤ ε)
    (hfar : ∀ z ∈ ball (0 : ℂ) ρ, ∀ w ∈ ball (0 : ℂ) ρ, 2 * ε ^ (q - 4 * ζ) < dist z w →
      ∫ ω, (maskedUStarPrime D hγ ε q ζ z ω - p48oCondMeanJoint D hγ ε q ζ ω z) *
        (maskedUStarPrime D hγ ε q ζ w ω - p48oCondMeanJoint D hγ ε q ζ ω w) ∂P ≤ Cf * ε ^ ζ)
    {domain : Set ℂ} {f : ℂ → ℝ} (hadm : GMS4.Prop48TestPairAdmissible ρ domain f)
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) ρ) (hw : w ∈ ball (0 : ℂ) ρ)
    (hzw : 2 * ε ^ (q - 4 * ζ) < dist z w) :
    ENNReal.ofReal (∫ ω, p48oCentredJoint D hγ ε q ζ ρ f ω z *
        p48oCentredJoint D hγ ε q ζ ρ f ω w ∂P) ≤
      ENNReal.ofReal (GMS4.prop48TestSupNorm ρ f ^ 2 * (Cf * ε ^ ζ)) := by
  obtain ⟨hfz0, hfzN⟩ := p48o_testExt_bounds hadm hz
  obtain ⟨hfw0, hfwN⟩ := p48o_testExt_bounds hadm hw
  have e : (∫ ω, p48oCentredJoint D hγ ε q ζ ρ f ω z * p48oCentredJoint D hγ ε q ζ ρ f ω w ∂P) =
      (p48oTestExt ρ f z * p48oTestExt ρ f w) *
        ∫ ω, (maskedUStarPrime D hγ ε q ζ z ω - p48oCondMeanJoint D hγ ε q ζ ω z) *
          (maskedUStarPrime D hγ ε q ζ w ω - p48oCondMeanJoint D hγ ε q ζ ω w) ∂P := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [p48o_ae_maskedVersion_eq D hγ ε q ζ,
      ae_maskedUStarPrime_eq_masked_fixed D hγ ε q ζ z,
      ae_maskedUStarPrime_eq_masked_fixed D hγ ε q ζ w] with ω h1 h2 h3
    simp only [p48oCentredJoint]
    rw [h1 z, h1 w, h2, h3]
    ring
  rw [e]
  refine ENNReal.ofReal_le_ofReal ?_
  have hff : p48oTestExt ρ f z * p48oTestExt ρ f w ≤ GMS4.prop48TestSupNorm ρ f ^ 2 := by
    rw [sq]; exact mul_le_mul hfzN hfwN hfw0 (hfz0.trans hfzN)
  calc (p48oTestExt ρ f z * p48oTestExt ρ f w) *
        ∫ ω, (maskedUStarPrime D hγ ε q ζ z ω - p48oCondMeanJoint D hγ ε q ζ ω z) *
          (maskedUStarPrime D hγ ε q ζ w ω - p48oCondMeanJoint D hγ ε q ζ ω w) ∂P
      ≤ (p48oTestExt ρ f z * p48oTestExt ρ f w) * (Cf * ε ^ ζ) :=
        mul_le_mul_of_nonneg_left (hfar z hz w hw hzw) (mul_nonneg hfz0 hfw0)
    _ ≤ GMS4.prop48TestSupNorm ρ f ^ 2 * (Cf * ε ^ ζ) :=
        mul_le_mul_of_nonneg_right hff (mul_nonneg hCf (Real.rpow_nonneg hε _))

/-- **Joint integrability of the pair kernel** (the Fubini premise of (4.30)), from Lemma 4.9's
moments and the mean bound. -/
lemma p48o_integrable_pairKernel {q ζ ρ : ℝ} (H : Lemma49ConditionalMoments D hγ q ζ ρ)
    {K : ℝ} (hK : 0 ≤ K)
    (hpair : ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) H.epsilonStar →
      ∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ w ∈ Metric.ball (0 : ℂ) ρ,
        (∫⁻ ω, ENNReal.ofReal (maskedUStar D hγ ε q ζ z ω) *
          ENNReal.ofReal (maskedUStar D hγ ε q ζ w ω) ∂P) ≤
            ENNReal.ofReal (ε ^ (-ζ)) ^ 2 *
              (ENNReal.ofReal K ^ (1 / (2 : ℝ)) * ENNReal.ofReal K ^ (1 / (2 : ℝ))))
    {A : ℝ} (hA : 0 ≤ A) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) H.epsilonStar)
    (hmean : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      Integrable (maskedUStar D hγ ε q ζ z) P ∧ ∀ᵐ ω ∂P, conditionalMean D hγ ε q ζ ω z ≤ A)
    {domain : Set ℂ} {f : ℂ → ℝ} (hadm : GMS4.Prop48TestPairAdmissible ρ domain f) :
    Integrable (fun t : Ω × (ℂ × ℂ) => p48oCentredJoint D hγ ε q ζ ρ f t.1 t.2.1 *
        p48oCentredJoint D hγ ε q ζ ρ f t.1 t.2.2)
      (P.prod ((volume.restrict domain).prod (volume.restrict domain))) := by
  let _ := D.isProbabilityMeasure
  set N := GMS4.prop48TestSupNorm ρ f with hN
  have hCm := measurable_p48oCentredJoint D hγ hε.1.le q ζ ρ hadm.test_measurable
  have hp1 : Measurable fun t : Ω × (ℂ × ℂ) => (t.1, t.2.1) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hp2 : Measurable fun t : Ω × (ℂ × ℂ) => (t.1, t.2.2) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have hF : Measurable fun t : Ω × (ℂ × ℂ) => p48oCentredJoint D hγ ε q ζ ρ f t.1 t.2.1 *
      p48oCentredJoint D hγ ε q ζ ρ f t.1 t.2.2 := by
    have h := (hCm.comp hp1).mul (hCm.comp hp2)
    exact h
  refine ⟨hF.aestronglyMeasurable, ?_⟩
  -- one pair
  set Bd : ℝ≥0∞ := ENNReal.ofReal (N ^ 2) *
    (ENNReal.ofReal (ε ^ (-(2 * ζ)) * K) + ENNReal.ofReal (A ^ 2) +
      (ENNReal.ofReal (ε ^ (-(2 * ζ)) * K) + ENNReal.ofReal (A ^ 2))) with hBd
  have hXm := measurable_p48oMaskedVersion D hγ hε.1.le q ζ
  have hmm := measurable_p48oCondMeanJoint D hγ ε q ζ
  have hpairBd : ∀ z ∈ domain, ∀ w ∈ domain,
      ∫⁻ ω, ‖p48oCentredJoint D hγ ε q ζ ρ f ω z * p48oCentredJoint D hγ ε q ζ ρ f ω w‖ₑ ∂P
        ≤ Bd := by
    intro z hzD w hwD
    have hz := hadm.domain_subset_ball hzD
    have hw := hadm.domain_subset_ball hwD
    obtain ⟨hfz0, hfzN⟩ := p48o_testExt_bounds hadm hz
    obtain ⟨hfw0, hfwN⟩ := p48o_testExt_bounds hadm hw
    have hXz : Measurable fun ω => p48oMaskedVersion D hγ ε q ζ ω z := by
      have h := hXm.comp (measurable_id.prodMk (measurable_const (a := z)) :
        Measurable fun ω : Ω => (ω, z))
      exact h
    have hXw : Measurable fun ω => p48oMaskedVersion D hγ ε q ζ ω w := by
      have h := hXm.comp (measurable_id.prodMk (measurable_const (a := w)) :
        Measurable fun ω : Ω => (ω, w))
      exact h
    have hmz : Measurable fun ω => p48oCondMeanJoint D hγ ε q ζ ω z := by
      have h := hmm.comp (measurable_id.prodMk (measurable_const (a := z)) :
        Measurable fun ω : Ω => (ω, z))
      exact h
    have hpt : ∀ ω, ‖p48oCentredJoint D hγ ε q ζ ρ f ω z *
        p48oCentredJoint D hγ ε q ζ ρ f ω w‖ₑ ≤
        ENNReal.ofReal (N ^ 2) *
          (ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) *
              ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) +
            ENNReal.ofReal (p48oCondMeanJoint D hγ ε q ζ ω z *
              p48oCondMeanJoint D hγ ε q ζ ω z) +
          (ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω w) *
              ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω w) +
            ENNReal.ofReal (p48oCondMeanJoint D hγ ε q ζ ω w *
              p48oCondMeanJoint D hγ ε q ζ ω w))) := by
      intro ω
      have hx := p48oMaskedVersion_nonneg D hγ ε q ζ ω z
      have hy := p48oMaskedVersion_nonneg D hγ ε q ζ ω w
      have hmx := p48oCondMeanJoint_nonneg D hγ ε q ζ ω z
      have hmy := p48oCondMeanJoint_nonneg D hγ ε q ζ ω w
      set x := p48oMaskedVersion D hγ ε q ζ ω z
      set y := p48oMaskedVersion D hγ ε q ζ ω w
      set mx := p48oCondMeanJoint D hγ ε q ζ ω z
      set my := p48oCondMeanJoint D hγ ε q ζ ω w
      set fz := p48oTestExt ρ f z
      set fw := p48oTestExt ρ f w
      rw [← ENNReal.ofReal_mul hx, ← ENNReal.ofReal_mul hy,
        ← ENNReal.ofReal_add (mul_nonneg hx hx) (mul_nonneg hmx hmx),
        ← ENNReal.ofReal_add (mul_nonneg hy hy) (mul_nonneg hmy hmy),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (sq_nonneg N), Real.enorm_eq_ofReal_abs]
      refine ENNReal.ofReal_le_ofReal ?_
      have habs1 : |x - mx| ≤ x + mx := abs_sub_le_of_nonneg_of_le hx (by linarith) hmx
        (by linarith)
      have habs2 : |y - my| ≤ y + my := abs_sub_le_of_nonneg_of_le hy (by linarith) hmy
        (by linarith)
      have hC : |fz * (x - mx) * (fw * (y - my))| ≤ N ^ 2 * ((x + mx) * (y + my)) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hfz0, abs_of_nonneg hfw0]
        have h1 : fz * |x - mx| ≤ N * (x + mx) :=
          mul_le_mul hfzN habs1 (abs_nonneg _) ((hfz0).trans hfzN)
        have h2 : fw * |y - my| ≤ N * (y + my) :=
          mul_le_mul hfwN habs2 (abs_nonneg _) ((hfw0).trans hfwN)
        calc fz * |x - mx| * (fw * |y - my|) ≤ (N * (x + mx)) * (N * (y + my)) :=
              mul_le_mul h1 h2 (mul_nonneg hfw0 (abs_nonneg _))
                (mul_nonneg ((hfz0).trans hfzN) (by linarith))
          _ = N ^ 2 * ((x + mx) * (y + my)) := by ring
      have hamgm : (x + mx) * (y + my) ≤ x * x + mx * mx + (y * y + my * my) := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (mx - my), sq_nonneg (x - my), sq_nonneg (mx - y)]
      calc |p48oCentredJoint D hγ ε q ζ ρ f ω z * p48oCentredJoint D hγ ε q ζ ρ f ω w|
          = |fz * (x - mx) * (fw * (y - my))| := rfl
        _ ≤ N ^ 2 * ((x + mx) * (y + my)) := hC
        _ ≤ N ^ 2 * (x * x + mx * mx + (y * y + my * my)) :=
          mul_le_mul_of_nonneg_left hamgm (sq_nonneg N)
    have hmw : Measurable fun ω => p48oCondMeanJoint D hγ ε q ζ ω w := by
      have h := hmm.comp (measurable_id.prodMk (measurable_const (a := w)) :
        Measurable fun ω : Ω => (ω, w))
      exact h
    have hmeasz : Measurable fun ω => ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) *
        ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) :=
      (ENNReal.measurable_ofReal.comp hXz).mul (ENNReal.measurable_ofReal.comp hXz)
    have hmeasw : Measurable fun ω => ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω w) *
        ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω w) :=
      (ENNReal.measurable_ofReal.comp hXw).mul (ENNReal.measurable_ofReal.comp hXw)
    have hmeasmz : Measurable fun ω => ENNReal.ofReal (p48oCondMeanJoint D hγ ε q ζ ω z *
        p48oCondMeanJoint D hγ ε q ζ ω z) := ENNReal.measurable_ofReal.comp (hmz.mul hmz)
    calc ∫⁻ ω, ‖p48oCentredJoint D hγ ε q ζ ρ f ω z *
          p48oCentredJoint D hγ ε q ζ ρ f ω w‖ₑ ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (N ^ 2) *
          (ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) *
              ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) +
            ENNReal.ofReal (p48oCondMeanJoint D hγ ε q ζ ω z *
              p48oCondMeanJoint D hγ ε q ζ ω z) +
          (ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω w) *
              ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω w) +
            ENNReal.ofReal (p48oCondMeanJoint D hγ ε q ζ ω w *
              p48oCondMeanJoint D hγ ε q ζ ω w))) ∂P := lintegral_mono hpt
      _ = ENNReal.ofReal (N ^ 2) *
          ((∫⁻ ω, ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) *
              ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) ∂P) +
            (∫⁻ ω, ENNReal.ofReal (p48oCondMeanJoint D hγ ε q ζ ω z *
              p48oCondMeanJoint D hγ ε q ζ ω z) ∂P) +
          ((∫⁻ ω, ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω w) *
              ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω w) ∂P) +
            ∫⁻ ω, ENNReal.ofReal (p48oCondMeanJoint D hγ ε q ζ ω w *
              p48oCondMeanJoint D hγ ε q ζ ω w) ∂P)) := by
          have hzsum : Measurable fun ω =>
              ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) *
                ENNReal.ofReal (p48oMaskedVersion D hγ ε q ζ ω z) +
              ENNReal.ofReal (p48oCondMeanJoint D hγ ε q ζ ω z *
                p48oCondMeanJoint D hγ ε q ζ ω z) := hmeasz.add hmeasmz
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_add_left hzsum, lintegral_add_left hmeasz,
            lintegral_add_left hmeasw]
      _ ≤ Bd := by
          rw [hBd]
          gcongr
          · exact p48o_lintegral_maskedVersion_mul_le D hγ H hK hpair hε hz hz
          · exact p48o_lintegral_condMeanJoint_mul_le D hγ hε.1.le hA hmean hz hz
          · exact p48o_lintegral_maskedVersion_mul_le D hγ H hK hpair hε hw hw
          · exact p48o_lintegral_condMeanJoint_mul_le D hγ hε.1.le hA hmean hw hw
  have hmem : ∀ᵐ p ∂((volume.restrict domain).prod (volume.restrict domain)),
      p ∈ domain ×ˢ domain := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (hadm.domain_borel.prod hadm.domain_borel)
  rw [HasFiniteIntegral, lintegral_prod_symm' _ hF.enorm]
  calc ∫⁻ p, ∫⁻ ω, ‖p48oCentredJoint D hγ ε q ζ ρ f ω p.1 *
        p48oCentredJoint D hγ ε q ζ ρ f ω p.2‖ₑ ∂P
          ∂((volume.restrict domain).prod (volume.restrict domain))
      ≤ ∫⁻ _p, Bd ∂((volume.restrict domain).prod (volume.restrict domain)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hmem] with p hp
        exact hpairBd p.1 hp.1 p.2 hp.2
    _ = Bd * (volume domain * volume domain) := by
        rw [lintegral_const, Measure.prod_restrict, Measure.restrict_apply_univ,
          Measure.prod_prod]
    _ < ⊤ := by
        have hD : volume domain < ⊤ := p48o_volume_lt_top_of_admissible hadm
        exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (by simp only [ENNReal.add_lt_top, ENNReal.ofReal_lt_top, and_self]))
          (ENNReal.mul_lt_top hD hD)

end Bounds

/-! ### Assembly of (4.30)–(4.38) -/

lemma p48o_setLIntegral_prod_restrict_le {domain : Set ℂ} (hD : MeasurableSet domain)
    {S : Set (ℂ × ℂ)} (hS : MeasurableSet S) {F : ℂ × ℂ → ℝ≥0∞} {Bd : ℝ≥0∞}
    (hF : ∀ p ∈ S, p.1 ∈ domain → p.2 ∈ domain → F p ≤ Bd) :
    ∫⁻ p in S, F p ∂((volume.restrict domain).prod (volume.restrict domain)) ≤
      Bd * (volume.prod volume) (S ∩ domain ×ˢ domain) := by
  rw [Measure.prod_restrict, Measure.restrict_restrict hS]
  calc ∫⁻ p in S ∩ domain ×ˢ domain, F p ∂(volume.prod volume)
      ≤ ∫⁻ _p in S ∩ domain ×ˢ domain, Bd ∂(volume.prod volume) :=
        setLIntegral_mono' (hS.inter (hD.prod hD)) fun p hp => hF p hp.1 hp.2.1 hp.2.2
    _ = Bd * (volume.prod volume) (S ∩ domain ×ˢ domain) := setLIntegral_const _ _

/-- The real arithmetic of (4.34), (4.37) and (4.38). -/
lemma p48o_secondMoment_arith {ε q ζ K A Cf N : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hζ : 0 ≤ ζ)
    (hK : 0 ≤ K) (hCf : 0 ≤ Cf) :
    N ^ 2 * (ε ^ (-(2 * ζ)) * K + A ^ 2) * (Real.pi * ((2 * ε ^ (q - 4 * ζ)) ^ 2 * Real.pi)) +
        N ^ 2 * (Cf * ε ^ ζ) * (Real.pi * Real.pi) ≤
      Real.pi ^ 2 * (4 * (K + A ^ 2) + Cf) * ε ^ GMS4.prop48RateAlpha q ζ * N ^ 2 := by
  have hsq : (2 * ε ^ (q - 4 * ζ)) ^ 2 = 4 * ε ^ (2 * q - 8 * ζ) := by
    rw [mul_pow, ← Real.rpow_natCast (ε ^ (q - 4 * ζ)), ← Real.rpow_mul hε.le]
    congr 1
    · norm_num
    · congr 1
      push_cast
      ring
  have hprod : ε ^ (-(2 * ζ)) * ε ^ (2 * q - 8 * ζ) = ε ^ (2 * q - 10 * ζ) := by
    rw [← Real.rpow_add hε]
    congr 1
    ring
  have h21 : ε ^ (2 * q - 8 * ζ) ≤ ε ^ (2 * q - 10 * ζ) :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
  have h1a : ε ^ (2 * q - 10 * ζ) ≤ ε ^ GMS4.prop48RateAlpha q ζ :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (min_le_left _ _)
  have hza : ε ^ ζ ≤ ε ^ GMS4.prop48RateAlpha q ζ :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (min_le_right _ _)
  have hA2 : 0 ≤ A ^ 2 := sq_nonneg A
  have hnear : (ε ^ (-(2 * ζ)) * K + A ^ 2) * (4 * ε ^ (2 * q - 8 * ζ)) ≤
      4 * (K + A ^ 2) * ε ^ GMS4.prop48RateAlpha q ζ := by
    have e : (ε ^ (-(2 * ζ)) * K + A ^ 2) * (4 * ε ^ (2 * q - 8 * ζ)) =
        4 * (K * ε ^ (2 * q - 10 * ζ) + A ^ 2 * ε ^ (2 * q - 8 * ζ)) := by
      rw [← hprod]; ring
    rw [e]
    have h1 : K * ε ^ (2 * q - 10 * ζ) ≤ K * ε ^ GMS4.prop48RateAlpha q ζ :=
      mul_le_mul_of_nonneg_left h1a hK
    have h2 : A ^ 2 * ε ^ (2 * q - 8 * ζ) ≤ A ^ 2 * ε ^ GMS4.prop48RateAlpha q ζ :=
      mul_le_mul_of_nonneg_left (h21.trans h1a) hA2
    nlinarith
  have hfar : Cf * ε ^ ζ ≤ Cf * ε ^ GMS4.prop48RateAlpha q ζ := mul_le_mul_of_nonneg_left hza hCf
  rw [hsq]
  have e : N ^ 2 * (ε ^ (-(2 * ζ)) * K + A ^ 2) * (Real.pi * (4 * ε ^ (2 * q - 8 * ζ) * Real.pi)) +
      N ^ 2 * (Cf * ε ^ ζ) * (Real.pi * Real.pi) =
      Real.pi ^ 2 * N ^ 2 * ((ε ^ (-(2 * ζ)) * K + A ^ 2) * (4 * ε ^ (2 * q - 8 * ζ)) +
        Cf * ε ^ ζ) := by ring
  rw [e]
  have e' : Real.pi ^ 2 * (4 * (K + A ^ 2) + Cf) * ε ^ GMS4.prop48RateAlpha q ζ * N ^ 2 =
      Real.pi ^ 2 * N ^ 2 * (4 * (K + A ^ 2) * ε ^ GMS4.prop48RateAlpha q ζ +
        Cf * ε ^ GMS4.prop48RateAlpha q ζ) := by ring
  rw [e']
  exact mul_le_mul_of_nonneg_left (add_le_add hnear hfar) (by positivity)

/-- **[18] (4.30)–(4.38), unconditional form, with the jointly measurable conditional mean.** For a
radius `ρ`, Lemma 4.9's moments (`H`), the mean bound `A` and the far-pair covariance bound give
`E[(∫_D f (X' − m))²] ≤ C ε^{min(2q−10ζ, ζ)} ‖f‖²_∞` for all small `ε` and all admissible tests. -/
theorem p48o_secondMoment_of_farPair
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {q ζ ρ : ℝ} (hζ : 0 ≤ ζ) (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (H : Lemma49ConditionalMoments D hγ q ζ ρ) {A : ℝ} (hA : 0 ≤ A)
    (hmeanA : ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) H.epsilonStar → ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      Integrable (maskedUStar D hγ ε q ζ z) P ∧ ∀ᵐ ω ∂P, conditionalMean D hγ ε q ζ ω z ≤ A)
    {Cf ε₀ : ℝ} (hCf : 0 ≤ Cf)
    (hfar : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ z ∈ ball (0 : ℂ) ρ, ∀ w ∈ ball (0 : ℂ) ρ,
      2 * ε ^ (q - 4 * ζ) < dist z w →
        ∫ ω, (maskedUStarPrime D hγ ε q ζ z ω - p48oCondMeanJoint D hγ ε q ζ ω z) *
          (maskedUStarPrime D hγ ε q ζ w ω - p48oCondMeanJoint D hγ ε q ζ ω w) ∂P ≤
            Cf * ε ^ ζ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioc (0 : ℝ) (min H.epsilonStar ε₀),
      ∀ (domain : Set ℂ) (f : ℂ → ℝ), GMS4.Prop48TestPairAdmissible ρ domain f →
        ∫⁻ ω, ENNReal.ofReal (p48oPrimedFluctuationJoint D hγ ε q ζ domain f ω ^ 2) ∂P ≤
          ENNReal.ofReal (C * ε ^ GMS4.prop48RateAlpha q ζ * GMS4.prop48TestSupNorm ρ f ^ 2) := by
  let _ := D.isProbabilityMeasure
  obtain ⟨K, hK, hpair⟩ := H.near_pair
  refine ⟨Real.pi ^ 2 * (4 * (K + A ^ 2) + Cf), by positivity, ?_⟩
  intro ε hε domain f hadm
  have hε1 : ε ∈ Ioc (0 : ℝ) H.epsilonStar := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have hε2 : ε ∈ Ioc (0 : ℝ) ε₀ := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  have hεle1 : ε ≤ 1 := hε1.2.trans H.epsilonStar_le_one
  have hmean := hmeanA ε hε1
  set N := GMS4.prop48TestSupNorm ρ f with hN
  set r : ℝ := 2 * ε ^ (q - 4 * ζ) with hr
  set a : Ω → ℂ → ℝ := p48oCentredJoint D hγ ε q ζ ρ f with ha
  have htriple := p48o_integrable_pairKernel D hγ H hK hpair hA hε1 hmean hadm
  have hsquare := GMS4.prop48_square_integrable_of_triple (μ := volume.restrict domain) a htriple
  have hS : MeasurableSet {p : ℂ × ℂ | dist p.1 p.2 ≤ r} :=
    measurableSet_le (measurable_fst.dist measurable_snd) measurable_const
  have hsplit := GMS4.prop48_secondMoment_near_far_positive_split
    (μ := volume.restrict domain) a _ hS htriple hsquare
  have hlhs : ∫⁻ ω, ENNReal.ofReal (p48oPrimedFluctuationJoint D hγ ε q ζ domain f ω ^ 2) ∂P =
      ∫⁻ ω, ENNReal.ofReal ((∫ z, a ω z ∂(volume.restrict domain)) ^ (2 : ℕ)) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [p48o_ae_primedFluctuationJoint_eq D hγ ε q ζ hadm] with ω h
    rw [h]
  -- near pairs
  have hnear : ∫⁻ p in {p : ℂ × ℂ | dist p.1 p.2 ≤ r},
      ENNReal.ofReal (∫ ω, a ω p.1 * a ω p.2 ∂P)
        ∂((volume.restrict domain).prod (volume.restrict domain)) ≤
      ENNReal.ofReal (N ^ 2 * (ε ^ (-(2 * ζ)) * K + A ^ 2)) *
        (volume domain * (ENNReal.ofReal r ^ 2 * (NNReal.pi : ℝ≥0∞))) := by
    refine (p48o_setLIntegral_prod_restrict_le hadm.domain_borel hS
      (fun p _ h1 h2 => p48o_ofReal_integral_centred_near_le D hγ H hK hpair hA hε1 hmean hadm
        (hadm.domain_subset_ball h1) (hadm.domain_subset_ball h2))).trans ?_
    gcongr
    have hset : {p : ℂ × ℂ | dist p.1 p.2 ≤ r} ∩ domain ×ˢ domain =
        {p : ℂ × ℂ | p.1 ∈ domain ∧ p.2 ∈ domain ∧ dist p.1 p.2 ≤ r} := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_prod]
      tauto
    rw [hset]
    exact GMS4.prop48_nearPair_volume_le domain hadm.domain_borel r
  -- far pairs
  have hfarI : ∫⁻ p in {p : ℂ × ℂ | dist p.1 p.2 ≤ r}ᶜ,
      ENNReal.ofReal (∫ ω, a ω p.1 * a ω p.2 ∂P)
        ∂((volume.restrict domain).prod (volume.restrict domain)) ≤
      ENNReal.ofReal (N ^ 2 * (Cf * ε ^ ζ)) * (volume domain * volume domain) := by
    refine (p48o_setLIntegral_prod_restrict_le hadm.domain_borel hS.compl
      (fun p hp h1 h2 => p48o_ofReal_integral_centred_far_le D hγ hCf hε.1.le
        (hfar ε hε2) hadm (hadm.domain_subset_ball h1) (hadm.domain_subset_ball h2)
        (lt_of_not_ge hp))).trans ?_
    gcongr
    calc (volume.prod volume) ({p : ℂ × ℂ | dist p.1 p.2 ≤ r}ᶜ ∩ domain ×ˢ domain)
        ≤ (volume.prod volume) (domain ×ˢ domain) := measure_mono Set.inter_subset_right
      _ = volume domain * volume domain := Measure.prod_prod _ _
  have hvol : volume domain ≤ ENNReal.ofReal Real.pi := p48o_volume_le_pi hadm hρ.2.le
  have hpi : (NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  have hr0 : 0 ≤ r := mul_nonneg (by norm_num) (Real.rpow_nonneg hε.1.le _)
  rw [hlhs]
  calc ∫⁻ ω, ENNReal.ofReal ((∫ z, a ω z ∂(volume.restrict domain)) ^ (2 : ℕ)) ∂P
      ≤ _ := hsplit
    _ ≤ ENNReal.ofReal (N ^ 2 * (ε ^ (-(2 * ζ)) * K + A ^ 2)) *
          (volume domain * (ENNReal.ofReal r ^ 2 * (NNReal.pi : ℝ≥0∞))) +
        ENNReal.ofReal (N ^ 2 * (Cf * ε ^ ζ)) * (volume domain * volume domain) :=
        add_le_add hnear hfarI
    _ ≤ ENNReal.ofReal (N ^ 2 * (ε ^ (-(2 * ζ)) * K + A ^ 2)) *
          (ENNReal.ofReal Real.pi * (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi)) +
        ENNReal.ofReal (N ^ 2 * (Cf * ε ^ ζ)) *
          (ENNReal.ofReal Real.pi * ENNReal.ofReal Real.pi) := by
        rw [hpi]
        gcongr
    _ = ENNReal.ofReal (N ^ 2 * (ε ^ (-(2 * ζ)) * K + A ^ 2) *
          (Real.pi * (r ^ 2 * Real.pi)) + N ^ 2 * (Cf * ε ^ ζ) * (Real.pi * Real.pi)) := by
        have h1 : 0 ≤ N ^ 2 * (ε ^ (-(2 * ζ)) * K + A ^ 2) :=
          mul_nonneg (sq_nonneg _) (add_nonneg (mul_nonneg (Real.rpow_nonneg hε.1.le _) hK)
            (sq_nonneg _))
        have h2 : 0 ≤ N ^ 2 * (Cf * ε ^ ζ) :=
          mul_nonneg (sq_nonneg _) (mul_nonneg hCf (Real.rpow_nonneg hε.1.le _))
        rw [← ENNReal.ofReal_pow hr0, ← ENNReal.ofReal_mul (sq_nonneg r),
          ← ENNReal.ofReal_mul Real.pi_pos.le, ← ENNReal.ofReal_mul h1,
          ← ENNReal.ofReal_mul Real.pi_pos.le, ← ENNReal.ofReal_mul h2,
          ← ENNReal.ofReal_add (mul_nonneg h1 (by positivity)) (mul_nonneg h2 (by positivity))]
    _ ≤ ENNReal.ofReal (Real.pi ^ 2 * (4 * (K + A ^ 2) + Cf) * ε ^ GMS4.prop48RateAlpha q ζ *
          N ^ 2) :=
        ENNReal.ofReal_le_ofReal (p48o_secondMoment_arith hε.1 hεle1 hζ hK hCf)

end MatedCRTHarmonic.GMS4O
