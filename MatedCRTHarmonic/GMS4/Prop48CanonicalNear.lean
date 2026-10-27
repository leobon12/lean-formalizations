import MatedCRTHarmonic.GMS4.Prop48CanonicalMoments
import MatedCRTHarmonic.GMS4.Prop48PrimedIntegral
import MatedCRTHarmonic.GMS4O.Prop48OCondMean
import MatedCRTHarmonic.GMS4.Prop48NearMeasure

/-!
# Near pairs for the canonical Proposition 4.8 observable

The local event includes the actual IG phase. Its degree cap and the
authorized Lemma 4.9 area moment give the near-pair estimate (4.32)--(4.34).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4.Canonical

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The pointwise algebra in [18] (4.32): the two mixed terms in the
centered product are nonpositive for nonnegative variables. -/
theorem prop48_centered_near_pair_le (x y mx my : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hmx : 0 ≤ mx) (hmy : 0 ≤ my) :
    (x - mx) * (y - my) ≤ x * y + mx * my := by
  nlinarith [mul_nonneg hx hmy, mul_nonneg hmx hy]

/-- Pointwise near-pair control with the literal phase-aware event. -/
theorem Lemma49ConditionalMoments.near_pair
    {D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm}
    {hγ : γ ∈ Ioo (0 : ℝ) 2} {q ζ ρ : ℝ}
    (H : Lemma49ConditionalMoments D hγ q ζ ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) H.epsilonStar →
      ∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ w ∈ Metric.ball (0 : ℂ) ρ,
        (∫⁻ ω, ENNReal.ofReal (maskedUStar D hγ ε q ζ z ω) *
          ENNReal.ofReal (maskedUStar D hγ ε q ζ w ω) ∂P) ≤
            ENNReal.ofReal (ε ^ (-ζ)) ^ 2 *
              (ENNReal.ofReal K ^ (1 / (2 : ℝ)) *
                ENNReal.ofReal K ^ (1 / (2 : ℝ))) := by
  obtain ⟨K, hK, hbound⟩ := H.area_lintegral_le 2 (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro ε hε z hz w hw
  let c : ℝ≥0∞ := ENNReal.ofReal (ε ^ (-ζ))
  let A : ℂ → Ω → ℝ≥0∞ :=
    fun x ω => ENNReal.ofReal (maskedAreaRatio D hγ ε q ζ x ω)
  let V : ℂ → Ω → ℝ≥0∞ :=
    fun x ω => ENNReal.ofReal (maskedUStar D hγ ε q ζ x ω)
  have hAz : AEMeasurable (A z) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (aemeasurable_maskedAreaRatio D hγ hε.1.le q ζ z)
  have hAw : AEMeasurable (A w) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (aemeasurable_maskedAreaRatio D hγ hε.1.le q ζ w)
  have hle : ∀ x ω, V x ω ≤ c * A x ω := by
    intro x ω
    change ENNReal.ofReal (maskedUStar D hγ ε q ζ x ω) ≤
      ENNReal.ofReal (ε ^ (-ζ)) *
        ENNReal.ofReal (maskedAreaRatio D hγ ε q ζ x ω)
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hε.1.le _)]
    exact ENNReal.ofReal_le_ofReal (maskedUStar_le_areaRatio D hγ ε q ζ hε.1.le x ω)
  have hpoint : ∀ ω, V z ω * V w ω ≤ c ^ 2 * (A z ω * A w ω) := by
    intro ω
    calc
      V z ω * V w ω ≤ (c * A z ω) * (c * A w ω) :=
        mul_le_mul' (hle z ω) (hle w ω)
      _ = c ^ 2 * (A z ω * A w ω) := by ring
  have hholder : (∫⁻ ω, A z ω * A w ω ∂P) ≤
      (∫⁻ ω, A z ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) *
        (∫⁻ ω, A w ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq P
      (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩) hAz hAw
  have hboundz : (∫⁻ ω, A z ω ^ (2 : ℝ) ∂P) ≤ ENNReal.ofReal K :=
    calc
      _ = ∫⁻ ω, ENNReal.ofReal |maskedAreaRatio D hγ ε q ζ z ω| ^ (2 : ℝ) ∂P := by
        congr 1
        funext ω
        rw [abs_of_nonneg (maskedAreaRatio_nonneg D hγ ε q ζ z ω)]
      _ ≤ _ := hbound ε hε z hz
  have hboundw : (∫⁻ ω, A w ω ^ (2 : ℝ) ∂P) ≤ ENNReal.ofReal K :=
    calc
      _ = ∫⁻ ω, ENNReal.ofReal |maskedAreaRatio D hγ ε q ζ w ω| ^ (2 : ℝ) ∂P := by
        congr 1
        funext ω
        rw [abs_of_nonneg (maskedAreaRatio_nonneg D hγ ε q ζ w ω)]
      _ ≤ _ := hbound ε hε w hw
  calc
    (∫⁻ ω, V z ω * V w ω ∂P) ≤
        ∫⁻ ω, c ^ 2 * (A z ω * A w ω) ∂P := lintegral_mono hpoint
    _ = c ^ 2 * ∫⁻ ω, A z ω * A w ω ∂P := by
      exact lintegral_const_mul'' (c ^ 2) (hAz.mul hAw)
    _ ≤ c ^ 2 *
        ((∫⁻ ω, A z ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) *
          (∫⁻ ω, A w ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ))) :=
      mul_le_mul' le_rfl hholder
    _ ≤ c ^ 2 * (ENNReal.ofReal K ^ (1 / (2 : ℝ)) *
          ENNReal.ofReal K ^ (1 / (2 : ℝ))) := by
      gcongr

/-- The near-pair Fubini estimate (4.34) on the canonical centre disk. -/
theorem Lemma49ConditionalMoments.near_pair_integrated
    {D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm}
    {hγ : γ ∈ Ioo (0 : ℝ) 2} {q ζ ρ : ℝ}
    (H : Lemma49ConditionalMoments D hγ q ζ ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) H.epsilonStar →
      (∫⁻ p in {p : ℂ × ℂ | p.1 ∈ Metric.ball (0 : ℂ) ρ ∧
        p.2 ∈ Metric.ball (0 : ℂ) ρ ∧
        dist p.1 p.2 ≤ 2 * ε ^ (q - 4 * ζ)},
        (∫⁻ ω, ENNReal.ofReal (maskedUStar D hγ ε q ζ p.1 ω) *
          ENNReal.ofReal (maskedUStar D hγ ε q ζ p.2 ω) ∂P)
        ∂(volume.prod volume)) ≤
        (ENNReal.ofReal (ε ^ (-ζ)) ^ 2 *
          (ENNReal.ofReal K ^ (1 / (2 : ℝ)) *
            ENNReal.ofReal K ^ (1 / (2 : ℝ)))) *
          (volume (Metric.ball (0 : ℂ) ρ) *
            (ENNReal.ofReal (2 * ε ^ (q - 4 * ζ)) ^ 2 *
              (NNReal.pi : ℝ≥0∞))) := by
  obtain ⟨K, hK, hpair⟩ := H.near_pair
  refine ⟨K, hK, ?_⟩
  intro ε hε
  apply GMS4.prop48_nearPair_lintegral_le
    (Metric.ball (0 : ℂ) ρ) Metric.isOpen_ball.measurableSet
  intro z hz w hw _
  exact hpair ε hε z hz w hw

/-- Lemma 4.9's near-pair bound holds for the all-visit local variable at
every fixed pair of centres, since a deterministic point is visited once
almost surely. This is the pair kernel used by the local Borel factor. -/
theorem Lemma49ConditionalMoments.near_pair_prime
    {D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm}
    {hγ : γ ∈ Ioo (0 : ℝ) 2} {q ζ ρ : ℝ}
    (H : Lemma49ConditionalMoments D hγ q ζ ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) H.epsilonStar →
      ∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ w ∈ Metric.ball (0 : ℂ) ρ,
        (∫⁻ ω, ENNReal.ofReal (maskedUStarPrime D hγ ε q ζ z ω) *
          ENNReal.ofReal (maskedUStarPrime D hγ ε q ζ w ω) ∂P) ≤
            ENNReal.ofReal (ε ^ (-ζ)) ^ 2 *
              (ENNReal.ofReal K ^ (1 / (2 : ℝ)) *
                ENNReal.ofReal K ^ (1 / (2 : ℝ))) := by
  obtain ⟨K, hK, hb⟩ := H.near_pair
  refine ⟨K, hK, ?_⟩
  intro ε hε z hz w hw
  have hzEq := ae_maskedUStarPrime_eq_masked_fixed D hγ ε q ζ z
  have hwEq := ae_maskedUStarPrime_eq_masked_fixed D hγ ε q ζ w
  have heq : (∫⁻ ω, ENNReal.ofReal (maskedUStarPrime D hγ ε q ζ z ω) *
      ENNReal.ofReal (maskedUStarPrime D hγ ε q ζ w ω) ∂P) =
      ∫⁻ ω, ENNReal.ofReal (maskedUStar D hγ ε q ζ z ω) *
        ENNReal.ofReal (maskedUStar D hγ ε q ζ w ω) ∂P := by
    apply lintegral_congr_ae
    filter_upwards [hzEq, hwEq] with ω h1 h2
    rw [h1, h2]
  rw [heq]
  exact hb ε hε z hz w hw

/-- The centered near-pair kernel is bounded by the uncentered all-visit
product plus the square of the uniform conditional-mean bound. -/
theorem prop48_centered_near_pair_ae_le
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {ε q ζ ρ A : ℝ} (hε : 0 ≤ ε) (hA : 0 ≤ A)
    (hmean : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      Integrable (maskedUStar D hγ ε q ζ z) P ∧
        ∀ᵐ ω ∂P, conditionalMean D hγ ε q ζ ω z ≤ A)
    {z w : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) ρ)
    (hw : w ∈ Metric.ball (0 : ℂ) ρ) :
    ∀ᵐ ω ∂P,
      (maskedUStarPrime D hγ ε q ζ z ω -
        GMS4O.p48oCondMeanJoint D hγ ε q ζ ω z) *
      (maskedUStarPrime D hγ ε q ζ w ω -
        GMS4O.p48oCondMeanJoint D hγ ε q ζ ω w) ≤
      maskedUStarPrime D hγ ε q ζ z ω *
        maskedUStarPrime D hγ ε q ζ w ω + A ^ 2 := by
  have hzm := GMS4O.p48o_condMeanJoint_le_of_mean D hγ hε hmean z hz
  have hwm := GMS4O.p48o_condMeanJoint_le_of_mean D hγ hε hmean w hw
  filter_upwards [ae_maskedUStarPrime_eq_masked_fixed D hγ ε q ζ z,
    ae_maskedUStarPrime_eq_masked_fixed D hγ ε q ζ w,
    hzm, hwm] with ω hzEq hwEq hzmω hwmω
  have hz0 : 0 ≤ maskedUStarPrime D hγ ε q ζ z ω := by
    rw [hzEq]
    exact maskedUStar_nonneg D hγ ε q ζ z ω
  have hw0 : 0 ≤ maskedUStarPrime D hγ ε q ζ w ω := by
    rw [hwEq]
    exact maskedUStar_nonneg D hγ ε q ζ w ω
  have hmz0 := GMS4O.p48oCondMeanJoint_nonneg D hγ ε q ζ ω z
  have hmw0 := GMS4O.p48oCondMeanJoint_nonneg D hγ ε q ζ ω w
  have hpair := prop48_centered_near_pair_le
    (maskedUStarPrime D hγ ε q ζ z ω)
    (maskedUStarPrime D hγ ε q ζ w ω)
    (GMS4O.p48oCondMeanJoint D hγ ε q ζ ω z)
    (GMS4O.p48oCondMeanJoint D hγ ε q ζ ω w)
    hz0 hw0 hmz0 hmw0
  have hmprod : GMS4O.p48oCondMeanJoint D hγ ε q ζ ω z *
      GMS4O.p48oCondMeanJoint D hγ ε q ζ ω w ≤ A ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hzmω) hmw0,
      mul_nonneg hA (sub_nonneg.mpr hwmω)]
  linarith

end MatedCRTHarmonic.GMS4.Canonical

