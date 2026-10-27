import MatedCRTHarmonic.GMS4.Prop48

/-!
# Near-pair geometry for [18] Proposition 4.8

The spatial part of (4.34) bounds the area of pairs of test points within a
fixed distance by the test-domain area times the area of one planar ball.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4

/-- The geometric Fubini bound behind [18] (4.34). -/
theorem prop48_nearPair_volume_le (D : Set ℂ) (hD : MeasurableSet D)
    (r : ℝ) :
    (volume.prod volume) {p : ℂ × ℂ | p.1 ∈ D ∧ p.2 ∈ D ∧ dist p.1 p.2 ≤ r} ≤
      volume D * (ENNReal.ofReal r ^ 2 * (NNReal.pi : ENNReal)) := by
  let S : Set (ℂ × ℂ) := {p | p.1 ∈ D ∧ p.2 ∈ D ∧ dist p.1 p.2 ≤ r}
  have hS : MeasurableSet S := by
    have h1 : MeasurableSet {p : ℂ × ℂ | p.1 ∈ D} := hD.preimage measurable_fst
    have h2 : MeasurableSet {p : ℂ × ℂ | p.2 ∈ D} := hD.preimage measurable_snd
    have h3 : MeasurableSet {p : ℂ × ℂ | dist p.1 p.2 ≤ r} :=
      measurableSet_le (measurable_fst.dist measurable_snd) measurable_const
    simpa only [S, Set.ofPred_and] using h1.inter (h2.inter h3)
  have hsection : ∀ z : ℂ, volume (Prod.mk z ⁻¹' S) ≤
      D.indicator (fun _ => ENNReal.ofReal r ^ 2 * (NNReal.pi : ENNReal)) z := by
    intro z
    by_cases hz : z ∈ D
    · simp only [Set.indicator_of_mem hz]
      have hsubset : Prod.mk z ⁻¹' S ⊆ closedBall z r := by
        intro w hw
        simpa only [mem_closedBall, dist_comm] using hw.2.2
      calc
        volume (Prod.mk z ⁻¹' S) ≤ volume (closedBall z r) := measure_mono hsubset
        _ = ENNReal.ofReal r ^ 2 * (NNReal.pi : ENNReal) := Complex.volume_closedBall z r
    · have hempty : Prod.mk z ⁻¹' S = ∅ := by
        ext w
        simp [S, hz]
      simp [Set.indicator_of_notMem hz, hempty]
  change (volume.prod volume) S ≤ _
  rw [Measure.prod_apply hS]
  calc
    (∫⁻ z, volume (Prod.mk z ⁻¹' S) ∂volume) ≤
        ∫⁻ z, D.indicator (fun _ => ENNReal.ofReal r ^ 2 * (NNReal.pi : ENNReal)) z ∂volume :=
      lintegral_mono hsection
    _ = volume D * (ENNReal.ofReal r ^ 2 * (NNReal.pi : ENNReal)) := by
      rw [lintegral_indicator_const hD, mul_comm]

/-- Integrate a pointwise near-pair bound over the region in (4.31). -/
theorem prop48_nearPair_lintegral_le (D : Set ℂ) (hD : MeasurableSet D)
    (r : ℝ) (B : ℝ≥0∞) (F : ℂ × ℂ → ℝ≥0∞)
    (hF : ∀ z ∈ D, ∀ w ∈ D, dist z w ≤ r → F (z, w) ≤ B) :
    (∫⁻ p in {p : ℂ × ℂ | p.1 ∈ D ∧ p.2 ∈ D ∧ dist p.1 p.2 ≤ r},
      F p ∂(volume.prod volume)) ≤
        B * (volume D * (ENNReal.ofReal r ^ 2 * (NNReal.pi : ENNReal))) := by
  let S : Set (ℂ × ℂ) := {p | p.1 ∈ D ∧ p.2 ∈ D ∧ dist p.1 p.2 ≤ r}
  have hpoint : ∀ p ∈ S, F p ≤ B := by
    intro p hp
    exact hF p.1 hp.1 p.2 hp.2.1 hp.2.2
  change (∫⁻ p in S, F p ∂(volume.prod volume)) ≤ _
  calc
    (∫⁻ p in S, F p ∂(volume.prod volume)) ≤
        ∫⁻ _p in S, B ∂(volume.prod volume) :=
      setLIntegral_mono' (by
        have h1 : MeasurableSet {p : ℂ × ℂ | p.1 ∈ D} := hD.preimage measurable_fst
        have h2 : MeasurableSet {p : ℂ × ℂ | p.2 ∈ D} := hD.preimage measurable_snd
        have h3 : MeasurableSet {p : ℂ × ℂ | dist p.1 p.2 ≤ r} :=
          measurableSet_le (measurable_fst.dist measurable_snd) measurable_const
        simpa only [S, Set.ofPred_and] using h1.inter (h2.inter h3)) hpoint
    _ = B * (volume.prod volume) S := setLIntegral_const S B
    _ ≤ B * (volume D * (ENNReal.ofReal r ^ 2 * (NNReal.pi : ENNReal))) := by
      exact mul_le_mul' le_rfl (prop48_nearPair_volume_le D hD r)

/-- The concrete (4.33) bound integrated over (4.31)'s near region. Its only
probabilistic premise is the uniform second moment of the masked area ratio
from (4.24); the degree cap and Cauchy–Schwarz are already proved. -/
theorem prop48_zeroCone_masked_near_pair_lintegral_le
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (C : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (ε q ζ : ℝ) (hε : 0 ≤ ε) (D : Set ℂ) (hD : MeasurableSet D)
    (K : ℝ≥0∞)
    (hK : ∀ z ∈ D,
      ∫⁻ ω, prop48ZeroConeMaskedAreaRatio γ X₀ hIG₀ B₀ B₀' η₀ ε q ζ z ω ^
        (2 : ℝ) ∂P ≤ K) :
    (∫⁻ p in {p : ℂ × ℂ | p.1 ∈ D ∧ p.2 ∈ D ∧
        dist p.1 p.2 ≤ 2 * ε ^ (q - 4 * ζ)},
      (∫⁻ ω, prop48ZeroConeMaskedUStar γ X₀ hIG₀ B₀ B₀' η₀ ε q ζ p.1 ω *
        prop48ZeroConeMaskedUStar γ X₀ hIG₀ B₀ B₀' η₀ ε q ζ p.2 ω ∂P)
        ∂(volume.prod volume)) ≤
      (ENNReal.ofReal (ε ^ (-ζ)) ^ 2 *
        (K ^ (1 / (2 : ℝ)) * K ^ (1 / (2 : ℝ)))) *
        (volume D * (ENNReal.ofReal (2 * ε ^ (q - 4 * ζ)) ^ 2 *
          (NNReal.pi : ENNReal))) := by
  apply prop48_nearPair_lintegral_le D hD _ _ _
  intro z hz w hw _
  exact prop48_zeroCone_masked_pair_lintegral_le C ε q ζ hε z w K (hK z hz) (hK w hw)

/-- The geometric integration step (4.37) for an off-diagonal pointwise bound. -/
theorem prop48_farPair_lintegral_le (D : Set ℂ) (hD : MeasurableSet D)
    (r : ℝ) (B : ℝ≥0∞) (F : ℂ × ℂ → ℝ≥0∞)
    (hF : ∀ z ∈ D, ∀ w ∈ D, r < dist z w → F (z, w) ≤ B) :
    (∫⁻ p in {p : ℂ × ℂ | p.1 ∈ D ∧ p.2 ∈ D ∧ r < dist p.1 p.2},
      F p ∂(volume.prod volume)) ≤ B * (volume D * volume D) := by
  let S : Set (ℂ × ℂ) := {p | p.1 ∈ D ∧ p.2 ∈ D ∧ r < dist p.1 p.2}
  have hS : MeasurableSet S := by
    have h1 : MeasurableSet {p : ℂ × ℂ | p.1 ∈ D} := hD.preimage measurable_fst
    have h2 : MeasurableSet {p : ℂ × ℂ | p.2 ∈ D} := hD.preimage measurable_snd
    have h3 : MeasurableSet {p : ℂ × ℂ | r < dist p.1 p.2} :=
      measurableSet_lt measurable_const (measurable_fst.dist measurable_snd)
    simpa only [S, Set.ofPred_and] using h1.inter (h2.inter h3)
  have hsubset : S ⊆ D ×ˢ D := by
    intro p hp
    exact ⟨hp.1, hp.2.1⟩
  have hpoint : ∀ p ∈ S, F p ≤ B := by
    intro p hp
    exact hF p.1 hp.1 p.2 hp.2.1 hp.2.2
  change (∫⁻ p in S, F p ∂(volume.prod volume)) ≤ _
  calc
    (∫⁻ p in S, F p ∂(volume.prod volume)) ≤
        ∫⁻ _p in S, B ∂(volume.prod volume) := setLIntegral_mono' hS hpoint
    _ = B * (volume.prod volume) S := setLIntegral_const S B
    _ ≤ B * (volume.prod volume) (D ×ˢ D) :=
      mul_le_mul' le_rfl (measure_mono hsubset)
    _ = B * (volume D * volume D) := by rw [Measure.prod_prod]

end MatedCRTHarmonic.GMS4

