/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2RealizeTypes
import InteractingSLE.Spec.Sec6.Prop65Gauss
import InteractingSLE.Spec.Supplement.GW1

/-!
# Seed, Gaussian integrability and lifetime transfer for first-contact K2

These lemmas discharge the analytic adapters. The source Gaussian law, incident
height inequalities, and collision identity remain mathematical inputs.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb
open DomainMarkov DomainMarkov.K2
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

omit mΩ in
/-- Aux. 78's two exposed-side alternatives are admissible for both paths. The
original-real-boundary alternatives require their separate source argument. -/
theorem firstContact_exposedSides_admissible {κ θ₁ θ₂ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂ + Real.pi) :
    ExplState.IsAdmissibleSeed κ (-sleLambda κ - θ₂ * QuantumZipper.chiC κ)
        (sleLambda κ - θ₁ * QuantumZipper.chiC κ) θ₁ ∧
      ExplState.IsAdmissibleSeed κ (-sleLambda κ - θ₂ * QuantumZipper.chiC κ)
        (sleLambda κ - θ₁ * QuantumZipper.chiC κ) θ₂ := by
  have hLambda := Sec4.sleLambda_pos hκ
  have hChi := Sec4.chiC_pos hκ hκ4
  have hd : (θ₁ - θ₂) * QuantumZipper.chiC κ < Real.pi * QuantumZipper.chiC κ :=
    mul_lt_mul_of_pos_right (by linarith) hChi
  have hp : Real.pi * QuantumZipper.chiC κ < 2 * sleLambda κ := by
    rw [Sec4.pi_mul_chiC hκ]
    nlinarith [mul_pos hκ hLambda]
  unfold ExplState.IsAdmissibleSeed
  constructor <;> constructor <;> nlinarith

/-- Admissibility of the two incident heights is precisely the required seed
condition, for every fixed-type reading of the same word. -/
theorem not_threshold_type_of_admissible {κ θ : ℝ} (hκ : 0 < κ)
    {c : BoundaryWord} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hc : c ∈ FCDet.typeSet κ θ nL nR ρL ρR)
    (ha : ExplState.IsAdmissibleSeed κ
      (PiecewiseConstantBoundaryData.leftLim c.fn 0)
      (PiecewiseConstantBoundaryData.rightLim c.fn 0) θ) :
    ¬ ForceWord.ThresholdCondition ρL ρR 0
      (FCDet.typeXL κ θ nL nR ρL ρR c) (FCDet.typeXR κ θ nL nR ρL ρR c) := by
  obtain ⟨eL, eR, hxL, hxR, hρL, hρR⟩ := FCDet.isFlowType_of_mem_typeSet hc
  subst nL nR
  change FCDet.typeXL κ θ _ _ ρL ρR c = flowLineXL c.fn c.jumps 0 at hxL
  change FCDet.typeXR κ θ _ _ ρL ρR c = flowLineXR c.fn c.jumps 0 at hxR
  change ρL = flowLineRhoL κ c.fn c.jumps 0 θ at hρL
  change ρR = flowLineRhoR κ c.fn c.jumps 0 θ at hρR
  rw [hxL, hxR, hρL, hρR]
  intro ht
  exact ((Theorem14.GW1.thresholdCondition_flowLine_zero_iff hκ c.fn c.jumps θ).1 ht) ha

/-- A bounded conditional Gaussian mean gives integrability of the original
observable, by the landed conditional Gaussian first-moment theorem. -/
theorem integrable_of_condGaussian_bounded_mean [IsProbabilityMeasure P]
    {𝒢 : MeasurableSpace Ω} {X μ V : Ω → ℝ} {K C : ℝ}
    (hg : @Sec6.Prop65.IsCondGaussian Ω 𝒢 mΩ P X μ V K) (hμ : ∀ ω, ‖μ ω‖ ≤ C) :
    Integrable X P := by
  let _ : MeasurableSpace Ω := mΩ
  have hc : Integrable (fun ω => X ω - μ ω) P := by
    simpa only [pow_one] using hg.integrable_pow 1
  have hm : Integrable μ P := Integrable.of_bound hg.measurable_mean'.aestronglyMeasurable C
    (ae_of_all P hμ)
  exact (hc.add hm).congr (ae_of_all P fun ω => sub_add_cancel (X ω) (μ ω))

/-- Apply the previous result to a branch-clamped pairing. Its law is Gaussian
on the branch and degenerate at zero off it. -/
theorem integrable_restrict_of_condGaussian_indicator [IsProbabilityMeasure P]
    {𝒢 : MeasurableSpace Ω} {B : Set Ω} (hB : MeasurableSet[mΩ] B)
    {X μ V : Ω → ℝ} {K C : ℝ}
    (hg : @Sec6.Prop65.IsCondGaussian Ω 𝒢 mΩ P (B.indicator X) μ V K)
    (hμ : ∀ ω, ‖μ ω‖ ≤ C) : Integrable X (P.restrict B) := by
  let _ : MeasurableSpace Ω := mΩ
  exact (integrable_indicator_iff (f := X) (μ := P) hB).1
    (integrable_of_condGaussian_bounded_mean hg hμ)

variable {𝓕 : Filtration ℝ≥0 mΩ} {F B : Set Ω} {U V : Ω → ℝ≥0∞}
  {W : ℝ≥0 → Ω → ℝ} {X : Ω → DistOn upperHalfPlaneOpens}
  {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}

/-- Safe Gaussian identities restrict to smaller live events and transfer
across an almost-sure lifetime equality only on that smaller event. -/
theorem hasSafeLaw_of_subset_ae_lifetime (hBF : B ⊆ F)
    (he : ∀ᵐ ω ∂P, ω ∈ B → U ω = V ω)
    (hl : HasSafeLaw κ ρL ρR P 𝓕 F U W VL VR X) :
    HasSafeLaw κ ρL ρR P 𝓕 B V W VL VR X := by
  intro ψ q D hD hsafe
  apply hl ψ q D hD
  filter_upwards [hsafe, he] with ω hs heω hω
  obtain ⟨hB, havoid⟩ := hs hω
  refine ⟨hBF hB, ?_⟩
  exact ⟨by rw [heω hB]; exact havoid.1, havoid.2⟩

/-- The member identities have the same branch and lifetime invariance. No
completion or standard Borel assumption on the source space is needed. -/
theorem hasSafeMembers_of_subset_ae_lifetime (hBF : B ⊆ F)
    (he : ∀ᵐ ω ∂P, ω ∈ B → U ω = V ω)
    (hl : HasSafeMembers P 𝓕 F U W X) :
    HasSafeMembers P 𝓕 B V W X := by
  intro s Fb hFb D hD hsafe
  apply hl s Fb hFb D hD
  filter_upwards [hsafe, he] with ω hs heω hω
  obtain ⟨hB, hlt, hd⟩ := hs hω
  exact ⟨hBF hB, by rwa [heω hB], hd⟩

end InteractingSLE.Restart.FCPlumb
