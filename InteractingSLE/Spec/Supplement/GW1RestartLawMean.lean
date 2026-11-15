/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1RestartLawStopped
import InteractingSLE.Spec.Supplement.SB4SewLawK2

/-!
# BW1: the physical Gaussian law from marked locality and the active mean

This is the stopped counterpart of the Gaussian step inside the sewn-flow K2
bridge. The only field-identification input is an equality of conditional means;
marked locality supplies the covariance and the characteristic functional.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW1RestartLaw

open LocalSets

/-- A marked terminal or retargeting mean determines the whole physical Gaussian
kernel off the retained union. No separate covariance or kernel premise is needed. -/
theorem ae_physical_kernel_of_activeMean
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    {𝓜 : ℝ≥0 → MeasurableSpace Ω} (h𝓜 : ∀ q, 𝓜 q ≤ mΩ)
    {F : Set Ω} (hF : ∀ q, MeasurableSet[𝓜 q] F) {V : Ω → ℝ≥0∞}
    (hV : ∀ q : ℝ≥0, MeasurableSet[𝓜 q] {ω | (q : ℝ≥0∞) < V ω})
    {A : ℝ≥0 → Ω → Set ℂ} (hAm : ∀ q, Measurable[𝓜 q, hittingSigma] (A q))
    (hAc : ∀ q ω, A q ω ⊆ H ∧ IsOpen (H \ A q ω))
    (hloc : ∀ q, WholeField.IsHistoryAvoidanceLocal
      (𝓜 q) (A q) (WholeField.centredField h u₀) P)
    {M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens} (hM : ∀ q, Measurable[𝓜 q] (M q))
    (hgm : SB.SewLaw.HasActiveGermMean P 𝓜 A h u₀ F V M) :
    ∀ (q : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
      ω ∈ F → (q : ℝ≥0∞) < V ω → tsupport φ ⊆ H \ A q ω →
      P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | 𝓜 q] ω =
        Complex.exp (Complex.I * (M q ω φ : ℂ) -
          (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov (H \ A q ω) φ φ : ℝ) : ℂ)) := by
  intro q φ
  let D := {ω | ω ∈ F ∧ (q : ℝ≥0∞) < V ω ∧
    Disjoint (tsupport φ) (relClosureH (A q ω))}
  have hD : MeasurableSet[𝓜 q] D := (hF q).inter ((hV q).inter
    ((measurableSet_disjoint_relClosureH φ.hasCompactSupport.isCompact
      φ.tsupport_subset).preimage (hAm q)))
  have he := SB.SewLaw.ae_retained_physical_cexp_of_mean ⟨𝓜 q, h𝓜 q⟩ hu₀ hh0
    (hAm q) (hloc q) (Eventually.of_forall (hAc q)) φ hD
    ((LQGMetric.measurable_distOn_apply φ).comp (hM q))
    ((hgm q φ).mono fun ω hω hωD => hω hωD.1 hωD.2.1
      (fun z hz => ⟨φ.tsupport_subset hz, fun hzA =>
        Set.disjoint_left.1 hωD.2.2 hz
          ((relClosureH_eq (hAc q ω).1 (hAc q ω).2).symm ▸ hzA)⟩))
  filter_upwards [he] with ω heω hω hq hφ
  apply heω
  refine ⟨hω, hq, ?_⟩
  rw [relClosureH_eq (hAc q ω).1 (hAc q ω).2]
  exact Set.disjoint_left.2 fun z hz hzA => (hφ hz).2 hzA

end InteractingSLE.Theorem14.GW1RestartLaw
