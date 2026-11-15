/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4SewLawMean
import InteractingSLE.Spec.Supplement.CondDriverBridge

/-!
# The retained Gaussian law as input to the K2 flow-driver bridge

The named active-germ mean identity below is the remaining analytic input.
The Gaussian characteristic functional itself is proved from marked locality
and this identity, rather than assumed again at the K2 interface. The random
word evolution, its word identification, and the actual charts remain inputs.
This conditional helper does not assert either uniform SB4 construction.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.SewLaw

open LocalSets Exist.Staged

/-- The exact additional mean identification for the physical active component.
It is not a consequence of locality alone. Both retained histories, including
their old boundary labels, must be used to prove this identity in applications. -/
def HasActiveGermMean {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝓜 : ℝ≥0 → MeasurableSpace Ω) (A : ℝ≥0 → Ω → Set ℂ)
    (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ)
    (F : Set Ω) (ζ : Ω → ℝ≥0∞) (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ (q : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F →
    (q : ℝ≥0∞) < ζ ω → tsupport φ ⊆ H \ A q ω →
      P[fun ω' => WholeField.centredField h u₀ ω' φ |
        germSigma (A q) (WholeField.centredField h u₀) ⊔ 𝓜 q] ω =
          M q ω φ - (∫ z, u₀ z * φ z)

variable {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {nL nR : ℕ}
  {κ θ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {F : Set Ω} {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {𝓗 : Filtration ℝ≥0 mΩ} {bc : Ω → ℝ → ℝ} {jc : Ω → Finset ℝ}

/-- K2 constructs the retained conditional ordinary driver once the joint local
mean is identified. The physical Gaussian-law premise of the landed bridge is
discharged here, with the correct physical active component covariance. -/
theorem isCondFlowLineDriverOn_of_activeGermMean
    (hE : Sec7.Aux122Disint.IsRandomWordEvolution κ P 𝒢 F ΘL ΘR ρL ρR 𝓗 W VL VR B ζ)
    (hζ0 : ∀ᵐ ω ∂P, ω ∈ F → 0 < ζ ω)
    {𝓗' : Filtration ℝ≥0 mΩ} (h𝒢' : 𝒢 ≤ 𝓗' 0) (hW' : AdaptedBefore 𝓗' ζ W)
    (hVL' : ∀ i, AdaptedBefore 𝓗' ζ (VL i)) (hVR' : ∀ j, AdaptedBefore 𝓗' ζ (VR j))
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom)
    (𝓜 : ℝ≥0 → MeasurableSpace Ω) (h𝓗𝓜 : ∀ q, 𝓗' q ≤ 𝓜 q)
    (h𝓜 : ∀ q, 𝓜 q ≤ mΩ) (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hMm : ∀ q, Measurable[𝓜 q] (M q))
    (A : ℝ≥0 → Ω → Set ℂ) (hAm : ∀ s, Measurable[𝓜 s, hittingSigma] (A s))
    (hAc : ∀ s ω, A s ω ⊆ H ∧ IsOpen (H \ A s ω))
    (hloc : ∀ s, WholeField.IsHistoryAvoidanceLocal
      (𝓜 s) (A s) (WholeField.centredField h u₀) P)
    (hAK : ∀ s : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (s : ℝ≥0∞) < ζ ω →
      H \ A s ω = (c ω).2.1 '' (H \ QuantumZipper.fwdHull
        (fun r : ℝ => W r.toNNReal ω) s))
    (hgm : HasActiveGermMean P 𝓜 A h u₀ F ζ M)
    (hmean : ∀ (q : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F →
      ω ∈ Restart.DomainMarkov.avoidSet W ζ ψ q →
        Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (M q ω) ψ =
          ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) q
            (Restart.DomainMarkov.bheProc κ ρL ρR W VL VR ω q) z * ψ z)
    (hword : ∀ᵐ ω ∂P, ω ∈ F → IsPiecewiseConstantBoundaryData (bc ω) (jc ω) ∧
      flowLineNL (bc ω) (jc ω) 0 = nL ∧ flowLineNR (bc ω) (jc ω) 0 = nR ∧
      truncWord nL nR (padFL κ θ (bc ω) (jc ω)) = ((ΘL ω, ΘR ω), (ρL, ρR)))
    (hcc : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), c ω = c ω₀)
    (hWm : ∀ t, Measurable (W t)) :
    IsCondFlowLineDriverOn κ θ 𝒢 P F h c bc jc W ζ := by
  have hcond : ∀ (q : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F →
      (q : ℝ≥0∞) < ζ ω → tsupport φ ⊆ (c ω).2.1 ''
        (H \ QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) q) →
      P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | 𝓜 q] ω =
        Complex.exp (Complex.I * (M q ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 ''
            (H \ QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) q)) φ φ : ℝ) : ℂ)) := by
    intro q φ
    let D := {ω | ω ∈ F ∧ (q : ℝ≥0∞) < ζ ω ∧
      Disjoint (tsupport φ) (relClosureH (A q ω))}
    have hFq : MeasurableSet[𝓜 q] F :=
      (h𝒢'.trans ((𝓗'.mono (zero_le (a := q))).trans (h𝓗𝓜 q))) _ hE.2.1
    have hζq : MeasurableSet[𝓜 q] {ω | (q : ℝ≥0∞) < ζ ω} :=
      h𝓗𝓜 q _ (Restart.DomainMarkov.K2.measurableSet_lt_of_adaptedBefore hW' q)
    have hD : MeasurableSet[𝓜 q] D :=
      hFq.inter (hζq.inter ((measurableSet_disjoint_relClosureH
        φ.hasCompactSupport.isCompact φ.tsupport_subset).preimage (hAm q)))
    have he := ae_retained_physical_cexp_of_mean ⟨𝓜 q, h𝓜 q⟩ hu₀ hh0
      (hAm q) (hloc q) (Eventually.of_forall (hAc q)) φ hD
      ((LQGMetric.measurable_distOn_apply φ).comp (hMm q))
      ((hgm q φ).mono fun ω hω hωD => hω hωD.1 hωD.2.1
        (fun z hz => ⟨φ.tsupport_subset hz, fun hzA =>
          Set.disjoint_left.1 hωD.2.2 hz ((relClosureH_eq (hAc q ω).1
            (hAc q ω).2).symm ▸ hzA)⟩))
    filter_upwards [he, hAK q] with ω heω hAKω hωF hωq hφ
    have hdis : Disjoint (tsupport φ) (relClosureH (A q ω)) := by
      rw [relClosureH_eq (hAc q ω).1 (hAc q ω).2]
      exact Set.disjoint_left.2 fun z hz hzA =>
        ((hAKω hωF hωq).symm ▸ hφ hz).2 hzA
    simpa only [hAKω hωF hωq, Function.comp_apply] using heω ⟨hωF, hωq, hdis⟩
  exact CondDriverBridge.isCondFlowLineDriverOn_of_k2 hE hζ0 h𝒢' hW' hVL' hVR'
    hhm hu₀ hh0 hc hdom hfwd hliftm hliftc hlift 𝓜 h𝓗𝓜 h𝓜 M hcond hmean
    𝓜 h𝓗𝓜 h𝓜 A (fun s => (hAm s).mono (h𝓜 s) le_rfl) hAc hloc hAK hword hcc hWm

end InteractingSLE.Theorem14.SB.SewLaw
