/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1RestartLawMean
import InteractingSLE.Spec.Restart.DomainMarkovMeanK2

/-!
# BW1 and BR4a: retained-chart kernels from local means

The physical covariance and both K2 field clauses follow from marked locality.
Thus only the active germ mean and its chart identification need to be supplied
by the terminal or retargeting comparison, along with the actual relative
evolution and hull geometry. No conditional field–path law is assumed here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.GW1RestartLaw

open Coupling LocalSets WholeField Restart.DomainMarkov

/-- The precise chart-mean identification still needed on terminal and
retargeting comparison buffers. It asserts only an identity of distributions;
the conditional Gaussian law is a consequence proved below. -/
def HasRetainedChartMean {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (F : Set Ω) (V : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal) (a k : ℝ)
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ (q : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F →
    ω ∈ avoidSet W V ψ q → Chart.chartTransport (hc ω) 1 a k (M q ω) ψ =
      ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) q (bheProc κ ρL ρR W VL VR ω q) z * ψ z

/-- The stopped K2 in a retained chart, with its Gaussian and member clauses
proved from history-marked locality and the active physical mean. -/
theorem ae_isOptionalHullCoupling_chartTransport_of_activeMean
    {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} {nL nR : ℕ}
    {F : Set Ω} {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓗 𝓗' : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hE : Restart.StoppedK2.IsRandomWordEvolutionUpTo κ P 𝒢 F ΘL ΘR ρL ρR 𝓗 W VL VR B V)
    (h𝒢' : 𝒢 ≤ 𝓗' 0) (hW : AdaptedBefore 𝓗' V W)
    (hVL : ∀ i, AdaptedBefore 𝓗' V (VL i)) (hVR : ∀ j, AdaptedBefore 𝓗' V (VR j))
    (hXP : IsMeasurableKilledDriving W VL VR V)
    (hV : ∀ᵐ ω ∂P, ω ∈ F → V ω = ⊤)
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom) (a k : ℝ)
    (𝓜 : ℝ≥0 → MeasurableSpace Ω) (h𝓗𝓜 : ∀ q, 𝓗' q ≤ 𝓜 q) (h𝓜 : ∀ q, 𝓜 q ≤ mΩ)
    (A : ℝ≥0 → Ω → Set ℂ) (hAm : ∀ q, Measurable[𝓜 q, hittingSigma] (A q))
    (hAc : ∀ q ω, A q ω ⊆ H ∧ IsOpen (H \ A q ω))
    (hloc : ∀ q, IsHistoryAvoidanceLocal (𝓜 q) (A q) (centredField h u₀) P)
    (hAK : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < V ω →
      H \ A q ω = (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) q))
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens) (hM : ∀ q, Measurable[𝓜 q] (M q))
    (hgm : SB.SewLaw.HasActiveGermMean P 𝓜 A h u₀ F V M)
    (hmean : HasRetainedChartMean P κ ρL ρR F V W VL VR hc a k M) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ F →
      ∃ (𝓕' : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ)
        (VL' : Fin nL → ℝ≥0 → Ω → ℝ) (VR' : Fin nR → ℝ≥0 → Ω → ℝ)
        (B' : ℝ≥0 → Ω → ℝ),
        IsOptionalHullCoupling κ (ΘL ω₀) (ΘR ω₀) ρL ρR
          (condExpKernel P 𝒢 ω₀) 𝓕' W' VL' VR' B' V
            (fun ω => Chart.chartTransport (hc ω) 1 a k (h ω)) ∧
        ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∀ t, W' t ω = W t ω ∧
          (∀ i, VL' i t ω = VL i t ω) ∧ ∀ j, VR' j t ω = VR j t ω := by
  have h𝒢m : 𝒢 ≤ mΩ := h𝒢'.trans (𝓗'.le 0)
  have hX : Measurable fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) :=
    Chart.measurable_chartTransport_random' hc (fun z => h𝒢m _ (hdom z))
      (fun z => (hfwd z).mono h𝒢m le_rfl) (fun z => (hliftm z).mono h𝒢m le_rfl) hliftc hhm 1 a k
  have hreg : ∀ᵐ ω ∂P, ω ∈ F → Mean.IsDrvReg W V ω := by
    filter_upwards [hE.2.2.2.2.2.2.2.2] with ω hp hω
    exact ⟨(hp hω).continuousOn_w, (hp hω).w_zero⟩
  have hF : ∀ q, MeasurableSet[𝓜 q] F := fun q =>
    h𝓗𝓜 q _ (h𝒢'.trans (𝓗'.mono (zero_le (a := q))) _ hE.2.1)
  have hVq : ∀ q : ℝ≥0, MeasurableSet[𝓜 q] {ω | (q : ℝ≥0∞) < V ω} := fun q =>
    h𝓗𝓜 q _ (K2.measurableSet_lt_of_adaptedBefore hW q)
  have hphys := ae_physical_kernel_of_activeMean hu₀ hh0 h𝓜 hF hVq hAm hAc hloc hM hgm
  have hcond : ∀ (q : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
      ω ∈ F → (q : ℝ≥0∞) < V ω →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) q) →
      P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | 𝓜 q] ω =
        Complex.exp (Complex.I * (M q ω φ : ℂ) -
          (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov
            ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) q)) φ φ : ℝ) : ℂ)) := by
    intro q φ
    filter_upwards [hphys q φ, hAK q] with ω hp ha hω hq hφ
    rw [← ha hω hq]
    exact hp hω hq (by rwa [ha hω hq])
  have hlaw := Mean.hasSafeLaw_chartTransport (ρL := ρL) (ρR := ρR) (VL := VL) (VR := VR)
    h𝒢' hc hdom hfwd hliftm hliftc hhm a k 𝓜 h𝓗𝓜 h𝓜 M hcond hmean hreg
  have hmem := Mean.hasSafeMembers_chartTransport h𝒢' hhm hu₀ hh0 hc hdom hfwd hliftm
    hliftc hlift a k 𝓜 h𝓗𝓜 h𝓜 A
    (fun q => (hAm q).mono (h𝓜 q) le_rfl) hAc hloc hAK hreg
  exact ae_isOptionalHullCoupling_of_stoppedK2_ae_top hE hX h𝒢' hW hVL hVR hlaw hmem hXP hV

end InteractingSLE.Theorem14.GW1RestartLaw
