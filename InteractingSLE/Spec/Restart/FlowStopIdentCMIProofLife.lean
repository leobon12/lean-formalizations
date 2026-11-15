/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIStmt
import InteractingSLE.Spec.Restart.FlowStopIdentLLTerminal
import InteractingSLE.Spec.Restart.FlowStopIdentLift

/-!
# The lifetime clause of the explicit-shift (L1) is free

Packet PROVE-L1-CMI (continuation). `FlowLineStopIdentCMIStatement` asks for a stopped flow line **with the lifetime
clause** (`FlowStopIdentG.IsStoppedFlowLineL`). PROVE-L1-LL's `FlowStopIdentLL.isStoppedFlowLineL_of_isStoppedFlowLine`
adds the clause to any stopped replacement flow line in the locality setting. Here:

* `CMIStoppedStatement`: the explicit-shift (L1) with the stopped flow line **without** the lifetime clause;
* **`flowLineStopIdentCMIStatement_of_stopped`**: it implies `FlowLineStopIdentCMIStatement` (the source flow line read
  through the first projection on `Q₀ ⊗ ν` is a flow line, `FlowStopIdentLift.isFlowLine_fst`; `Q* ⊗ ν ≪ Q₀ ⊗ ν`; the
  real points of `V` lie in `O` since `closure V ⊆ N`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

namespace FlowStopIdentCMI

open QuantumZipper (H)
open LQGMetric (TestOn DistOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open StoppedExtend

/-- **The explicit-shift (L1) without the lifetime clause**: as `FlowLineStopIdentCMIStatement`, with
`StoppedExtend.IsStoppedFlowLine` in place of `FlowStopIdentG.IsStoppedFlowLineL`. -/
def CMIStoppedStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b bR : ℝ → ℝ) (J Ĵ : Finset ℝ), IsPiecewiseConstantBoundaryData b J →
    IsPiecewiseConstantBoundaryData bR Ĵ → ∀ O : Set ℝ, IsOpen O → (∀ x ∈ O, b x = bR x) →
    ∀ N : Set ℂ, IsOpen N → (∀ z ∈ N, z.im = 0 → z.re ∈ O) →
    ∀ V : Set ℂ, IsOpen V → Bornology.IsBounded V → closure V ⊆ N →
    ∀ a c : ℝ, Icc a c ⊆ O → (∀ z ∈ closure V, z.im = 0 → z.re ∈ Icc a c) → FlowStopIdentCM.shiftHullSet V a c ⊆ N →
    ∀ (F : CMCut) (q : ℂ → ℝ),
      IsBoundedHarmonicExtension (fun x => bR x - b x) ((J ∪ Ĵ : Finset ℝ) : Set ℝ) q →
      (∀ z ∈ N, z ∈ H → F.f z = q z) → (∀ z ∈ N, QuantumZipper.K3.greenDensity F.f z = 0) →
    ∀ y θ : ℝ,
    ∀ {S : Type u} [MeasurableSpace S] (Q₀ : Measure S) [IsProbabilityMeasure Q₀]
      (H₀ : S → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q₀ H₀ b J →
    ∀ s : ℕ → TestOn upperHalfPlaneOpens, (∀ n z, |s n z| ≤ |F.src z|) →
      (∀ z, Tendsto (fun n => s n z) atTop (𝓝 (F.src z))) →
    ∀ Λ : S → ℝ, Measurable Λ → (∀ᵐ x ∂Q₀, Tendsto (fun n => H₀ x (s n)) atTop (𝓝 (Λ x))) →
    ∀ k : ℝ, 0 < k → IsProbabilityMeasure (Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x))) →
    ∀ (Γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞), IsFlowLine κ b J y θ Q₀ H₀ Γ U →
      ∃ (ν : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure ν),
        IsStoppedFlowLine κ bR Ĵ y θ ((Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x))).prod ν)
          (fun p => H₀ p.1 + smoothDist upperHalfPlaneOpens fun z => q z - F.f z) (fun p => Γ p.1)
          fun p => RLC.exitTime V (Γ p.1) (U p.1)

/-- **The lifetime clause is free** (PROVE-L1-LL). -/
theorem flowLineStopIdentCMIStatement_of_stopped (h : CMIStoppedStatement.{u}) :
    FlowLineStopIdentCMIStatement.{u} := by
  intro κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO V hV hVb hVN a c haO hVa hsN F q hq hFq hFΔ y θ S _ Q₀ _ H₀ hH
    s hsle hslim Λ hΛm hΛ k hk hprob Γ U hΓ
  obtain ⟨ν, hν, hstop⟩ := h κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO V hV hVb hVN a c haO hVa hsN F q hq hFq hFΔ
    y θ Q₀ H₀ hH s hsle hslim Λ hΛm hΛ k hk hprob Γ U hΓ
  refine ⟨ν, hν, ?_⟩
  have hμ : (Q₀.prod ν).map Prod.fst = Q₀ := Measure.map_fst_prod.trans (by simp)
  have hflow := FlowStopIdentLift.isFlowLine_fst (C := ℕ → ℝ) hμ hΓ
  have hac : (Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x))).prod ν ≪ Q₀.prod ν :=
    (withDensity_absolutelyContinuous _ _).prod Measure.AbsolutelyContinuous.rfl
  exact FlowStopIdentLL.isStoppedFlowLineL_of_isStoppedFlowLine hκ hb hbR hO hbO hV
    (fun z hz => hNO z (hVN (subset_closure hz))) hac hflow hstop

end FlowStopIdentCMI

end Restart

end InteractingSLE
