/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkTrace12Compare
import InteractingSLE.Spec.Sec5.Aux61R45Barrier

/-!
# One null event excludes every left comparison contact

The announced local comparison estimate is independent of a trace. Intersecting
its complements over rational restart times makes it available for every
completed trace prefix on the same sample.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.TwoMark.Trace12

/-- No left comparison contact occurs before an announced local horizon, including its endpoint. -/
theorem ae_no_left_comparison {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {κ c : ℝ} {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {τ : Ω → ℝ≥0∞} {A : ℕ → Ω → ℝ≥0}
    (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hE : Sec2.IsSLEEvolutionUpTo κ xL xR ρL ρR P 𝓕 W VL VR B τ)
    (hW : ∀ ω, ContinuousOn (W · ω) {u | (u : ℝ≥0∞) < τ ω})
    (hL : ∀ i ω, ContinuousOn (VL i · ω) {u | (u : ℝ≥0∞) < τ ω})
    (hR : ∀ j ω, ContinuousOn (VR j · ω) {u | (u : ℝ≥0∞) < τ ω})
    (hA : Coupling.IsAnnouncingSeq 𝓕 P τ A) {k : Fin nL} (hc : κ / 2 - 2 ≤ c) :
    ∀ᵐ ω ∂P, ∀ q : ℚ, ¬ GB7a.RightCmpPath ρR ρL (fun u => -W u ω)
      (fun j u => -VR j u ω) (fun i u => -VL i u ω) (τ ω) k none c (q : ℝ).toNNReal := by
  have hER : Sec2.IsSLEEvolutionUpTo κ (-xR) (-xL) ρR ρL P 𝓕 (-W)
      (fun j => -VR j) (fun i => -VL i) (-B) τ :=
    ⟨hE.brownian.neg, hE.adapted_W.neg, fun j => (hE.adapted_VR j).neg,
      fun i => (hE.adapted_VL i).neg, hE.ae_path.mono fun _ hp => hp.reflect⟩
  have hnull : ∀ q : ℚ, P {ω | GB7a.RightCmp ρR ρL (-W) (fun j => -VR j) (fun i => -VL i)
      τ k none c (q : ℝ).toNNReal ω} = 0 := fun q =>
    Aux61R45.measure_rightCmp_eq_zero_upTo hκ hκ4 hER (fun ω => (hW ω).neg)
      (fun j ω => (hR j ω).neg) (fun i ω => (hL i ω).neg) hA
      (by simp only [reduceCtorEq, false_implies, implies_true]) hc (q : ℝ).toNNReal
  filter_upwards [ae_all_iff.2 (fun q => measure_eq_zero_iff_ae_notMem.1 (hnull q))] with ω hω q hq
  exact hω q (GB7a.rightCmp_iff.2 hq)

end InteractingSLE.Sec5.TwoMark.Trace12
