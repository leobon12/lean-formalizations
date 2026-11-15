/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofResidualVersions
import InteractingSLE.Spec.Restart.RetPlumbProofResidualDriver

/-!
# Supported-clock versions of the landed retained-line wrappers

Packet PROVE-RETPLUMB. The original line kernels, words and filled line sets
supply (S) and (L) with the supported measurable clock. No measurability of the
raw clock outside the initial event is required.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdMapInv fwdHull logDerivFwd zeroGFFTestCov)
open LQGMetric (TestOn DistOn)
namespace InteractingSLE.Restart.RetAux79
open Chart DomainMarkov DomainMarkov.Aux79 DomainMarkov.K2
open Coupling LocalSets WholeField
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- Apply the retained-line (S) wrapper with the supported clock and lifetime.
All its geometric and kernel premises keep their original on-event form. -/
theorem hasSafeLaw_of_retLines_indicator {𝓖 : Filtration ℝ≥0 mΩ} {F : Set Ω}
    (hF : MeasurableSet[𝓖 0] F) {Qc : ℝ≥0 → Ω → ℝ≥0} {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (a : ℝ)
    (hQc : ∀ ω, Continuous fun t => Qc t ω) (hQm : ∀ ω, Monotone fun t => Qc t ω) (hQ0 : ∀ ω, Qc 0 ω = 0)
    (hQa : ∀ t, Measurable[𝓖 t] (F.indicator (Qc t)))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < ζ ω → ∃ t, q ≤ Qc t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR ζ ω)
    (hS : ∀ (ψ : TestOn upperHalfPlaneOpens) t, MeasurableSet[𝓖 t] (F ∩ lineSafe Qc W ζ (tsupport ψ) t))
    (𝒢L : ℝ≥0 → MeasurableSpace Ω) (h𝒢L : ∀ t, 𝓖 t ≤ 𝒢L t) (h𝒢Lm : ∀ t, 𝒢L t ≤ mΩ)
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hker : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F → (Qc t ω : ℝ≥0∞) < ζ ω →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω)) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢L t] ω =
        Complex.exp (Complex.I * (M t ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω))) φ φ :
            ℝ) : ℂ)))
    (hWc : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {cl : ℝ≥0 → Ω → Chart}
    (hcl : ∀ t ω, (cl t ω).IsConformal) (β : ℝ≥0 → Ω → BoundaryWord)
    (hline : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (Qc t ω : ℝ≥0∞) < ζ ω → (β t ω).IsSorted ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        chartTransport (hcl t ω) 1 0 (QuantumZipper.chiC κ) (M t ω) φ = ∫ w, (β t ω).mean w * φ w) ∧
      (∀ w ∈ H, (cl t ω).2.1 w = (c ω).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (Qc t ω) w)) ∧
      (∀ w ∈ H, (cl t ω).2.2 ((cl t ω).2.1 w) =
        (logDerivFwd (fun s : ℝ => W s.toNNReal ω) (Qc t ω)
          (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (Qc t ω) w)).im +
          (c ω).2.2 ((c ω).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (Qc t ω) w))) ∧
      ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S, forceBoundaryData κ ρL ρR (fun i => VL i (Qc t ω) ω - W (Qc t ω) ω)
        (fun j => VR j (Qc t ω) ω - W (Qc t ω) ω) y = (β t ω).fn y + a) :
    HasSafeLaw κ ρL ρR P (timeChange 𝓖 (fun t => F.indicator (Qc t)) hQa) F (F.indicator ζ) W VL VR
      fun ω => chartTransport (hc ω) 1 a (QuantumZipper.chiC κ) (h ω) := by
  classical
  obtain ⟨hc', hm', h0'⟩ := indicator_clock_properties hQc hQm hQ0 (F := F)
  apply hasSafeLaw_of_retLines hF hc hdom hfwd hliftm hliftc hh a hc' hm' h0' hQa
    (fun _ _ hD t => measurableSet_inter_of_timeChange hD t) ?_ ?_ ?_
    𝒢L h𝒢L h𝒢Lm M ?_ hWc hW0 hcl β ?_
  · intro q
    filter_upwards [hreach q] with ω hr hω hq
    rw [indicator_of_mem hω] at hq
    obtain ⟨t, ht⟩ := hr hω hq
    exact ⟨t, by simpa only [indicator_of_mem hω] using ht⟩
  · filter_upwards [hreg] with ω hr hω
    simpa only [IsForceReg, indicator_of_mem hω] using hr hω
  · intro ψ t
    rw [lineSafe_indicator]
    exact hS ψ t
  · intro t φ
    filter_upwards [hker t φ] with ω hk hω hlt hs
    simpa only [indicator_of_mem hω] using hk hω
      (by simpa only [indicator_of_mem hω] using hlt)
      (by simpa only [indicator_of_mem hω] using hs)
  · intro t
    filter_upwards [hline t] with ω hl hω hlt
    simpa only [indicator_of_mem hω] using hl hω
      (by simpa only [indicator_of_mem hω] using hlt)

/-- Apply the retained filled-set (L) wrapper with the supported clock and
lifetime. History locality is still the landed locality of the real line sets. -/
theorem hasSafeMembers_of_lineLocal_indicator {𝓖 : Filtration ℝ≥0 mΩ} {F : Set Ω} {Qc : ℝ≥0 → Ω → ℝ≥0}
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom) (a k : ℝ)
    (hQc : ∀ ω, Continuous fun t => Qc t ω) (hQm : ∀ ω, Monotone fun t => Qc t ω) (hQ0 : ∀ ω, Qc 0 ω = 0)
    (hQa : ∀ t, Measurable[𝓖 t] (F.indicator (Qc t)))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < ζ ω → ∃ t, q ≤ Qc t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR ζ ω)
    (hS : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[𝓖 t] (F ∩ lineSafe Qc W ζ (ballsK Fb) t))
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (h𝓖ℋ : ∀ t, 𝓖 t ≤ ℋ t) (hℋ : ∀ t, ℋ t ≤ mΩ)
    (B : ℝ≥0 → Ω → Set ℂ) (hBm : ∀ t, Measurable[mΩ, hittingSigma] (B t))
    (hBc : ∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω))
    (hloc : ∀ t, IsHistoryAvoidanceLocal (ℋ t) (B t) (centredField h u₀) P)
    (hBK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (Qc t ω : ℝ≥0∞) < ζ ω →
      H \ B t ω = (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω))) :
    HasSafeMembers P (timeChange 𝓖 (fun t => F.indicator (Qc t)) hQa) F (F.indicator ζ) W
      fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) := by
  classical
  obtain ⟨hc', hm', h0'⟩ := indicator_clock_properties hQc hQm hQ0 (F := F)
  apply hasSafeMembers_of_lineLocal (VL := VL) (VR := VR) hhm hu₀ hh0 hc hdom hfwd hliftm
    hliftc hlift a k hc' hm' h0' hQa
    (fun _ _ hD t => measurableSet_inter_of_timeChange hD t) ?_ ?_ ?_
    ℋ h𝓖ℋ hℋ B hBm hBc hloc ?_
  · intro q
    filter_upwards [hreach q] with ω hr hω hq
    rw [indicator_of_mem hω] at hq
    obtain ⟨t, ht⟩ := hr hω hq
    exact ⟨t, by simpa only [indicator_of_mem hω] using ht⟩
  · filter_upwards [hreg] with ω hr hω
    simpa only [IsForceReg, indicator_of_mem hω] using hr hω
  · intro Fb t
    rw [lineSafe_indicator]
    exact hS Fb t
  · intro t
    filter_upwards [hBK t] with ω hk hω hlt
    simpa only [indicator_of_mem hω] using hk hω
      (by simpa only [indicator_of_mem hω] using hlt)

end InteractingSLE.Restart.RetAux79
