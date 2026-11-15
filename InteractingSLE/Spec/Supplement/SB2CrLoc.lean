/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CrMem
import InteractingSLE.Spec.Supplement.SB2CrLife

/-!
# (L) from the history-marked line locality, under a strict time change

Packet PROVE-SB2-CONDFIN (round 8, D44). `Aux79.hasSafeMembers_of_lineLocal` and
`BW1Lines.hasSafeMembers_life_of_lineLocal` with the strict first passage (`Cr.hasSafeMembers_of_lineMembersS`):
the capacity-time filtration's `q`-events need only be cut by `{q < Qc t}`, and the line safe events need only be
measurable where the clock is positive.

* `hasSafeMembers_of_lineLocalS`; **`hasSafeMembers_life_of_lineLocalS`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Cr

open Restart.DomainMarkov Restart.DomainMarkov.K2 Restart.DomainMarkov.Aux79 Restart.DomainMarkov.Mean BW1Chain
  BW1Lines Coupling LocalSets WholeField

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {nL nR : ℕ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}

/-- **(L) from the history-marked line locality, under a strict time change.** -/
theorem hasSafeMembers_of_lineLocalS {𝓖 𝓗' : Filtration ℝ≥0 mΩ} {F : Set Ω} {ζ : Ω → ℝ≥0∞}
    {Qc : ℝ≥0 → Ω → ℝ≥0} {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom) (a k : ℝ)
    (hQc : ∀ ω, Continuous fun t => Qc t ω) (hQm : ∀ ω, Monotone fun t => Qc t ω) (hQ0 : ∀ ω, Qc 0 ω = 0)
    (hQa : ∀ t, Measurable[𝓖 t] (Qc t))
    (h𝓗' : ∀ q D, MeasurableSet[𝓗' q] D → ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | q < Qc t ω}))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < ζ ω → ∃ t, q ≤ Qc t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR ζ ω)
    (hS : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t,
      MeasurableSet[𝓖 t] ({ω | 0 < Qc t ω} ∩ lineSafe Qc W ζ (ballsK Fb) t))
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (h𝓖ℋ : ∀ t, 𝓖 t ≤ ℋ t) (hℋ : ∀ t, ℋ t ≤ mΩ)
    (B : ℝ≥0 → Ω → Set ℂ) (hBm : ∀ t, Measurable[mΩ, hittingSigma] (B t))
    (hBc : ∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω))
    (hloc : ∀ t, IsHistoryAvoidanceLocal (ℋ t) (B t) (centredField h u₀) P)
    (hBK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (Qc t ω : ℝ≥0∞) < ζ ω →
      H \ B t ω = (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω))) :
    HasSafeMembers P 𝓗' F ζ W fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) := by
  have hXψ : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) ψ :=
    fun ψ => ((measurable_pi_apply ψ).comp (Measurable.of_comap_le le_rfl)).comp
      (Chart.measurable_chartTransport_random' hc (fun z => 𝓖.le 0 _ (hdom z))
        (fun z => (hfwd z).mono (𝓖.le 0) le_rfl) (fun z => (hliftm z).mono (𝓖.le 0) le_rfl) hliftc hhm 1 a k)
  have hreg' : ∀ᵐ ω ∂P, ω ∈ F → IsDrvReg W ζ ω := by
    filter_upwards [hreg] with ω hω hωF using ⟨(hω hωF).2.1, (hω hωF).1⟩
  refine hasSafeMembers_of_lineMembersS (VL := VL) (VR := VR) hXψ hQc hQm hQ0 hQa h𝓗' hreach hreg hS
    fun t Fb hFH E hE hEs f Ξ => ?_
  have h0t : 𝓖 0 ≤ ℋ t := (𝓖.mono (zero_le (a := t))).trans (h𝓖ℋ t)
  exact setIntegral_lapTest_of_lineLocal hhm hu₀ hh0 hc (hℋ t) (fun z => h0t _ (hdom z))
    (fun z => (hfwd z).mono h0t le_rfl) (fun z => (hliftm z).mono h0t le_rfl) hliftc hlift a k (Qc t) (B t)
    (hBm t) (hBc t) (hloc t) (hBK t) hreg' Fb hFH (h𝓖ℋ t _ hE) (by
      filter_upwards [hEs] with ω hω hωE using ⟨(hω hωE).1, (hω hωE).2.2.1, (hω hωE).2.2.2⟩) f Ξ

/-- **(L) with the lifetime `V` from the history-marked line locality below `V`, under a strict time change.** -/
theorem hasSafeMembers_life_of_lineLocalS {a : ℝ≥0 → Ω → ℝ≥0∞} {𝓖 𝓗' : Filtration ℝ≥0 mΩ} {F : Set Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom) (σa k : ℝ)
    (hac : ∀ ω, Continuous fun t => a t ω) (ham : ∀ ω, Monotone fun t => a t ω)
    (ha0 : ∀ ω, a 0 ω = 0) (haa : ∀ t, Measurable[𝓖 t] (a t))
    (h𝓗' : ∀ q D, MeasurableSet[𝓗' q] D → ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | (q : ℝ≥0∞) < a t ω}))
    (V : Ω → ℝ≥0∞) (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < V ω → ∃ t, (q : ℝ≥0∞) ≤ a t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR V ω)
    (hS : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[𝓖 t]
      {ω | 0 < a t ω ∧ a t ω < V ω ∧
        Disjoint (Coupling.ballsK Fb) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)})
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (h𝓖ℋ : ∀ t, 𝓖 t ≤ ℋ t) (hℋ : ∀ t, ℋ t ≤ mΩ)
    (B : ℝ≥0 → Ω → Set ℂ) (hBm : ∀ t, Measurable[mΩ, hittingSigma] (B t))
    (hBc : ∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω))
    (hloc : ∀ t, IsHistoryAvoidanceLocal (ℋ t) (B t) (centredField h u₀) P)
    (hBK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → a t ω < V ω →
      H \ B t ω = (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)) :
    HasSafeMembers P 𝓗' F V W fun ω => Chart.chartTransport (hc ω) 1 σa k (h ω) := by
  have hN : ∀ N : ℝ≥0, HasSafeMembers P 𝓗' F (fun ω => min (V ω) N) W
      fun ω => Chart.chartTransport (hc ω) 1 σa k (h ω) := by
    intro N
    refine hasSafeMembers_of_lineLocalS (Qc := capClock a N) (VL := VL) (VR := VR) hhm hu₀ hh0 hc hdom hfwd
      hliftm hliftc hlift σa k (continuous_capClock hac N) (monotone_capClock ham N) (capClock_zero ha0 N)
      (measurable_capClock haa N) (measurableSet_inter_capClockS h𝓗' N) (reach_capClock_life hreach N) ?_
      (fun Fb t => measurableSet_pos_lineSafe_capClock_life haa (hS Fb t) N) ℋ h𝓖ℋ hℋ B hBm hBc hloc ?_
    · filter_upwards [hreg] with ω hω hωF using isForceReg_mono (min_le_left _ _) (hω hωF)
    · intro t
      filter_upwards [hBK t] with ω hω hωF hlt
      obtain ⟨haN, haV⟩ := coe_capClock_lt_min_iff.1 hlt
      rw [capClock_eq_of_lt haN]
      exact hω hωF haV
  intro s Fb hFb D hD hDs
  refine hN (s + 1) s Fb hFb D hD ?_
  filter_upwards [hDs] with ω h1 hωD
  obtain ⟨hF', hsV, hdis⟩ := h1 hωD
  exact ⟨hF', lt_min hsV (ENNReal.coe_lt_coe.2 (lt_add_one s)), hdis⟩

end InteractingSLE.Theorem14.SB.Cr
