/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CrKer
import InteractingSLE.Spec.Supplement.BW1LinesSafe

/-!
# (S) with a lifetime from the line data, under a strict time change

Packet PROVE-SB2-CONDFIN (round 8, D44). `BW1Lines.hasSafeLaw_life_of_lineKernel` with
`Cr.hasSafeLaw_of_lineKernelS` in place of `Aux79.hasSafeLaw_of_lineKernel`. The relative clock `a` is extended
(`ℝ≥0∞`), the lifetime `V` arbitrary, and the strict time change `D ∈ 𝓗'_q ⇒ D ∩ {q < a t} ∈ 𝓖_t`. The conditioning
event `M` (an event of `𝓖₀` containing the live event) carries the line data where the clock is positive.

* `pos_capClock_iff`, `measurableSet_inter_capClockS`, `measurableSet_pos_lineSafe_capClock_life`;
* **`hasSafeLaw_life_of_lineKernelS`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Cr

open Restart.DomainMarkov Restart.DomainMarkov.K2 Restart.DomainMarkov.Aux79 BW1Chain BW1Lines

section Cap

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {a : ℝ≥0 → Ω → ℝ≥0∞}

/-- The capped clock is positive exactly when the clock and the level are. -/
theorem pos_capClock_iff {N t : ℝ≥0} {ω : Ω} : 0 < capClock a N t ω ↔ 0 < a t ω ∧ 0 < N := by
  rw [← ENNReal.coe_pos, coe_capClock, lt_min_iff, ENNReal.coe_pos]

/-- The strict time change passes to the capped clock. -/
theorem measurableSet_inter_capClockS {𝓖 𝓗' : Filtration ℝ≥0 mΩ}
    (h𝓗' : ∀ q D, MeasurableSet[𝓗' q] D → ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | (q : ℝ≥0∞) < a t ω}))
    (N q : ℝ≥0) (D : Set Ω) (hD : MeasurableSet[𝓗' q] D) (t : ℝ≥0) :
    MeasurableSet[𝓖 t] (D ∩ {ω | q < capClock a N t ω}) := by
  by_cases hqN : q < N
  · have e : D ∩ {ω | q < capClock a N t ω} = D ∩ {ω | (q : ℝ≥0∞) < a t ω} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq]
      rw [← ENNReal.coe_lt_coe, coe_capClock, lt_min_iff]
      exact and_congr_right fun _ => ⟨fun h => h.1, fun h => ⟨h, ENNReal.coe_lt_coe.2 hqN⟩⟩
    rw [e]
    exact h𝓗' q D hD t
  · have e : D ∩ {ω | q < capClock a N t ω} = ∅ := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
      intro _
      rw [← ENNReal.coe_le_coe, coe_capClock]
      exact (min_le_right _ _).trans (ENNReal.coe_le_coe.2 (not_lt.1 hqN))
    rw [e]
    exact @MeasurableSet.empty _ (𝓖 t)

/-- The positive part of the capped line safe event, from the positive part of the line safe event. -/
theorem measurableSet_pos_lineSafe_capClock_life {𝓖 : Filtration ℝ≥0 mΩ} (haa : ∀ t, Measurable[𝓖 t] (a t))
    {W : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {C : Set ℂ} {t : ℝ≥0}
    (hS : MeasurableSet[𝓖 t] {ω | 0 < a t ω ∧ a t ω < V ω ∧
      Disjoint C (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)}) (N : ℝ≥0) :
    MeasurableSet[𝓖 t] ({ω | 0 < capClock a N t ω} ∩ lineSafe (capClock a N) W (fun ω => min (V ω) N) C t) := by
  rw [lineSafe_capClock_life_eq]
  by_cases hN : 0 < N
  · have e : {ω | 0 < capClock a N t ω} ∩ ({ω | a t ω < N} ∩
        {ω | a t ω < V ω ∧ Disjoint C (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)}) =
        {ω | a t ω < N} ∩ {ω | 0 < a t ω ∧ a t ω < V ω ∧
          Disjoint C (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, pos_capClock_iff]
      tauto
    rw [e]
    exact (measurableSet_lt (haa t) measurable_const).inter hS
  · have e : {ω | 0 < capClock a N t ω} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, pos_capClock_iff, mem_empty_iff_false, iff_false, not_and]
      exact fun _ h => hN h
    rw [e, empty_inter]
    exact @MeasurableSet.empty _ (𝓖 t)

end Cap

section Lines

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {nL nR : ℕ} {κ : ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {a : ℝ≥0 → Ω → ℝ≥0∞}

/-- **(S) with the lifetime `V` from the line data below `V`, under a strict time change**, conditioning on a
`𝓖₀`-event `M` that contains the live event `F`; the line data are asked on `M` where `0 < a t < V`. -/
theorem hasSafeLaw_life_of_lineKernelS {𝓖 𝓗' : Filtration ℝ≥0 mΩ} {F M : Set Ω} (hM : MeasurableSet[𝓖 0] M)
    (hFM : ∀ᵐ ω ∂P, ω ∈ F → ω ∈ M)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (σa k : ℝ) (hac : ∀ ω, Continuous fun t => a t ω) (ham : ∀ ω, Monotone fun t => a t ω)
    (ha0 : ∀ ω, a 0 ω = 0) (haa : ∀ t, Measurable[𝓖 t] (a t))
    (h𝓗' : ∀ q D, MeasurableSet[𝓗' q] D → ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | (q : ℝ≥0∞) < a t ω}))
    (V : Ω → ℝ≥0∞) (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < V ω → ∃ t, (q : ℝ≥0∞) ≤ a t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR V ω)
    (hregM : ∀ t, ∀ᵐ ω ∂P, ω ∈ M → 0 < a t ω → IsForceReg W VL VR V ω)
    (hS : ∀ (ψ : TestOn upperHalfPlaneOpens) t, MeasurableSet[𝓖 t]
      {ω | 0 < a t ω ∧ a t ω < V ω ∧ Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)})
    (𝒢L : ℝ≥0 → MeasurableSpace Ω) (h𝒢L : ∀ t, 𝓖 t ≤ 𝒢L t) (h𝒢Lm : ∀ t, 𝒢L t ≤ mΩ)
    (Mk : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hker : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ M → 0 < a t ω → a t ω < V ω →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢L t] ω =
        Complex.exp (Complex.I * (Mk t ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω)
            (a t ω).toNNReal)) φ φ : ℝ) : ℂ)))
    (hmean : ∀ (t : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ M → 0 < a t ω → a t ω < V ω →
      Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal) →
      Chart.chartTransport (hc ω) 1 σa k (Mk t ω) ψ =
        ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal
          (bheProc κ ρL ρR W VL VR ω (a t ω).toNNReal) z * ψ z) :
    HasSafeLaw κ ρL ρR P 𝓗' F V W VL VR fun ω => Chart.chartTransport (hc ω) 1 σa k (h ω) := by
  have hN : ∀ N : ℝ≥0, HasSafeLaw κ ρL ρR P 𝓗' F (fun ω => min (V ω) N) W VL VR
      fun ω => Chart.chartTransport (hc ω) 1 σa k (h ω) := by
    intro N
    refine hasSafeLaw_of_lineKernelS (Qc := capClock a N) hM hFM hc hdom hfwd hliftm hliftc hh σa k
      (continuous_capClock hac N) (monotone_capClock ham N) (capClock_zero ha0 N) (measurable_capClock haa N)
      (measurableSet_inter_capClockS h𝓗' N) (reach_capClock_life hreach N) ?_ ?_
      (fun ψ t => measurableSet_pos_lineSafe_capClock_life haa (hS ψ t) N) 𝒢L h𝒢L h𝒢Lm Mk ?_ ?_
    · filter_upwards [hreg] with ω hω hωF using isForceReg_mono (min_le_left _ _) (hω hωF)
    · intro t
      filter_upwards [hregM t] with ω hω hωM hpos
      exact isForceReg_mono (min_le_left _ _) (hω hωM (pos_capClock_iff.1 hpos).1)
    · intro t φ
      filter_upwards [hker t φ] with ω hω hωM hpos hlt hsupp
      obtain ⟨haN, haV⟩ := coe_capClock_lt_min_iff.1 hlt
      rw [capClock_eq_of_lt haN] at hsupp ⊢
      exact hω hωM (pos_capClock_iff.1 hpos).1 haV hsupp
    · intro t ψ
      filter_upwards [hmean t ψ] with ω hω hωM hpos hS'
      rw [lineSafe_capClock_life_eq] at hS'
      rw [capClock_eq_of_lt hS'.1]
      exact hω hωM (pos_capClock_iff.1 hpos).1 hS'.2.1 hS'.2.2
  intro ψ q D hD hDs
  refine hN (q + 1) ψ q D hD ?_
  filter_upwards [hDs] with ω h1 hωD
  obtain ⟨hF', hqV, hdis⟩ := h1 hωD
  exact ⟨hF', lt_min hqV (ENNReal.coe_lt_coe.2 (lt_add_one q)), hdis⟩

end Lines

end InteractingSLE.Theorem14.SB.Cr
