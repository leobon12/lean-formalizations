/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofResidualDriver
import InteractingSLE.Spec.Restart.FCThresholdDriverAEMeas

/-!
# Inverse clocks using only the current physical prefix

Packet PROVE-RETPLUMB. Truncate both the clock and its physical domain at the
observed line. The inverse agrees with the full inverse at every capacity
already reached. The truncated lifetime is observable at the current line.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open Supp7

/-- Restricting a clock to the current physical line preserves its clock axioms. -/
theorem isClockOn_min {C : ℝ≥0 → ℝ} {L : ℝ≥0∞} (hC : IsClockOn C L) (t : ℝ≥0) :
    IsClockOn (fun s => C (min s t)) (min L (t : ℝ≥0∞)) := by
  have hle (s : ℝ≥0) (hs : (s : ℝ≥0∞) ≤ min L (t : ℝ≥0∞)) : s ≤ t :=
    ENNReal.coe_le_coe.1 (hs.trans (min_le_right _ _))
  refine ⟨by simpa using hC.zero, ?_, ?_, ?_⟩
  · intro s hs v hv hsv
    change (s : ℝ≥0∞) ≤ min L (t : ℝ≥0∞) at hs
    change (v : ℝ≥0∞) ≤ min L (t : ℝ≥0∞) at hv
    dsimp only
    rw [min_eq_left (hle s hs), min_eq_left (hle v hv)]
    exact hC.strictMonoOn (hs.trans (min_le_left _ _)) (hv.trans (min_le_left _ _)) hsv
  · apply (hC.continuousOn.mono (fun s hs =>
      (show (s : ℝ≥0∞) ≤ min L (t : ℝ≥0∞) from hs).trans (min_le_left _ _))).congr
    intro s hs
    dsimp only
    rw [min_eq_left (hle s hs)]
  · intro ht
    exact False.elim ((ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right L (t : ℝ≥0∞))) ht)

/-- A capacity already reached at `t` has the same inverse in the truncated clock. -/
theorem invClock_min_eq {C : ℝ≥0 → ℝ} {L : ℝ≥0∞} (hC : IsClockOn C L)
    {q t : ℝ≥0} (hq : (q : ℝ≥0∞) ≤ capLife C L)
    (hqt : (q : ℝ) ≤ C t) :
    invClock (fun s => C (min s t)) (min L (t : ℝ≥0∞)) q = invClock C L q ∧
      invClock C L q ≤ t := by
  obtain ⟨hrL, hrq⟩ := hC.invClock_spec hq
  have hrt : invClock C L q ≤ t := by
    by_contra h
    have htr := lt_of_not_ge h
    have htL := (ENNReal.coe_le_coe.2 htr.le).trans hrL
    exact (not_lt_of_ge hqt) (hrq ▸ hC.strictMonoOn htL hrL htr)
  refine ⟨?_, hrt⟩
  have hr := (isClockOn_min hC t).invClock_apply
    (le_min hrL (ENNReal.coe_le_coe.2 hrt))
  simpa only [min_eq_left hrt, hrq, Real.toNNReal_coe] using hr

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The countable-supremum inverse is measurable from its clock coordinates
and truncated physical lifetime. No regularity assumption is used here. -/
theorem measurable_invClock_of_coordinates {C : Ω → ℝ≥0 → ℝ} {L : Ω → ℝ≥0∞}
    (hm : ∀ s, Measurable fun ω => C ω s) (hL : Measurable L) (q : ℝ≥0) :
    Measurable fun ω => invClock (C ω) (L ω) q := by
  classical
  refine Measurable.iSup fun s : ℚ => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (MeasurableSet.const _).inter ((measurableSet_le measurable_const hL).inter
    (measurableSet_lt (hm _) measurable_const))

/-- Jointly evaluating a continuous coordinate-measurable path at a measurable
time is measurable. This adapter keeps the random-curve parameters abstract. -/
theorem measurable_eval_of_continuous_coordinates {Γ : Ω → ℝ≥0 → ℂ}
    (hc : ∀ ω, Continuous (Γ ω)) (hm : ∀ s, Measurable fun ω => Γ ω s)
    {τ : Ω → ℝ≥0} (hτ : Measurable τ) : Measurable fun ω => Γ ω (τ ω) := by
  have hj := measurable_uncurry_of_continuous_of_measurable (u := fun s ω => Γ ω s) hc hm
  exact hj.comp (hτ.prodMk measurable_id)

omit [MeasurableSpace Ω] in
/-- Reading a driver uses only the trace through the requested capacity. -/
theorem fcReadDriver_congr_prefix {Γ Δ : Ω → ℝ≥0 → ℂ} {ω : Ω} {q : ℝ≥0}
    (he : ∀ s ≤ q, Γ ω s = Δ ω s) :
    FCPlumb.fcReadDriver Γ q ω = FCPlumb.fcReadDriver Δ q ω := by
  classical
  have hm (s : ℝ≥0) (hs : s ≤ q) (z : ℂ) :
      FCPlumb.fcPrefixMap Γ s z ω = FCPlumb.fcPrefixMap Δ s z ω := by
    have hi : Γ ω '' Icc 0 s = Δ ω '' Icc 0 s :=
      image_congr fun v hv => he v (hv.2.trans hs)
    by_cases hz : z ∈ QuantumZipper.H \ fillH (Γ ω '' Icc 0 s)
    · have hz' : z ∈ QuantumZipper.H \ fillH (Δ ω '' Icc 0 s) := hi ▸ hz
      unfold FCPlumb.fcPrefixMap
      rw [indicator_of_mem (show ω ∈ {ω | z ∈ QuantumZipper.H \ fillH (Γ ω '' Icc 0 s)} from hz),
        indicator_of_mem (show ω ∈ {ω | z ∈ QuantumZipper.H \ fillH (Δ ω '' Icc 0 s)} from hz'), hi]
    · have hz' : z ∉ QuantumZipper.H \ fillH (Δ ω '' Icc 0 s) := hi ▸ hz
      unfold FCPlumb.fcPrefixMap
      rw [indicator_of_notMem (show ω ∉ {ω | z ∈ QuantumZipper.H \ fillH (Γ ω '' Icc 0 s)} from hz),
        indicator_of_notMem (show ω ∉ {ω | z ∈ QuantumZipper.H \ fillH (Δ ω '' Icc 0 s)} from hz')]
  unfold FCPlumb.fcReadDriver
  by_cases hq : q = 0
  · simp only [hq, ite_true]
  · simp only [hq, ite_false]
    congr 1
    funext N
    congr 1
    funext k
    rw [hm q le_rfl, hm _ (Real.toNNReal_le_iff_le_coe.2 (sub_le_self _ (by positivity))) ]

end InteractingSLE.Restart.RetAux79
