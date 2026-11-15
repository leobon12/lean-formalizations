/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCKerCRead
import InteractingSLE.Spec.Restart.FCKerCGlue
import InteractingSLE.Spec.Restart.FCBoxKernel

/-!
# The first canonical continuation on the physical lines (pathwise facts)

Packet PROVE-T15-FCKER3 (R82). Deterministic facts about the canonical first continuation at a physical line `t`,
on the canonical continuation event `E` (where the chart path, its capacity clock and the supplied canonical path
`γ = cGamma` with lifetime `U = cLife` are available):

* `fcCapacityClock_eq_clamp`, **`coe_fcCapacityClock_lt_cLife_iff`**: the clock at `t` is below the capacity
  lifetime iff the first path is alive at `s₀ + t`;
* **`fwdHull_eq_fillH_cPath`**: when alive, the hull of the generating driver at the clock value is the filling of
  the chart path on `[0, t]`;
* **`isFCLine_of_canon`**: the later-line chart data `IsFCLine` used by the per-cap kernels and Aux. 79's mean
  (FCKER2's "Supply `IsFCLine`").
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb.FCKerC

open Sec6 LocalSets FCAux79

section Pathwise

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω} {E : Set Ω}

/-- On `E` the concrete clock is the chart clock at the clamped physical time. -/
theorem fcCapacityClock_eq_clamp (hd : d.IsMeasGood) (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁) {ω : Ω}
    (hω : ω ∈ E) (t : ℝ≥0) :
    fcCapacityClock d E t ω = (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω)
      (min (t : ℝ≥0∞) (d.ζ₁ ω - d.s₀ ω)).toNNReal).toNNReal := by
  unfold fcCapacityClock
  rw [hs.cClock_eq hd hω]
  unfold chartClock
  rw [IsContSpec.image_cPath_clamp hω t]

theorem cLife_eq_capLife (hd : d.IsMeasGood) (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁) {ω : Ω} (hω : ω ∈ E) :
    cLife d E d.s₀ d.η₁ d.ζ₁ ω =
      capLife (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω) := by
  rw [cLife, ite_eq_left hω, hs.cClock_eq hd hω]

/-- **The clock at `t` is below the capacity lifetime iff the first path is alive at `s₀ + t`.** -/
theorem coe_fcCapacityClock_lt_cLife_iff (hd : d.IsMeasGood) (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω))
    {ω : Ω} (hω : ω ∈ E) (t : ℝ≥0) :
    (fcCapacityClock d E t ω : ℝ≥0∞) < cLife d E d.s₀ d.η₁ d.ζ₁ ω ↔
      ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω := by
  have hC := hclk ω hω
  set C := chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω) with hCdef
  set L := d.ζ₁ ω - d.s₀ ω with hLdef
  rw [fcCapacityClock_eq_clamp hd hs hω, cLife_eq_capLife hd hs hω, ← hCdef, ← hLdef, ENNReal.coe_add,
    ← lt_tsub_iff_left]
  constructor
  · intro h
    by_contra hn
    have htL : L ≤ t := not_lt.1 hn
    have hLt : L ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top htL
    rw [min_eq_right htL, capLife, ite_eq_right hLt] at h
    exact absurd h (lt_irrefl _)
  · intro htL
    rw [min_eq_left htL.le, ENNReal.toNNReal_coe]
    by_cases hLt : L = ⊤
    · rw [capLife, ite_eq_left hLt]
      exact ENNReal.coe_lt_top
    · rw [capLife, ite_eq_right hLt]
      have hle : ((L.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ L := ENNReal.coe_toNNReal_le_self
      have htL' : t < L.toNNReal := by
        rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hLt]
        exact htL
      have hlt : C t < C L.toNNReal :=
        hC.strictMonoOn (show ((t : ℝ≥0) : ℝ≥0∞) ≤ L from htL.le) hle htL'
      rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ (hC.nonneg htL.le)]
      exact (ENNReal.ofReal_lt_ofReal_iff ((hC.nonneg htL.le).trans_lt hlt)).2 hlt

/-- The clock is positive at positive live physical times. -/
theorem fcCapacityClock_pos (hd : d.IsMeasGood) (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω))
    {ω : Ω} (hω : ω ∈ E) {t : ℝ≥0} (ht : 0 < t) (hlive : ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω) :
    0 < fcCapacityClock d E t ω := by
  have hC := hclk ω hω
  have htL : (t : ℝ≥0∞) < d.ζ₁ ω - d.s₀ ω := by
    rw [lt_tsub_iff_left, ← ENNReal.coe_add]
    exact hlive
  rw [fcCapacityClock_eq_clamp hd hs hω, min_eq_left htL.le, ENNReal.toNNReal_coe]
  have h := hC.strictMonoOn (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ d.ζ₁ ω - d.s₀ ω by simp) htL.le ht
  rw [hC.zero] at h
  exact Real.toNNReal_pos.2 h

/-- **The hull of the canonical continuation at the clock value is the filling of the chart path on `[0, t]`.** -/
theorem fwdHull_eq_fillH_cPath (hd : d.IsMeasGood) (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω))
    {ω : Ω} (hω : ω ∈ E) {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {U : ℝ≥0∞}
    (hgen : IsGeneratingTrace W U γ)
    (hγ : ∀ q : ℝ≥0, (q : ℝ≥0∞) ≤ U → γ q = cGamma d E d.s₀ d.η₁ d.ζ₁ ω q) {t : ℝ≥0}
    (hlive : (fcCapacityClock d E t ω : ℝ≥0∞) < U) :
    QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal) (fcCapacityClock d E t ω) =
      fillH (cPath d E d.s₀ d.η₁ d.ζ₁ ω '' Icc 0 t) := by
  have hC := hclk ω hω
  set C := chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω) with hCdef
  set L := d.ζ₁ ω - d.s₀ ω with hLdef
  set Q := fcCapacityClock d E t ω with hQdef
  set r : ℝ≥0 := (min (t : ℝ≥0∞) L).toNNReal with hrdef
  have hrL : (r : ℝ≥0∞) ≤ L := min_le_sub (d.s₀ ω) (d.ζ₁ ω) t
  have hQ : Q = (C r).toNNReal := fcCapacityClock_eq_clamp hd hs hω t
  have hQcap : (Q : ℝ≥0∞) ≤ capLife C L := by
    rw [hQ]
    exact hC.coe_toNNReal_le_capLife hrL
  have hinv : invClock C L Q = r := by
    rw [hQ]
    exact hC.invClock_apply hrL
  have himg : γ '' Icc 0 Q = cPath d E d.s₀ d.η₁ d.ζ₁ ω '' Icc 0 t := by
    have h1 : γ '' Icc 0 Q = (fun s => cPath d E d.s₀ d.η₁ d.ζ₁ ω (invClock C L s)) '' Icc 0 Q := by
      refine image_congr fun v hv => ?_
      rw [hγ v ((ENNReal.coe_le_coe.2 hv.2).trans hlive.le)]
      simp only [cGamma, hω, ite_true]
      rw [hs.cClock_eq hd hω]
    rw [h1, RetAux79.image_invClock_Icc hC hQcap, hinv, hrdef,
      ← IsContSpec.image_cPath_clamp hω t]
  have hc : ContinuousOn (cPath d E d.s₀ d.η₁ d.ζ₁ ω) (Icc 0 t) :=
    (hs.continuous_cPath hd ω).continuousOn
  have hK := hgen.2.2 Q hlive
  rw [himg] at hK
  exact (fillH_eq_iff_isFilling_of_isClosed (isCompact_Icc.image_of_continuousOn hc).isBounded
    (isCompact_Icc.image_of_continuousOn hc).isClosed (QuantumZipper.fwdHull_mono.2 _)).1 hK

/-- **The later-line chart data of the canonical continuation** (FCKER2's "Supply `IsFCLine`"): at a positive
physical time at which the first path is alive, the canonical chart path, its driver and the clock value form the
data `IsFCLine` of the per-cap kernels and of Aux. 79's line mean. -/
theorem isFCLine_of_canon (hd : d.IsMeasGood) (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω))
    {ω : Ω} (hω : ω ∈ E) {x₁ x₂ : ℝ}
    (hp₁ : IsPathGood (d.η₁ ω) (d.ζ₁ ω) x₁) (hp₂ : IsPathGood (d.η₂ ω) (d.ζ₂ ω) x₂)
    {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {U : ℝ≥0∞} (hWc : Continuous W) (hW0 : W 0 = 0)
    (hgen : IsGeneratingTrace W U γ) (hinj : InjOn γ {s | (s : ℝ≥0∞) ≤ U})
    (hγ : ∀ q : ℝ≥0, (q : ℝ≥0∞) ≤ U → γ q = cGamma d E d.s₀ d.η₁ d.ζ₁ ω q)
    (hU : U = cLife d E d.s₀ d.η₁ d.ζ₁ ω) {t : ℝ≥0} (ht : 0 < t)
    (hlive : ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω) :
    IsFCLine d ω x₁ x₂ t W γ U (fcCapacityClock d E t ω) := by
  have hC := hclk ω hω
  set C := chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω) with hCdef
  set L := d.ζ₁ ω - d.s₀ ω with hLdef
  set Q := fcCapacityClock d E t ω with hQdef
  have htL : (t : ℝ≥0∞) ≤ L := by
    have h : (t : ℝ≥0∞) < L := by
      rw [hLdef, lt_tsub_iff_left, ← ENNReal.coe_add]
      exact hlive
    exact h.le
  have hQ : Q = (C t).toNNReal := by
    rw [hQdef, fcCapacityClock_eq_clamp hd hs hω, min_eq_left htL, ENNReal.toNNReal_coe]
  have hQcap : (Q : ℝ≥0∞) ≤ capLife C L := by
    rw [hQ]
    exact hC.coe_toNNReal_le_capLife htL
  have hinv : invClock C L Q = t := by
    rw [hQ]
    exact hC.invClock_apply htL
  have hlt : (Q : ℝ≥0∞) < U := by
    rw [hU]
    exact (coe_fcCapacityClock_lt_cLife_iff hd hs hclk hω t).2 hlive
  have hγQ : ∀ v ∈ Icc 0 Q, γ v = cPath d E d.s₀ d.η₁ d.ζ₁ ω (invClock C L v) := fun v hv => by
    rw [hγ v ((ENNReal.coe_le_coe.2 hv.2).trans hlt.le)]
    simp only [cGamma, hω, ite_true]
    rw [hs.cClock_eq hd hω]
  have hread : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ L →
      d.inv ω (cPath d E d.s₀ d.η₁ d.ζ₁ ω r) = d.η₁ ω (d.s₀ ω + r) := fun r hr => by
    have he := (hs.cPath_spec hω r).2.2.1
    rwa [contTime_of_le hr] at he
  refine ⟨hs.subset hω, hp₁, hp₂, hlive.le, hgen, hWc, hW0, hinj, hlt,
    fcCapacityClock_pos hd hs hclk hω ht hlive, ?_, ?_⟩
  · have h1 : (fun s => d.inv ω (γ s)) '' Icc 0 Q =
        (fun s => (fun r => d.inv ω (cPath d E d.s₀ d.η₁ d.ζ₁ ω r)) (invClock C L s)) '' Icc 0 Q :=
      image_congr fun v hv => by rw [hγQ v hv]
    rw [h1, RetAux79.image_invClock_Icc (Γ := fun r => d.inv ω (cPath d E d.s₀ d.η₁ d.ζ₁ ω r)) hC hQcap,
      hinv]
    have h2 : (fun r => d.inv ω (cPath d E d.s₀ d.η₁ d.ζ₁ ω r)) '' Icc 0 t =
        d.η₁ ω '' ((fun r => d.s₀ ω + r) '' Icc 0 t) := by
      rw [image_image]
      exact image_congr fun r hr => hread r ((ENNReal.coe_le_coe.2 hr.2).trans htL)
    rw [h2, Set.image_const_add_Icc, add_zero]
  · rw [hγQ Q ⟨zero_le, le_rfl⟩, hinv]
    exact hread t htL

end Pathwise

end InteractingSLE.Restart.FCPlumb.FCKerC
