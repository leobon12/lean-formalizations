/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedEndEndpoint

/-!
# Strict endpoint versions of seeded coefficients

Packet PROVE-ZHAN-GT4-A22. Remove the single endpoint from the actual
predictable noise while retaining its adaptedness, Riemann regularity
and chosen stochastic integral.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {w B : ℝ≥0 → Ω → ℝ} {S : Ω → ℝ≥0}

/-- Zero only the value at the pathwise endpoint. -/
def seedFin2Endpoint (S : Ω → ℝ≥0) (w : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  if u = S ω then 0 else w u ω

theorem seedFin2Endpoint_adapted
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (hw : StronglyAdapted 𝓕 w) :
    StronglyAdapted 𝓕 (seedFin2Endpoint S w) := by
  intro u
  have hm : MeasurableSet[𝓕 u] {ω | u = S ω} := by
    simpa only [WithTop.coe_eq_coe, eq_comm] using hS.measurableSet_eq u
  exact (Measurable.ite hm measurable_const (hw u).measurable).stronglyMeasurable

theorem abs_seedFin2Endpoint_le {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u ω, |w u ω| ≤ C) (u : ℝ≥0) (ω : Ω) :
    |seedFin2Endpoint S w u ω| ≤ C := by
  unfold seedFin2Endpoint
  split_ifs
  · simpa only [abs_zero] using hC
  · exact hb u ω

/-- A change at one time preserves almost-everywhere left continuity. -/
theorem seedFin2Endpoint_regular (hw : IsRiemannRegular P w) :
    IsRiemannRegular P (seedFin2Endpoint S w) := by
  filter_upwards [hw] with ω hω
  filter_upwards [hω, ae_ne_real (S ω)] with r hr hne
  rcases le_or_gt r 0 with h0 | h0
  · have he : Iic r.toNNReal = {r.toNNReal} := by
      simp only [Real.toNNReal_of_nonpos h0]
      ext u
      simp only [mem_Iic, nonpos_iff_eq_zero, mem_singleton_iff]
    rw [he]
    exact continuousWithinAt_singleton
  · have hu : (r.toNNReal : ℝ) = r := Real.coe_toNNReal _ h0.le
    have hn : r.toNNReal ≠ S ω := fun he => hne (hu.symm.trans (congrArg NNReal.toReal he))
    apply hr.congr_of_eventuallyEq
    · have hopen : {u : ℝ≥0 | u ≠ S ω} ∈ 𝓝 r.toNNReal :=
        isOpen_ne.mem_nhds hn
      filter_upwards [nhdsWithin_le_nhds hopen] with u hu'
      exact ite_eq_right hu'
    · exact ite_eq_right hn

/-- The strict version has exactly the same original chosen integral. -/
theorem seed_stochIntegral_endpoint
    (hB : IsFilteredPreBrownian B 𝓕 P) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (hw : StronglyAdapted 𝓕 w)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u ω, |w u ω| ≤ C) (hr : IsRiemannRegular P w) (u : ℝ≥0) :
    stochIntegral P 𝓕 B (seedFin2Endpoint S w) u =ᵐ[P] stochIntegral P 𝓕 B w u := by
  exact seed_stochIntegral_eq_of_endpoint hB hBc (seedFin2Endpoint_adapted hS hw) hw
    (abs_seedFin2Endpoint_le hC hb) hb (seedFin2Endpoint_regular hr) hr
    (fun ω t ht => ite_eq_right ht) u

end InteractingSLE.ZhanGT4
