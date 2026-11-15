/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin2Protected

/-!
# The actual finite-variation coordinate after seeded Girsanov

Packet PROVE-ZHAN-GT4-A22. Keep the original driver and replace its
Brownian coordinate by the constructed Girsanov process. The remaining
offset has exactly the image-logarithm drift. This proves the drift part
of the mapped-driver calculation; the random-field Itô formula for the
reflected map is still needed for its stochastic-integral identity.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The finite-variation offset when the Brownian coordinate is changed. -/
def seedImageOffset (σ : ℝ) (D θ : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  D u ω - σ * Girsanov.drift θ u ω

/-- The Brownian change and the new offset preserve the actual driver. -/
theorem seed_driver_girsanov_eq (σ : ℝ) (B D θ : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    driftDriver σ (Girsanov.girsanovProcess B θ) (seedImageOffset σ D θ) ω =
      driftDriver σ B D ω := by
  funext t
  simp only [driftDriver, Girsanov.girsanovProcess, seedImageOffset]
  ring

/-- The new offset is adapted in the original filtration. -/
theorem seedImageOffset_adapted {𝓕 : Filtration ℝ≥0 mΩ} {σ : ℝ}
    {D θ : ℝ≥0 → Ω → ℝ} (hD : ∀ u, Measurable[𝓕 u] (D u))
    (hp : IsStronglyProgressive 𝓕 θ) (u : ℝ≥0) :
    Measurable[𝓕 u] (seedImageOffset σ D θ u) :=
  (hD u).sub ((Girsanov.stronglyMeasurable_integral_comp hp measurable_id u).measurable.const_mul σ)

/-- A bounded progressive noise gives a continuous offset, including zero. -/
theorem continuous_seedImageOffset {𝓕 : Filtration ℝ≥0 mΩ} {σ : ℝ}
    {D θ : ℝ≥0 → Ω → ℝ} (hD : ∀ ω, Continuous (D · ω))
    (hp : IsStronglyProgressive 𝓕 θ) {C : ℝ} (hb : ∀ u ω, |θ u ω| ≤ C) (ω : Ω) :
    Continuous (seedImageOffset σ D θ · ω) :=
  (hD ω).sub ((Girsanov.continuous_drift hp hb ω).const_mul σ)

/-- The primitive of bounded progressive noise has the expected positive
time derivative, also within the interval at its right endpoint. -/
theorem hasDerivWithinAt_seed_drift_pos {𝓕 : Filtration ℝ≥0 mΩ}
    {θ : ℝ≥0 → Ω → ℝ} (hp : IsStronglyProgressive 𝓕 θ)
    {C : ℝ} (hb : ∀ u ω, |θ u ω| ≤ C) {S : Ω → ℝ≥0}
    (hc : ∀ ω, ContinuousOn (fun u : ℝ => θ u.toNNReal ω) (Ioc 0 (S ω)))
    (ω : Ω) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) (S ω)) :
    HasDerivWithinAt (fun u : ℝ => Girsanov.drift θ u.toNNReal ω)
      (θ t.toNNReal ω) (Ioc 0 (S ω)) t := by
  have hnh : Ioc (0 : ℝ) (S ω) ∈ 𝓝[Icc 0 (S ω)] t := by
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds ht.1), self_mem_nhdsWithin] with u hu huS
    exact ⟨hu, huS.2⟩
  have hct := (hc ω t ht).mono_of_mem_nhdsWithin hnh
  have : Fact (t ∈ Icc (0 : ℝ) (S ω)) := ⟨Ioc_subset_Icc_self ht⟩
  have hinter : Ioi (0 : ℝ) ∩ Icc 0 (S ω : ℝ) = Ioc 0 (S ω : ℝ) := by
    ext u
    exact ⟨fun hu => ⟨hu.1, hu.2.2⟩, fun hu => ⟨hu.1, hu.1.le, hu.2⟩⟩
  have hEq := nhdsWithin_inter_of_mem
    (nhdsWithin_le_nhds (Ioi_mem_nhds ht.1) : Ioi (0 : ℝ) ∈ 𝓝[Icc 0 (S ω)] t)
  rw [hinter] at hEq
  have hm := (hc ω).stronglyMeasurableAtFilter_nhdsWithin (μ := volume) measurableSet_Ioc t
  rw [hEq] at hm
  have hd := intervalIntegral.integral_hasDerivWithinAt_right (s := Icc 0 (S ω))
    (Girsanov.intervalIntegrable_time hp hb ω 0 t) hm hct
  have he : (fun u : ℝ => Girsanov.drift θ u.toNNReal ω) =ᶠ[𝓝[Ioc 0 (S ω)] t]
      fun u => ∫ v in (0 : ℝ)..u, θ v.toNNReal ω := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp only [Girsanov.drift, Real.coe_toNNReal _ hu.1.le]
  apply (hd.mono Ioc_subset_Icc_self).congr_of_eventuallyEq he
  simp only [Girsanov.drift, Real.coe_toNNReal _ ht.1.le]

/-- Positive-time evolution of the actual offset after seeded Girsanov.
The result includes the D10 generator cancellation at the mapped driver. -/
theorem seedImageOffset_deriv_and_d10 {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} (hκ : 0 < κ)
    {n : ℕ} {d : Ω → SeedData n} {S : Ω → ℝ≥0} {D : ℝ≥0 → Ω → ℝ}
    (hdκ : ∀ ω, (d ω).κ = κ)
    (hp : IsStronglyProgressive 𝓕 (seedNoise κ d S))
    {C : ℝ} (hb : ∀ u ω, |seedNoise κ d S u ω| ≤ C)
    (hc : ∀ ω, ContinuousOn (fun u : ℝ => seedNoise κ d S u.toNNReal ω) (Ioc 0 (S ω)))
    (hD : ∀ ω t, t ∈ Ioc (0 : ℝ) (S ω) → HasDerivWithinAt
      (fun u : ℝ => D u.toNNReal ω) ((d ω).drift t) (Ioc 0 (S ω)) t)
    (ω : Ω) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) (S ω)) (hA : (d ω).A 1 t ≠ 0) :
    let b := (d ω).drift t - Real.sqrt κ * seedNoise κ d S t.toNNReal ω
    HasDerivWithinAt
      (fun u : ℝ => seedImageOffset (Real.sqrt κ) D (seedNoise κ d S) u.toNNReal ω)
      b (Ioc 0 (S ω)) t ∧
      -3 * (d ω).A 2 t + κ / 2 * (d ω).A 2 t + b * (d ω).A 1 t = (d ω).d10Rate t := by
  dsimp only
  refine ⟨(hD ω t ht).sub ((hasDerivWithinAt_seed_drift_pos hp hb hc ω ht).const_mul _), ?_⟩
  have hnoise : seedNoise κ d S t.toNNReal ω =
      -Real.sqrt κ * (d ω).ellX t ((d ω).W t) := by
    have hh := (seedNoise_coordinate κ d S).1 ω t.toNNReal (Real.toNNReal_pos.2 ht.1)
      (Real.toNNReal_le_iff_le_coe.2 ht.2)
    simpa only [Real.coe_toNNReal _ ht.1.le] using hh
  rw [hnoise]
  have he : (d ω).drift t - Real.sqrt κ * (-Real.sqrt κ * (d ω).ellX t ((d ω).W t)) =
      (d ω).drift t + κ * (d ω).ellX t ((d ω).W t) := by
    calc _ = (d ω).drift t + (Real.sqrt κ) ^ 2 * (d ω).ellX t ((d ω).W t) := by ring
         _ = _ := by rw [Real.sq_sqrt hκ.le]
  rw [he]
  simpa only [hdκ ω] using (d ω).d10_drift (by rw [hdκ ω]; exact hκ.ne') hA

end InteractingSLE.ZhanGT4
