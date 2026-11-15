/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedR80Primitive

/-!
# Exact measurability of the compensated seeded mapped driver

Packet PROVE-ZHAN-GT4-A22. Prove adaptedness of the actual map, entrance
drift primitive and Brownian continuation separately. An almost-sure
stochastic-integral identity is not used to infer exact adaptedness.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal
namespace InteractingSLE.ZhanGT4
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The exact compensated map coordinates are measurable in the original
filtration, including their unbounded entrance drift and continuation. -/
theorem measurable_seedOwnMappedNoise {𝓕 : Filtration ℝ≥0 mΩ} {n : ℕ}
    {d : Ω → SeedData n} {κ : ℝ} {S : Ω → ℝ≥0} {B : ℝ≥0 → Ω → ℝ}
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hAm : ∀ u : ℝ≥0, Measurable[𝓕 u] ({ω | u ≤ S ω}.indicator fun ω => (d ω).A 0 u))
    (hAc : ∀ ω, ContinuousOn ((d ω).A 0) (Icc 0 (S ω)))
    (hgm : ∀ u : ℝ≥0, Measurable[𝓕 u] ({ω | u ≤ S ω}.indicator fun ω => (d ω).d10Rate u))
    (hgc : ∀ ω, ContinuousOn (fun u : ℝ≥0 => (d ω).d10Rate u) (Ioc 0 (S ω)))
    (hi : ∀ ω, IntervalIntegrable (d ω).d10Rate volume 0 (S ω))
    (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hBc : ∀ ω, Continuous (B · ω)) (t : ℝ≥0) :
    Measurable[𝓕 t] (seedOwnMappedNoise κ d S B t) := by
  have hA := measurable_stopped_of_indicator hS hAm hAc
  have hA0 : Measurable[𝓕 0] (fun ω => (d ω).A 0 0) := by
    simpa only [zero_min, NNReal.coe_zero] using hA 0
  have hg := measurable_stopped_seed_primitive hS hgm hgc hi t
  have hB (u : ℝ≥0) : Measurable[𝓕 u]
      ({ω | u ≤ S ω}.indicator fun ω => B u ω) :=
    (hBm u).indicator (measurableSet_ge_of_isStoppingTime hS u)
  have hBs : Measurable[𝓕 t] fun ω => B (min t (S ω)) ω := by
    have hh := measurable_stopped_of_indicator (X := fun ω r => B r.toNNReal ω)
      hS (fun u => by simpa only [Real.toNNReal_coe] using hB u)
      (fun ω => ((hBc ω).comp continuous_real_toNNReal).continuousOn) t
    simpa only [Real.toNNReal_coe] using hh
  exact (((hA t).sub (hA0.mono (𝓕.mono bot_le) le_rfl)).sub hg).div_const _ |>.add
    ((hBm t).sub hBs)

end InteractingSLE.ZhanGT4
