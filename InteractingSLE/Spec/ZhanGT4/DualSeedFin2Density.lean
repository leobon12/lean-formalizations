/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin2Girsanov

/-!
# The actual seeded density process

Packet PROVE-ZHAN-GT4-A22. Identify the normalized stopped density at
every time with the Doléans martingale. Adaptedness is proved for the
actual density, so an almost-everywhere identity does not substitute for
measurability. These processes supply the finite-column construction.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The actual normalized density, stopped at the protected horizon. -/
def seedDensityProcess {n : ℕ} (d : Ω → SeedData n) (S : Ω → ℝ≥0)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp ((d ω).normEll (min t (S ω)) - (d ω).normEll 0)

/-- The density starts at one for every path. -/
theorem seedDensityProcess_zero {n : ℕ} (d : Ω → SeedData n) (S : Ω → ℝ≥0) (ω : Ω) :
    seedDensityProcess d S 0 ω = 1 := by
  simp only [seedDensityProcess, NNReal.coe_zero, min_eq_left (S ω).coe_nonneg, sub_self, Real.exp_zero]

/-- The density at a time after the horizon is the terminal seeded density. -/
theorem seedDensityProcess_eq_terminal {n : ℕ} {d : Ω → SeedData n} {S : Ω → ℝ≥0}
    {t : ℝ≥0} {ω : Ω} (ht : S ω ≤ t) : seedDensityProcess d S t ω = seedDensity d S ω := by
  simp only [seedDensityProcess, min_eq_right (show (S ω : ℝ) ≤ t from ht), seedDensity]

/-- Continuity includes the seed entrance and the stopping horizon. -/
theorem continuous_seedDensityProcess {n : ℕ} {d : Ω → SeedData n} {S : Ω → ℝ≥0}
    (hc : ∀ ω, ContinuousOn (d ω).normEll (Icc 0 (S ω))) (ω : Ω) :
    Continuous (seedDensityProcess d S · ω) :=
  Real.continuous_exp.comp ((continuous_stopped_of_continuousOn hc ω).sub continuous_const)

/-- Alive-coordinate measurability gives adaptedness of the normalized process. -/
theorem seedDensityProcess_adapted {n : ℕ} {𝓕 : Filtration ℝ≥0 mΩ}
    {d : Ω → SeedData n} {S : Ω → ℝ≥0}
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hm : ∀ u : ℝ≥0,
      Measurable[𝓕 u] ({ω | u ≤ S ω}.indicator fun ω => (d ω).normEll u))
    (hc : ∀ ω, ContinuousOn (d ω).normEll (Icc 0 (S ω))) :
    StronglyAdapted 𝓕 (seedDensityProcess d S) := by
  have h0 : Measurable[𝓕 0] (fun ω => (d ω).normEll 0) := by
    simpa only [zero_le, Set.ofPred_true, Set.indicator_univ, NNReal.coe_zero] using hm 0
  intro u
  exact ((measurable_stopped_of_indicator hS hm hc u).sub
    (h0.mono (𝓕.mono (zero_le (a := u))) le_rfl)).exp.stronglyMeasurable

/-- Positive-time Itô and the proved entrance limit identify every time
of the actual density with the chosen Doléans process. -/
theorem seedDensityProcess_eq_doleans_of_positiveIto {n : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {B θ : ℝ≥0 → Ω → ℝ}
    (hB : IsFilteredPreBrownian B 𝓕 P) (hp : IsStronglyProgressive 𝓕 θ)
    {C : ℝ} (hb : ∀ u ω, |θ u ω| ≤ C) (hr : Girsanov.IsRiemannRegular P θ)
    {d : Ω → SeedData n} {S : Ω → ℝ≥0}
    (hc : ∀ ω, ContinuousOn (d ω).normEll (Icc 0 (S ω)))
    (hi : SeedPositiveLogIto P 𝓕 B θ d S) (u : ℝ≥0) :
    seedDensityProcess d S u =ᵐ[P] Girsanov.doleansDensity P 𝓕 B θ u := by
  filter_upwards [seed_log_doleans_ae_of_positiveIto hB hp hb hr hc hi u] with ω hω
  exact congrArg Real.exp hω

/-- The actual seeded density is a martingale in the original filtration. -/
theorem martingale_seedDensityProcess_of_positiveIto {n : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {B θ : ℝ≥0 → Ω → ℝ}
    (hB : IsFilteredPreBrownian B 𝓕 P) (hp : IsStronglyProgressive 𝓕 θ)
    {C : ℝ} (hb : ∀ u ω, |θ u ω| ≤ C) (hr : Girsanov.IsRiemannRegular P θ)
    {d : Ω → SeedData n} {S : Ω → ℝ≥0}
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hm : ∀ u : ℝ≥0,
      Measurable[𝓕 u] ({ω | u ≤ S ω}.indicator fun ω => (d ω).normEll u))
    (hc : ∀ ω, ContinuousOn (d ω).normEll (Icc 0 (S ω)))
    (hi : SeedPositiveLogIto P 𝓕 B θ d S) :
    Martingale (seedDensityProcess d S) 𝓕 P := by
  have : IsFilteredPreBrownian B 𝓕 P := hB
  apply (Girsanov.martingale_doleansDensity (B := B) hp hb hr).congr (seedDensityProcess_adapted hS hm hc)
  exact fun u => (seedDensityProcess_eq_doleans_of_positiveIto hB hp hb hr hc hi u).symm

end InteractingSLE.ZhanGT4
