/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedImageDoleans

/-!
# Seeded Girsanov in the original filtration

Packet PROVE-ZHAN-GT4-A22. Use the landed general-filtration theorem,
including its Lévy characterization, and the actual normalized density.
The only remaining calculus input is `SeedPositiveLogIto`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Seeded Girsanov with the full filtered-Brownian conclusion and an
equivalent probability measure. Predictability and boundedness can be
supplied by `exists_seedNoise_prepared_right`. -/
theorem seed_girsanov_of_positiveIto {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsFilteredBrownianReal 𝓕 B P) {κ : ℝ} {d : Ω → SeedData n} {S : Ω → ℝ≥0}
    (hpred : IsStronglyPredictable 𝓕 (seedNoise κ d S)) {C : ℝ}
    (hb : ∀ u ω, |seedNoise κ d S u ω| ≤ C)
    (hreg : Girsanov.IsRiemannRegular P (seedNoise κ d S))
    (hc : ∀ ω, ContinuousOn (d ω).normEll (Icc 0 (S ω)))
    (hIto : SeedPositiveLogIto P 𝓕 B (seedNoise κ d S) d S)
    {U : ℝ≥0} (hSU : ∀ ω, S ω < U) :
    IsFilteredBrownianReal 𝓕 (Girsanov.girsanovProcess B (seedNoise κ d S)) (seedMeasure P d S) ∧
      MathFin.IsEquivProbMeasure P (seedMeasure P d S) := by
  have hpre := Girsanov.isFilteredPreBrownian_of_isFilteredBrownianReal hB
  have hθ := hpred.isStronglyProgressive
  have hZ := seedDensity_eq_doleans_of_positiveIto hpre hθ hb hreg hc hIto (fun ω => (hSU ω).le)
  have hQ : seedMeasure P d S = Girsanov.girsanovMeasure P 𝓕 B (seedNoise κ d S) U :=
    withDensity_congr_ae (hZ.mono fun _ he => congrArg ENNReal.ofReal he)
  have htail : ∀ u ω, U ≤ u → seedNoise κ d S u ω = 0 := fun u ω hu =>
    (seedNoise_coordinate κ d S).2 ω u ((hSU ω).trans_le hu)
  rw [hQ]
  have : IsFilteredPreBrownian B 𝓕 P := hpre
  exact ⟨Girsanov.isFilteredBrownianReal_girsanov hB hθ hb hreg htail,
    Girsanov.isEquivProbMeasure_girsanovMeasure hθ.stronglyAdapted hb hreg U⟩

/-- Under the constructed change of Brownian coordinate, the original
force drift becomes exactly the image-chart logarithmic drift. -/
theorem seedNoise_drift_eq_dualQ {n : ℕ} {κ : ℝ} {d : Ω → SeedData n} {S : Ω → ℝ≥0}
    (hκ : 0 ≤ κ) (hdκ : ∀ ω, (d ω).κ = κ) (ω : Ω) {u : ℝ≥0}
    (hu : 0 < u) (huS : u ≤ S ω) :
    (d ω).drift u - Real.sqrt κ * seedNoise κ d S u ω =
      κ * dualQ κ ((d ω).A 1 u) ((d ω).A 2 u) ((d ω).A 0 u - (d ω).A20 u)
        (d ω).r (fun m => (d ω).A 0 u - (d ω).B0 u m) :=
  (seedNoise_coordinate κ d S).drift_eq_dualQ hκ hdκ ω hu huS

end InteractingSLE.ZhanGT4
