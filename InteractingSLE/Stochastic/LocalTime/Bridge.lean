/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.IsFilteredBrownianReal
import BrownianMotion.Gaussian.BrownianMotion

/-!
# From the project's filtered Brownian motion to MathFin's

Packet PROVE-TANAKA. The theorems of `InteractingSLE.Stochastic.LocalTime` take the vendored class
`ProbabilityTheory.IsFilteredPreBrownian B 𝓕 P` (pre-Brownian law, strongly adapted, increments
independent of the past), which is also what MathFin's Lévy characterization produces. The
frozen definition `InteractingSLE.IsFilteredBrownianReal 𝓕 B P` (Brownian law with a.s. continuous
paths, adapted, independent increments) implies it.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.LocalTime

lemma isFilteredPreBrownian_of_isFilteredBrownianReal {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
    (h : IsFilteredBrownianReal 𝓕 B P) : IsFilteredPreBrownian B 𝓕 P where
  toIsPreBrownianReal := h.1.toIsPreBrownianReal
  stronglyAdapted := h.2.1.stronglyAdapted
  indep := h.2.2

end InteractingSLE.LocalTime
