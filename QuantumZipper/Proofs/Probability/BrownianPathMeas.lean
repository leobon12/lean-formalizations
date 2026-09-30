import QuantumZipper.Proofs.LQG.WedgeRestriction

/-!
# A Brownian motion has a.e.-measurable paths

AUDIT12 F12-1 (`audits/2026-09-27-fidelity/AUDIT12.md`): for `IsBrownianReal B P`, the path map
`pathOf B : Ω → (ℝ≥0 → ℝ)` (product σ-algebra on `ℝ≥0 → ℝ`) is `P`-a.e.-measurable.

Proof: `WedgeRes.exists_good_version` gives a jointly measurable `B'` with continuous paths and
`∀ᵐ ω, ∀ s, B' s ω = B s ω`; `pathOf B'` is measurable coordinatewise (`measurable_pi_iff`), and
`pathOf B =ᵐ pathOf B'`. Standard bookkeeping (own; no source needed).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **AUDIT12 F12-1.** The path map of a Brownian motion is a.e.-measurable. -/
theorem IsBrownianReal.aemeasurable_pathOf {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    AEMeasurable (pathOf B) P := by
  obtain ⟨B', hB'm, -, hB'eq⟩ := WedgeRes.exists_good_version hB
  have hm : Measurable (pathOf B') :=
    measurable_pi_iff.2 fun s => hB'm.comp (measurable_const.prodMk measurable_id)
  refine ⟨pathOf B', hm, ?_⟩
  filter_upwards [hB'eq] with ω hω
  funext s
  exact (hω s).symm

end QuantumZipper
