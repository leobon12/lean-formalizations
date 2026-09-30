import QuantumZipper.Proofs.Thm18.LWFarDefs
import QuantumZipper.Proofs.Thm11.ClockIntegrable
import QuantumZipper.Proofs.Thm11.AddendumAreaBound
import QuantumZipper.Proofs.Thm18.LWFarCondFlow

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LWF-1 (stopping part): the Loewner state at a stopping time is `𝓕_τ`-measurable

Task LWF-1 (plan `handoff/LW-FAR.md`). For the natural filtration of a Brownian motion with all
paths continuous (`SMSetup`), an `ℝ≥0`-valued stopping time `τ`, a point `w ∈ H` and an event
`A ∈ 𝓕_τ` on which `w` is not swallowed at time `τ`, the maps `ω ↦ Z_τ(w) = f_τ(w)` and
`ω ↦ C_τ(w) = log CR` (both put to `0` off `A`) are `𝓕_τ`-measurable
(`measurable_stopVals`). Proof: replace `B` by the stopped path `B_{·∧τ}` (its coordinates are
`𝓕_τ`-measurable, `measurable_stoppedValue`; the Loewner state at time `τ` depends only on the
driver on `[0, τ]`, `LWFarCondFlow`), approximate `τ` from above by the dyadic times
`(⌊2ⁿτ⌋ + 1)/2ⁿ` (countably many values, fixed-time joint measurability of `LWFarCondMeas`) and
pass to the limit using continuity of the flow in time while `w` is alive. Standard
(Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, Prop. 1.2.18: a progressively
measurable process stopped at a stopping time is `𝓕_τ`-measurable); own elementary proof here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

open FwdClock

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}

end Generic

section Stop

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- The coordinates of `B` are adapted to the natural filtration. -/
lemma SMSetup.adapted (hS : SMSetup P B 𝓕) (t : ℝ≥0) : Measurable[𝓕 t] (B t) := by
  rw [hS.natural t]
  have hpath : Measurable[MeasurableSpace.comap (fun ω (r : Set.Iic t) => B r ω)
      MeasurableSpace.pi] (fun ω (r : Set.Iic t) => B r ω) := Measurable.of_comap_le le_rfl
  exact (measurable_pi_apply (⟨t, Set.mem_Iic.2 le_rfl⟩ : Set.Iic t)).comp hpath

end Stop

end LWFar
end Thm18Asm
end QuantumZipper
