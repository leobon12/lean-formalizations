/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLawPast
import InteractingSLE.Spec.Restart.FlowCodeWord

/-!
# The flow-line word of a boundary word is Borel: `WordMeasStatement`

Packet PROVE-STAGEDLAW2. The named input `WordMeasStatement` of PROVE-STAGEDLAW (the numbers of marks and the padded
flow-line word at the seed `0` are measurable functions of the boundary word) is the restriction to the seed `0` of
PROVE-CONDDET's measurability in the word and the seed (`Restart.measurable_flowLineNL`,
`Restart.measurable_flowLineNR`, `Restart.measurable_flowPad`; `padFL κ θ c.fn c.jumps = flowPad κ θ (c, 0)` by
definition).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open Restart

/-- **`WordMeasStatement` holds.** -/
theorem wordMeasStatement : WordMeasStatement := by
  have hc : Measurable fun c : BoundaryWord => (c, (0 : ℝ)) := measurable_id.prodMk measurable_const
  have h1 := measurable_flowLineNL.comp hc
  have h2 := measurable_flowLineNR.comp hc
  refine ⟨h1, h2, fun κ θ => ?_⟩
  have h3 := (measurable_flowPad κ θ).comp hc
  exact h3

end StagedLaw

end Exist

end InteractingSLE
