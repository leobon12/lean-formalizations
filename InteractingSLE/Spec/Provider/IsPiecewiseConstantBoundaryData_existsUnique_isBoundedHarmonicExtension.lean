import InteractingSLE.Frozen.Spec.IsBoundedHarmonicExtension
import InteractingSLE.Frozen.Spec.IsPiecewiseConstantBoundaryData
import InteractingSLE.Impl.PiecewiseConstant

/-!
# Provider for the frozen anchor `InteractingSLE/Frozen/Spec/IsPiecewiseConstantBoundaryData_existsUnique_isBoundedHarmonicExtension.lean`

Quarantined while that anchor is DRAFT_SORRY: only its frozen file and audit files may import this module
(lean-orchestrator draft quarantine). Packet PROVE-T15-COMP.

## Proof
The implementation theorem `InteractingSLE.PiecewiseConstant.existsUnique_isBoundedHarmonicExtension`
(`InteractingSLE/Impl/PiecewiseConstant.lean`) has exactly the anchor's statement, stated over the
frozen (sealed) definitions `IsPiecewiseConstantBoundaryData` and `IsBoundedHarmonicExtension`.

## Binder form
The anchor's hypothesis `hb` is a named binder before the colon, and the sealed body must be the bare
`by exact <provider>`. With `hb` implicit, `exact` cannot fill it (it does not search the local
context for implicit arguments: "don't know how to synthesize implicit argument"). The provider
therefore takes `hb` as an auto-parameter `(hb : … := by assumption)`: `autoParam T _` is reducibly
`T`, so `@provider` has the anchor's type, and in the anchor body `by exact provider` fills `hb`
from the context. The data arguments `b`, `jumps` are implicit.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace InteractingSLE

namespace Spec

namespace Provider

/-- Provider of the frozen companion theorem of Theorem 1.5
(`InteractingSLE.IsPiecewiseConstantBoundaryData.existsUnique_isBoundedHarmonicExtension`), with
exactly its type (data arguments implicit, the hypothesis an auto-parameter filled by
`assumption`, so that the frozen anchor's sealed body is the bare `by exact` the checker allows). -/
theorem IsPiecewiseConstantBoundaryData_existsUnique_isBoundedHarmonicExtension {b : ℝ → ℝ}
    {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption) :
    ∃ u : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u ∧
      ∀ v : ℂ → ℝ, IsBoundedHarmonicExtension b jumps v → EqOn v u QuantumZipper.H :=
  PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb

end Provider

end Spec

end InteractingSLE
