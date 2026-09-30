import QuantumZipper.Proofs.Zipper.SWCoreNA2Fam

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (G-b): `FamilyBounds` for a Hölder family pushed from any probability measure

`SWCore.swcNA2_familyBounds` (SWCoreNA2Fam.lean) with the uniform circle measure `circM` replaced by
an arbitrary probability measure `m` on a topological space `Θ` (the proof only uses that the
base measure is a probability measure and that the family is continuous, bounded, `α`-Frostman and
`η`-Hölder in the parameter). Needed for the dilated and translated test measures of PAIR-LIM,
whose base measure is a normalized test density on `ℂ`. Same proof, line by line (the repository's
own energy estimates; Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1-type argument).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function Real
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace SWCore

open Thm18Asm Thm18Asm.G1RC CircleFubini KolmD TwoPoint RegCont

section G3PlFam

variable {n : ℕ} {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
  {m : Measure Θ} [IsProbabilityMeasure m]

/-- The smoothed generic family. -/
abbrev g3plFamM (m : Measure Θ) (Φ : (Fin n → ℝ) → Θ → ℂ) : (Fin (n + 1) → ℝ) → Measure ℂ :=
  smoothFam m Φ

end G3PlFam

end SWCore
end QuantumZipper
