import QuantumZipper.Proofs.Zipper.UnifUCIdDet
import QuantumZipper.Proofs.GFF.CoordRegRandom

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G4 A-sep via GENERIC-UC (step (b)): the fixed-parameter identity for an arbitrary measure

The identity input `hid` of the engine (`GenUC.ae_unifConv_*`) for any family of measures pushed
through a forward map `f_T⁻¹ = fwdMapInv W T` at a fixed continuous driver: for a probability
measure `ν` carried by a compact `ballH R₁ = closedBall 0 R₁ ∩ ℍ̄` and a fixed scale `j`, almost
surely

`∫ avgReg (coordChange x_ω f_T⁻¹ Q) j dν = X_ω((ν ⋆ fc(·, 2^{-j})).map f_T⁻¹) + det_j(ν)`,

with `x_ω = X_ω + (a log|·| + g₁)` (`g₁` continuous) and the deterministic part
`det_j(ν) = ∫ Dfun V T a g₁ Q (z, 2^{-j}) dν(z)`, `V` the time-reversed driver.

This is the XFLOW identity `F1.flowIdentStmt_holds` (and the D33 `RegUnif.identStmt`) with the
pushed circle replaced by an arbitrary compactly supported `ν` and the field `𝔥₀ + X` by
`a log|·| + g₁ + X`: the proof only uses that `ν` is a probability measure on a compact part of
`ℍ̄`. Sources (as there): Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math.
185 (2011), Prop. 3.1 and its proof (p. 18); the regular witness
`CoordReg.exists_regular_witness_revMap` (Kolmogorov–Čentsov, Revuz–Yor Ch. I Thm 2.1); stochastic
Fubini `CoordReg.ae_integral_Vhat_eq_gen`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G4Core

open RegCont TwoPoint CoordReg CircleFubini RegSample RegUnif FrostmanReg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The deterministic part at scale `2^{-j}` for a general measure. -/
def detGen (W : ℝ → ℝ) (T a : ℝ) (g₁ : ℂ → ℝ) (Q : ℝ) (ν : Measure ℂ) (j : ℕ) : ℝ :=
  ∫ z, Dfun (fun s => W (T - s) - W T) T a g₁ Q (z, radius j) ∂ν

end G4Core
end Thm18Asm
end QuantumZipper
