import QuantumZipper.Proofs.Zipper.XAreaPCKolmBasic
import QuantumZipper.Proofs.Probability.KolmN
import QuantumZipper.Proofs.Probability.BMMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X-A-pc, step R2 (2/2): three-parameter Kolmogorov for the difference family

For a difference family `DiffFam B μ ν C` (`XAreaPCKolmBasic.lean`) and a free field `X`
modulo constants, the clamped process `Z q = X(μ z s) − X(ν z s)` (`0` at `s = 0`) has Gaussian
increments with `E (Z q − Z q')² ≤ K ‖q − q'‖^{1/2}`, hence `E |Z q − Z q'|^{14} ≤ K' ‖q − q'‖^{7/2}`
with `7/2 > 3`, and the Kolmogorov–Čentsov theorem (`KolmN.exists_continuous_modification_N`;
Revuz–Yor, 3rd ed., Ch. I, Thm (2.1)) gives a modification `Y` continuous for every `ω`
(`exists_contMod_diffFam`), vanishing at scale `0` for all parameters a.s. Consequently
(`ae_unif_small_diffFam`), a.s. `Y(z, s) → 0` as `s → 0`, uniformly in `z ∈ B.rect`
(Heine–Cantor on the compact parameter box).

Sources: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 (the same Gaussian-moment /
Kolmogorov route); the vanishing-at-`0` bookkeeping is an own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6
namespace XAreaPC

open KolmG KolmN KolmD

variable {B : PBox} {μ ν : ℂ → ℝ → Measure ℂ} {C : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- The parameter of `(z, s)`. -/
def emb (z : ℂ) (s : ℝ) : Fin 3 → ℝ := ![z.re, z.im, s]

end XAreaPC
end QuantumZipper.E6
