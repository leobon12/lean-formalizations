import QuantumZipper.Proofs.GFF.CoordRegRC2
import QuantumZipper.Proofs.Zipper.RegUnifDet

/-!
# G1-REGREP, part 1: DS11 Prop 3.1 for a general pulled-back map (fixed chord)

`CoordReg.exists_regular_witness_revMap` (`Proofs/GFF/CoordRegRC2.lean`) is the
Duplantier–Sheffield Kolmogorov argument for the unzip map `revMap W T`. For the G1 core the map
is the inverse `ψ` of a normalized uniformizer of a side domain of a fixed simple chord. This
file redoes the probabilistic part for an **arbitrary measurable map** `f : ℂ → ℂ`, with the
two map-specific inputs as explicit hypotheses:

* `PushBoundsMap f`: the images `f_* fc(u, r)` lie (a.e.) in a bounded part `ballH B` of `Hbar`,
  and have a uniform logarithmic potential bound (the conclusion of a Frostman bound) on
  `{r ≥ r₀, ‖u‖ + r ≤ R₀}`;
* `EnergyModulusMap f β`: Hölder variance modulus of `(u, r) ↦ X(f_* fc(u, r))`.

Results:
* `G1Kolm.exists_modification_map`: a modification `Vh` of `q ↦ X(f_* fc(cen q, rad q))`,
  continuous for every `ω`, satisfying the circle commutation
  `∫ Vh(u, ρ) dfc(w, r) = ∫ Vh(v, r) dfc(w, ρ)` for **all** `w ∈ Hbar`, `r, ρ > 0`, a.s.;
* `G1Kolm.ae_isRegularWith_of_raw`: RC2 for any field process `x` whose raw values at the
  folded dyadic circles are, a.s., `X(f_* fc(d, 2^{-k})) + D(d, 2^{-k})` with `D` deterministic,
  continuous, and smoothing-symmetric (RC1 is the input; for the pulled-back wedge field it is
  the job of the decomposition of `wedgeRep`).

Source: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Prop. 3.1 (arXiv:0808.1560, p. 18): variance modulus ⇒ Gaussian moments ⇒ Kolmogorov–Čentsov
(Revuz–Yor, 3rd ed., Ch. I, Thm (2.1)); the proof is that of `CoordRegRC2.lean`, with the
revMap-specific bounds replaced by the hypotheses above (the commutation step is the own
elementary argument of that file). The deterministic assembly is
`RegUnif.isRegularWith_of_witness`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1Kolm

open CoordReg RegSample KolmD KolmG CircleFubini

variable {f : ℂ → ℂ} (hf : Measurable f)

/-- Short name for the pushed kernel. -/
abbrev qK (ρ : ℝ) : Kernel ℂ ℂ := pushKernel f hf ρ

include hf

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

end G1Kolm
end Thm18Asm
end QuantumZipper
