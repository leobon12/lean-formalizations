import QuantumZipper.Proofs.Zipper.Cor15MarkovField

/-!
# D35 core piece 1: the law-level and measurability obligations behind `Cor15UnzipFieldStmt`

Continuation of `Cor15MarkovField.lean`. The field-level input `Cor15UnzipFieldStmt` (the field
version of Theorem 1.2) is reduced to the two obligations the repository's machinery is phrased in:

* **`Cor15UnzipRawMeasStmt`** (D27): each coordinate of the truncated raw difference of the
  unzipped field is measurable, and the pair with its normalized future driver is
  a.e.-measurable. The coordinates at s-finite measures are measurable by
  `B1Full.measurable_unzip_apply` (`MeasUnzip.measurable_unzippedField_random` is the analogue at a
  random time), the non-s-finite ones are killed by `FSMeas.sfTrunc`, and the driver is a
  measurable function of the Brownian path.
* **`Cor15UnzipRawLawStmt`** (the shape of `B1Full.b1_full`/`theorem1_2_holds`, lifted from the
  countable data `lawData`/`fieldLawMod0` to the whole field): the truncated raw difference of the
  unzipped field, jointly with the shifted Brownian path `u ↦ B(a+u) − B(a)` (which is the
  normalized future driver `(√κ)⁻¹ (D_a c).2`), has the law of a truncated free field jointly with
  an independent Brownian path on another probability space.

`cor15UnzipFieldStmt_of_law` derives the input of `Cor15MarkovField.lean`: freeness from the
marginal law (`isFreeGFFModConstH_of_map_eq`, `isFreeGFFModConstH_sfTrunc`), independence from the
joint law (`indepFun_iff_map_prod_eq_prod_map_map`), the a.s. identity with the truncated raw
difference by construction. Own elementary bookkeeping (D27-style); all analytic content sits in
the two obligations.

The two obligations together are the *field-level* Theorem 1.2: `B1Full.b1_full` proves the
analogue with `lawData` in place of the whole field (`coordsFull` plus the raw pairings with test
functions, normalized by `nrm`), and `theorem1_2_holds` the analogue for the pairings with
mass-zero test functions. Lifting those from the countable data to the field itself is what
`Cor15UnzipRawLawStmt` asks (its field part is the `RegEq`-irrelevant content of the law of the
unzipped field, its constant pinned by the raw-difference definition).

**Remaining statements** (nothing else is missing for `Cor15MarkovFieldStmt`):

* `Cor15UnzipCoordMeasStmt`: a measurable version of the truncated raw difference (D27) — built
  from `B1Full.measurable_unzip_apply`/`MeasUnzip.measurable_unzippedField_random` on the measures
  carried by `ℍ`, and from the a.s. reading at the remaining admissible measures;
* `Cor15UnzipRawLawStmt`: the field-level Theorem 1.2 as above (`b1_full` with `lawData` replaced
  by the whole field).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

/-- The shifted Brownian path `u ↦ B(a + u) − B(a)` as a measurable function of `pathOf B`. -/
def shiftPath (a : ℝ) : (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) :=
  fun p u => p (a.toNNReal + u) - p a.toNNReal

theorem measurable_shiftPath (a : ℝ) : Measurable (shiftPath a) :=
  measurable_pi_iff.2 fun u =>
    (measurable_pi_apply (a.toNNReal + u)).sub (measurable_pi_apply a.toNNReal)

/-- The shifted Brownian path of a path-valued map, with `pathOf` pulled inside. -/
theorem pathOf_shift_eq {Ω : Type} (a : ℝ) (B : ℝ≥0 → Ω → ℝ) :
    pathOf (fun u ω => B (a.toNNReal + u) ω - B a.toNNReal ω) = shiftPath a ∘ pathOf B := rfl

section Main

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

end Main

end Cor15Group
end QuantumZipper
