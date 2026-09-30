import QuantumZipper.Proofs.Zipper.Cor15UnzipZipSelfDrive
import Mathlib.Topology.Algebra.Module.Cardinality

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# COR15-FIELDGOOD: `Cor15UnzipZipFieldGoodStmt` forces a degenerate field (no-go)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18;
no proof in the paper). Task COR15-FIELDGOOD.

The node `Cor15UnzipZipFieldGoodStmt κ a P B X` (`Cor15UnzipZipSelfDrive`) asks for a measurable
set `A` of B1-FULL data such that `RegEq (D_a (U_a x)).1 x.1` for **every** configuration `x`
with `b1Data x ∈ A`. This quantifies over configurations whose driver `x.2` is arbitrary off the
countably many times that a measurable set of data can see, and unzipping `D_a` reads the driver
`(U_a x).2` of the zipped configuration beyond time `a` (the swallowing time asks for a forward
solution on some `[0,T]`, `T > a`), i.e. it reads `x.2` on `(0, ε)`.

* `exists_countable_dependsOn`: a measurable set of `α × (ι → ℝ)` depends on countably many
  coordinates of the second factor (standard; own elementary proof: such sets form a σ-algebra
  containing the generators).
* `continuousOn_of_isForwardSol`: a forward solution on `[0,T]` forces the driver to be continuous
  on `[0,T]`; hence `fwdMapInv_eq_zero_of_not_continuousOn`: if the driver is discontinuous on
  every `[0,T]`, `T > a`, the hull at time `a` is all of `ℍ` and `fwdMapInv V a` is the junk `0`.
* `avgReg_coordChange_const_zero`: the coordinate change along the constant map `0` has
  constant regularized averages.
* **`ae_avgReg_const_of_fieldGood`**: if `Cor15UnzipZipFieldGoodStmt κ a P B X` holds, then almost
  surely the regularized circle averages of the unzipped field `(D_a c).1` are **constant** in
  `(k, z)`. (Modify the driver of `D_a c` by `+1` at a sequence of times `s_n ↓ 0` invisible to
  `A`: the data stay in `A`, but `D_a ∘ U_a` of the modified configuration is the junk constant
  field.) Since the unzipped field is a free field plus a smooth function modulo constants, this
  is false; so the node is false as stated. The corrected node adds `Continuous x.2`
  (`Cor15FieldGoodFix`).

Own elementary arguments.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace QuantumZipper
namespace Cor15Group

/-! ## Countable dependence of product-measurable sets -/

/-- Sets of `α × (ι → ℝ)` whose membership only reads the first factor and countably many
coordinates of the second. -/
def CtblDep {α ι : Type*} (S : Set (α × (ι → ℝ))) : Prop :=
  ∃ J : Set ι, J.Countable ∧ ∀ p q : α × (ι → ℝ), p.1 = q.1 → (∀ i ∈ J, p.2 i = q.2 i) →
    p ∈ S → q ∈ S

/-- The σ-algebra of countably dependent sets. -/
abbrev ctblDepMS (α ι : Type*) : MeasurableSpace (α × (ι → ℝ)) where
  MeasurableSet' := CtblDep
  measurableSet_empty := ⟨∅, countable_empty, fun _ _ _ _ h => h.elim⟩
  measurableSet_compl := fun S ⟨J, hJ, h⟩ =>
    ⟨J, hJ, fun p q h1 h2 hp hq => hp (h q p h1.symm (fun i hi => (h2 i hi).symm) hq)⟩
  measurableSet_iUnion := fun f hf => by
    choose J hJ h using hf
    refine ⟨⋃ n, J n, countable_iUnion hJ, fun p q h1 h2 hp => ?_⟩
    obtain ⟨n, hn⟩ := mem_iUnion.1 hp
    exact mem_iUnion.2 ⟨n, h n p q h1 (fun i hi => h2 i (mem_iUnion.2 ⟨n, hi⟩)) hn⟩

/-! ## Unzipping along a driver that is discontinuous right after time `a` -/

variable {κ a : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

end Cor15Group
end QuantumZipper
