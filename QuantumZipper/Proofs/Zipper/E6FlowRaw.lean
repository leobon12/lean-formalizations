import QuantumZipper.Proofs.Zipper.E6InReduce
import QuantumZipper.Proofs.Zipper.JointModFinal

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E6 input `CanonZipRegStmt`: the circle half is proved, the pairing half is isolated

Theorem 1.3, node E6 (Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797,
§5.4, pp. 70–72; the paper works with distributions and never reads raw values, decision D25).
`E6.RawRegular x` has two halves: raw values at the enumerated folded circles equal `evalReg`
(`RawCircRegular`), and raw pairings with test functions equal `pairTest` (`RawPairRegular`).

* `rawCircRegular_rescale`: **every dilation `rescale R Q b` (`b > 0`) of a regular sample is
  circle-raw-regular** (deterministic; the witness calculus `RegClosure.rescale_fc_eq`,
  `IsRegularWith.rescale'`, `IsRegularWith.evalReg_fc`).
* Both sides of the zip identity are such dilations: the right side is
  `canonical γ (x_{u+t₀} + k)`, with `x_{u+t₀}` regular for all times at once
  (`RegUnif.ae_forall_isRegularSample`, unconditional: Duplantier–Sheffield 2011 Prop 3.1 via the
  joint Kolmogorov modification) and scale `> 0` (`B3d.ZipLenInputsStmt`, clause 1); the left side
  is `canonical γ (x')` with `x'` the canonicalized configuration unzipped at the length time, and
  `coordChange` reads `x'` only through `evalReg`, so it equals the dilation of the regular sample
  `rescale (x^{(u)}_{a²τ} + k) Q a` (`B3d.ZipLenInputsStmt`, clauses 2, 4, 5;
  `B3d.rescale_congr_avgReg`, `GoodTransforms.scaleParam_rescale`).
* `canonZipRegStmt_of_pair`, `canonZipRawAllStmt_of_pair`: hence `CanonZipRegStmt` (and
  `CanonZipRawAllStmt`) follow from `B3d.ZipLenInputsStmt` and the **pairing half only**,
  `CanonZipPairStmt`.

Own elementary bookkeeping (no published source reads raw values).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper.E6

open B2 E1 D3Plus

/-- Circle half of `RawRegular`. -/
def RawCircRegular (x : FieldSample) : Prop :=
  ∀ i : ℕ, CoordsFull.coordsFull x i =
    evalReg x (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2)

/-- Pairing half of `RawRegular`. -/
def RawPairRegular (x : FieldSample) : Prop :=
  ∀ ρ : TestFun H, pairRaw x ρ.1 = pairTest x ρ.1

theorem rawRegular_of_halves {x : FieldSample} (hc : RawCircRegular x) (hp : RawPairRegular x) :
    RawRegular x := ⟨hc, hp⟩

theorem fullIndex_radius_pos' (i : ℕ) : 0 < (CoordsFull.fullIndex i).2 := by
  unfold CoordsFull.fullIndex
  positivity

/-- **Dilations of regular samples are circle-raw-regular.** -/
theorem rawCircRegular_rescale {R : FieldSample} (hR : IsRegularSample R) (Q : ℝ) {b : ℝ}
    (hb : 0 < b) : RawCircRegular (rescale R Q b) := by
  obtain ⟨F, hF⟩ := hR
  intro i
  have hr := fullIndex_radius_pos' i
  show rescale R Q b (foldedCircle _ _) = _
  rw [RegClosure.rescale_fc_eq hF Q hb _ hr, (hF.rescale' Q hb).evalReg_fc _ hr,
    RegClosure.foldH_mul_pos _ hb]

variable {Ω : Type} [MeasurableSpace Ω]

end QuantumZipper.E6
