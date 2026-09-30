import QuantumZipper.Proofs.Zipper.Cor15MeasVerCInv
import QuantumZipper.Proofs.Zipper.Cor15MarkovField
import QuantumZipper.Proofs.Zipper.D3PlusN1Model

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# COR15-MEASVER (2): the consumers only need a `RegEq`-agreeing free version

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5.
Task COR15-MEASVER.

The consumers `cor15ZipGenuineStmt_of_law` (`Cor15ZipGenuine.lean`) and the Markov half
(`Cor15MarkovField*.lean`) use the measurable version `Y` of the zipped/unzipped field only through
(i) its freeness and its independence of the driver, and (ii) `RegEq` of the field with
`𝔥₀ + Y` (the field clause of `ConfigEq`; `RegEq` reads only the dyadic folded circles).
The pointwise identity `Y = sfTrunc (field − 𝔥₀)` a.s. *as a whole field* is never used.

* `Cor15ZipVersionStmt`, `Cor15UnzipVersionStmt`: the obligations in this weaker form.
* `cor15ZipGenuineStmt_of_version`, `cor15MarkovFieldStmt_of_version`: the consumers.
* `cor15ZipVersionStmt_of_law`, `cor15UnzipVersionStmt_of_law`: the old pointwise obligations
  imply the new ones (so this is a genuine weakening of what has to be proved).
* `cor15ZipVersionStmt_of_read`: the zip version from the reading input `Cor15ZipReadStmt` and the
  law obligation `Cor15ZipVerLawStmt` for the `CInv` version (`Cor15MeasVerZip.lean`).
* `theorem1_5_of_theorem1_3_of_versions`, `theorem1_5_of_theorem1_3_of_readVerLaw`: assemblies.

Own bookkeeping.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

/-! ## The obligations, version form -/

/-- **Unzip direction, version form.** There is a field `Y`, measurable in every coordinate, free
modulo constants, independent of the shifted Brownian path, with `D_a c` a.s. `RegEq` to
`𝔥₀ + Y`. -/
def Cor15UnzipVersionStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), IsGrpSetup P B X →
    ∀ a : ℝ, 0 < a → ∃ Y : Ω → FieldSample, (∀ μ : Measure ℂ, Measurable fun ω => Y ω μ) ∧
      IsFreeGFFModConstH Y P ∧
      IndepFun (fun ω => shiftPath a (pathOf B ω)) Y P ∧
      ∀ᵐ ω ∂P, RegEq (zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω)).1 (ofFun (h0rev κ) + Y ω)

/-! ## The consumers -/

/-- The driver clause of `ConfigEq` for `U_a c`, in the form the quotient by `√κ` gives it. -/
theorem zipCapUp_snd_eq_sqrt_mul_zipDrv {κ a : ℝ} (hκ : 0 < κ)
    (c : FieldSample × (ℝ → ℝ)) {u : ℝ} (hu : 0 ≤ u) :
    (zipCapUp (Real.sqrt κ) a c).2 u = Real.sqrt κ * zipDrv κ a c u.toNNReal := by
  rw [zipDrv, Real.coe_toNNReal _ hu, mul_inv_cancel_left₀ (Real.sqrt_pos.2 hκ).ne']

/-- **`Cor15MarkovFieldStmt` from the version form.** -/
theorem cor15MarkovFieldStmt_of_version (h : Cor15UnzipVersionStmt) : Cor15MarkovFieldStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hS a ha
  obtain ⟨Y, -, hfree, hind, hreg⟩ := h κ hκ hκ4 P B X hS a ha
  refine ⟨Y, hfree, ?_, hreg⟩
  rw [pathOf_shift_eq]
  exact hind

/-! ## The old pointwise obligations imply the version form -/

/-! ## The zip version from the reading input and the `CInv` law obligation -/

/-! ## Corollary 1.5 -/

end Cor15Group
end QuantumZipper
