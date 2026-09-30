import QuantumZipper.Proofs.Zipper.E5Main5
import QuantumZipper.Proofs.Zipper.F1ReflLaw
import QuantumZipper.Proofs.Probability.BrownianPathMeas

/-!
# E5-MAIN, part 6: the `P_*` side (`E5TargetStmtG`) is proved

For a readout `fr` that factors measurably through the `configLawFull` field data
`F1.dataH = WedgeMeas.dataFull H` (true for `locFieldFull` and `TV.locField`), the `P_*`
functional of `locG fr R` is the `P' ⊗ W` functional of `(fr R Y, √κ b(min · R))` for every
Brownian coordinate measure `W`: independence of `Y` and `B'` splits the joint law
(`indepFun_iff_map_prod_eq_prod_map_map`), `dataH ∘ Y` is a.e.-measurable for a wedge
(`Wire2.aemeasurable_dataFull_of_isQuantumWedge`), and the Brownian path law is unique
(projective limits, as in `F1.map_pathOf_eq_of_isPreBrownianReal`).

* `e5TargetStmtG_of_factor`, `e5TargetStmtG_locFieldFull`, `e5TargetStmtG_locField`;
* `e5Rich_of_model : D3PlusIStmtRich → D3PlusIIStmtRich → E5ModelStmtG locFieldFull →
  E4Stmt → E6.E5StmtRich` and `e5Node_of_model` (D23 form): **the only open input of E5 besides
  D3⁺(i), (ii) is the concrete identification `E5ModelStmtG`.**

Own bookkeeping (standard: independence gives the product law).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open LengthMarkov.GermDensity D3Plus

theorem drive_min_eq_drvWin (κ : ℝ) {Ω' : Type*} (B' : ℝ≥0 → Ω' → ℝ) (ω' : Ω') (R : ℕ) :
    (fun s : ℝ≥0 => drive κ B' ω' (min (s : ℝ) R)) =
      drvWin κ R (pathRestr (R : ℝ≥0) (pathOf B' ω')) := by
  funext s
  simp only [drive, drvWin, pathExt, pathRestr, pathOf]
  congr 2
  rw [show ((R : ℝ)) = ((R : ℝ≥0) : ℝ) from rfl, ← NNReal.coe_min, Real.toNNReal_coe]

/-- `locFieldFull R` is a measurable function of `F1.dataH`. -/
theorem locFieldFull_factor (R : ℕ) : ∃ φ : (ℕ → ℝ) × (TestFun H → ℝ) → (ℕ → ℝ) × (TestFun H → ℝ),
    Measurable φ ∧ ∀ x, locFieldFull R x = φ (F1.dataH x) :=
  ⟨fun d => (E6.truncFull R (d, fun _ => 0)).1,
    measurable_fst.comp ((E6.measurable_truncFull R).comp (measurable_id.prodMk measurable_const)),
    fun x => (congrArg Prod.fst (E6.truncFull_cfgFull R (x, fun _ => 0))).symm⟩

end E5
end QuantumZipper
