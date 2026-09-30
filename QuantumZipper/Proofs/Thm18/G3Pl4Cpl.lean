import QuantumZipper.Proofs.Thm18.G3Pl4Loc
import QuantumZipper.Proofs.Zipper.WedgeDecompCore
import QuantumZipper.Proofs.Thm18.R18G3TSplit
import QuantumZipper.Proofs.Section5.Prop17PalmCLog

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (G-b), part (b): the coupling "wedge = `h_C` on the unit half-disc"

Sheffield, arXiv:1012.4797, §1.6 and p. 28 (the `(γ − 2/γ)`-wedge restricted to the unit disc is a
free field plus `(γ − 2/γ)(−log|·|)`; Theorem 1.2's field plus the Palm profile `−γ log|·|` is the
same free field plus the same singularity), via the pathwise wedge decomposition of
`WedgeDecompCore` (`WDec.ae_pathwise`, `WDec.isFree_PhiF_of_indep`; Duplantier–Miller–Sheffield,
arXiv:1409.7055, §4.1).

* `g3pl4_wedge_fcAgree`: for the unscaled wedge `F2.zU γ X A` there is a free field `V` (on the same
  probability space) with, a.s., `zU = V + (γ − 2/γ)(−log|·|)` on every folded circle inside the
  unit disc.
* `g3pl4_hC_fc`: the field of scheme `C` is, on every folded circle,
  `X₀ − X₀(S) + (γ − 2/γ)(−log|·|)`.

Own bookkeeping on top of the cited decomposition (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm Prop16Area.G WedgeUnzip.WDec

/-- **The field of scheme `C` on folded circles.** -/
theorem g3pl4_hC_fc (γ : ℝ) (hγ : 0 < γ) (ω : gffBase.Ω) (d : ℂ) (r : ℝ) :
    g3pField γ (g3wProf γ) ω (foldedCircle d r) =
      (gffBase.X ω (foldedCircle d r) - gffBase.X ω refS) +
        F2.logSingField (γ ^ 2) (foldedCircle d r) := by
  have hs : Real.sqrt (γ ^ 2) = γ := Real.sqrt_sq hγ.le
  have hlog : Integrable (fun z : ℂ => Real.log ‖z‖) (foldedCircle d r) :=
    (S5.FieldLaw.Raw.palmC_integrable_log_sub_fc d 0 r).congr (ae_of_all _ fun z => by simp)
  simp only [g3pField, normField, Pi.add_apply, ofFun, F2.logSingField, g3wProf, h0rev, hs]
  rw [add_comm (∫ z, 2 / γ * Real.log ‖z‖ ∂foldedCircle d r), add_assoc,
    ← integral_add (hlog.const_mul _) (hlog.const_mul _)]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only
  ring

end R18
end QuantumZipper
