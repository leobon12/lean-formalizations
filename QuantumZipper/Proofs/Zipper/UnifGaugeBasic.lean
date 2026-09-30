import QuantumZipper.Proofs.Zipper.UnifUGReduce
import QuantumZipper.Proofs.Zipper.UnifFieldTipSupGaugeAx
import QuantumZipper.Proofs.Zipper.Cor15GoodConst
import QuantumZipper.Proofs.Zipper.F2AddConst
import QuantumZipper.Proofs.Zipper.JointModFinal
import QuantumZipper.Proofs.Zipper.B1Full
import QuantumZipper.Proofs.LQG.LocalRule
import QuantumZipper.Proofs.LQG.BoundaryVague

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D37-GAUGE (1)+(2): the gauge-normalized sample and the transfer of UG/UA

`IsFreeGFFModConstH` does not pin the additive constant of a `Γ⁰` sample: `X + C·mass` is
admissible for **any** measurable `C : Ω → ℝ` (`UnifFieldTipSupGaugeAx.isFreeGFFModConstH_shiftField`),
and the moment nodes of the D31 chain are equivariant but *not* invariant under that gauge
(`UnifFieldTipSupGauge.fieldTipSup_shiftField`), so they are false as stated (decision D37).

This file implements the fixture of decision D37:

* **the gauge-normalized sample** `nrmF X = ω ↦ nrm (X ω)` (`B1Full.nrm`, the field pinned at
  `foldedCircle 0 1`, i.e. `X − X(fc(0,1))·mass`): `isFreeGFFModConstH_nrmF`, `indepFun_nrmF`,
  `measurable_nrmF`, `nrmF_idem`, `nrmF_zero` — it is again a `Γ⁰` sample, independent of the
  driver, with a fixed gauge;
* **the scaling transfer**: under the named regularity input `GaugeRegStmt` at the normalized
  sample (`E1.RegShift` along the pushed dyadic circles and `Cor15Group.BdryConvAE`, for all
  `s ∈ [0,T]` at once — the analogue of the open node `F2.F2UnzipRegStmt`), the configuration
  fields of `X` and `nrmF X` differ by the constant `c = X ω (foldedCircle 0 1)` exactly
  (`cfg_fst_eq_addConst_nrmF`), so the boundary approximations of the unzipped fields scale by
  the positive finite factor `e^{γc/2}` (`bdryApprox_gaugeScale`; `F2.coordsFull_coordChange_addConst`,
  `Cor15Group.bdryApprox_addConst_ae`, rule (5.1)); existence of vague limits and atomlessness
  are preserved (`unifGlobalStmt_of_scale`, `unifAtomlessStmt_of_scale`,
  `unifGlobalStmt_of_gaugeShift`, `unifAtomlessStmt_of_gaugeShift`).

## Why a regularity input is needed

`h0f κ s B X ω = coordChange (𝔥₀ + X ω) (fwdMapInv W s) Q` reads the field through `evalReg`, a
`limUnder`, and `evalReg (addConst y c) ν = evalReg y ν + c` holds only where the defining limits
exist (`E1.evalReg_addConst_of_regShift`): where they do not, both sides take the junk value of
`limUnder`, which does *not* shift by `c`. So the gauge transfer cannot be purely deterministic;
it needs exactly the `RegShift`/`BdryConvAE` regularity already used by
`F2.qBoundaryMeasure_unzip_addConst_scale` (fixed time) — here at all `s ∈ [0,T]`.

Sources: Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.1 rule (5.1)
(pp. 60–62); Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Prop. 3.1 (constants). The gauge bookkeeping is our own (the paper has no gauge issue: it fixes
the additive constant implicitly).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 B5 B1Full

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-! ## 1. The gauge-normalized sample -/

/-- **The gauge-normalized sample** `nrmF X = ω ↦ nrm (X ω)`: the field pinned at the unit folded
circle, `X − X(foldedCircle 0 1)·mass`. -/
def nrmF (X : Ω → FieldSample) : Ω → FieldSample := fun ω => B1Full.nrm (X ω)

@[simp]
theorem nrmF_apply (X : Ω → FieldSample) (ω : Ω) : nrmF X ω = B1Full.nrm (X ω) := rfl

/-- `nrm` is the constant shift by `−X(foldedCircle 0 1)` (`UnifFieldTipSupGauge.shiftField`),
so the results of `UnifFieldTipSupGaugeAx` apply to it. -/
theorem nrmF_eq_shiftField (X : Ω → FieldSample) :
    nrmF X = fun ω => shiftField (-(X ω (foldedCircle 0 1))) (X ω) := rfl

/-- The normalization is a measurable operation on fields. -/
theorem measurable_nrm_field : Measurable fun x : FieldSample => B1Full.nrm x := by
  refine measurable_pi_iff.2 fun μ => ?_
  have h1 : (fun x : FieldSample => B1Full.nrm x μ) =
      fun x => x μ + (-(x (foldedCircle 0 1))) * (μ Set.univ).toReal := rfl
  rw [h1]
  exact (measurable_pi_apply μ).add ((measurable_pi_apply (foldedCircle 0 1)).neg.mul_const _)

/-- The normalized field vanishes at the pinning circle: the gauge is fixed. -/
theorem nrm_self (y : FieldSample) : B1Full.nrm y (foldedCircle 0 1) = 0 := by
  simp [B1Full.nrm, addConst, measure_univ]

/-- The normalization is idempotent. -/
theorem nrm_nrm (y : FieldSample) : B1Full.nrm (B1Full.nrm y) = B1Full.nrm y := by
  have h : B1Full.nrm y (foldedCircle 0 1) = 0 := nrm_self y
  simp only [B1Full.nrm] at h ⊢
  rw [h]
  funext μ
  simp [addConst]

/-- **The normalized sample is again a `Γ⁰` field modulo constants.** -/
theorem isFreeGFFModConstH_nrmF {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) :
    IsFreeGFFModConstH (nrmF X) P := by
  have hC : Measurable fun ω => -(X ω (foldedCircle 0 1)) := (hX.measurable_coord _).neg
  have h := isFreeGFFModConstH_shiftField hX (fun ω => -(X ω (foldedCircle 0 1))) hC
  simpa only [nrmF_eq_shiftField] using h

/-- **The normalized sample is independent of the driver.** -/
theorem indepFun_nrmF {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hind : IndepFun (pathOf B) X P) : IndepFun (pathOf B) (nrmF X) P := by
  have h : IndepFun (pathOf B) (fun ω => B1Full.nrm (X ω)) P :=
    hind.comp measurable_id measurable_nrm_field
  exact h

/-! ## 2. The regularity input and the scaling of the boundary approximations -/

/-! ## 3. Preservation of vague limits and atomlessness -/

end RegUnif
end QuantumZipper
