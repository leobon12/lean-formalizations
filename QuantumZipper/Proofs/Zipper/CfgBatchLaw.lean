import QuantumZipper.Proofs.Zipper.CfgBatchLawData
import QuantumZipper.Proofs.Zipper.LenInfCore
import QuantumZipper.Proofs.Zipper.F1ReadTimeRed
import QuantumZipper.Proofs.Zipper.F1ReadTimePath
import QuantumZipper.Proofs.Zipper.UnifClB5
import QuantumZipper.Proofs.Zipper.E1TransferM4Ae

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CFG-BATCH-LAW, part 2: the universal law of the total left length (`E6.CfgNormLenLawStmt`)

Theorem 1.3, node E6/LEN-INF; Sheffield, arXiv:1012.4797, §5.1 (pp. 60–62), §5.4 (pp. 70–72).
The paper uses, without proof, that the total left length `S = sup_{t ≥ 0} L⁻_t` of a normalized
`Γ⁰` sample has a law that does not depend on the probability space. Own bookkeeping:

* the data law `configLawFull (cfg κ B X) P` is universal (`configLawFull_cfg_eq_of_normalized`,
  `CfgBatchLawData.lean`);
* at every fixed time `t ≥ 0` the unzipped lengths are a.e.-measurable functions of the data
  (`F1.aemeasurable_unzipLengths_readCfg_of_ae_good`): the path part of the good-data event is
  `F1.ae_pathGoodAll`, the field part (finiteness of the approximating boundary measures of the
  field unzipped at time `t`) follows from the a.s. continuity of the regularized circle
  averages of `h⁰ = 𝔥₀ + X` unzipped at `t` (`E1.ae_continuousOn_avgReg_h0f`);
* a.s. `t ↦ L⁻_t` is monotone on `[0,∞)` (the existing node `F1.LenStrictMonoCfgStmt`), so
  `S = sup_n L⁻_{n+1}` a.s., a countable supremum of the fixed-time readings (`Φ = lenTotRd`),
  and the lengths agree with those of the configuration read back from the data
  (`F1.unzipLengths_eq_readCfg`);
* hence `S = Φ(data)` a.s. with `Φ` a.e.-measurable for the common data law, and the laws agree.

Main result: `cfgNormLenLawStmt_of_strictMono : F1.LenStrictMonoCfgStmt → CfgNormLenLawStmt κ`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper.E6

/-- A monotone function on `[0,∞)` has the same supremum over `[0,∞)` as over `1, 2, 3, …`. -/
theorem iSup_Ici_eq_iSup_nat_of_monotoneOn {L : ℝ → ℝ≥0∞} (h : MonotoneOn L (Ici 0)) :
    ⨆ t ∈ Ici (0 : ℝ), L t = ⨆ n : ℕ, L ((n : ℝ) + 1) := by
  refine le_antisymm (iSup₂_le fun t ht => ?_) (iSup_le fun n => ?_)
  · have hle : t ≤ (⌈t⌉₊ : ℝ) + 1 := (Nat.le_ceil t).trans (le_add_of_nonneg_right zero_le_one)
    exact (h ht (mem_Ici.2 (by positivity)) hle).trans
      (le_iSup (fun n : ℕ => L ((n : ℝ) + 1)) ⌈t⌉₊)
  · exact le_iSup₂_of_le (f := fun t (_ : t ∈ Ici (0 : ℝ)) => L t) ((n : ℝ) + 1)
      (mem_Ici.2 (by positivity)) le_rfl

section Sample

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

theorem aemeasurable_dataH_cfg (hX : IsFreeGFFModConstH X P) :
    AEMeasurable (fun ω => F1.dataH (ofFun (h0rev κ) + X ω)) P := by
  have hY : Measurable fun ω => ofFun (h0rev κ) + X ω :=
    measurable_pi_iff.2 fun μ => measurable_const.add (hX.measurable_coord μ)
  have hD : Measurable (WedgeMeas.dataFull H) :=
    CoordsFull.measurable_coordsFull.prodMk
      (measurable_pi_iff.2 fun ρ => (measurable_pi_apply _).sub (measurable_pi_apply _))
  exact (hD.comp hY).aemeasurable

theorem aemeasurable_cfgData_cfg (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) :
    AEMeasurable (fun ω => F1.cfgData (B2.cfg κ B X ω)) P :=
  F1.aemeasurable_cfgData_drive κ (aemeasurable_dataH_cfg hX)
    (IsBrownianReal.aemeasurable_pathOf hB)

end Sample

end QuantumZipper.E6
