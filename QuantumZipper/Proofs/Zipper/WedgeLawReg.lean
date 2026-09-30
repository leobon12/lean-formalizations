import QuantumZipper.Proofs.Thm18.G4RoundWedgeReg
import QuantumZipper.Proofs.Wire2b

/-!
# WEDGE-LAW (2): the Theorem 1.8 wedge sample is a.s. regular

`Thm18Asm.WedgeRegSampleStmt` asks that a `γ`-quantum wedge `Y` of weight `α = γ − 2/γ` is a.s.
a regular sample (`IsRegularSample`, blueprint M4-R4). Regularity is the first clause of
`IsLQGGood` (`GoodSample.lean`), and every quantum wedge is a.s. `IsLQGGood`
(`Wire2.isQuantumWedge_ae_unitArea`, R23 (c): the good event is read off the data law and holds
for the reference field `canonical γ (h† + Q(−log|·|) + A_{−log|·|})`, Duplantier–Miller–
Sheffield, arXiv:1409.7055, Def. 4.5, via `LogSingGood.wedgeRefGoodAS_holds`). The range
condition `α < Q` is part of `IsQuantumWedge`.

Own bookkeeping (a two-line consequence of the cited project results).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter

namespace QuantumZipper

/-- **`WedgeRegSampleStmt` holds.** A `γ`-quantum wedge (`0 < γ < 2`) is a.s. a regular
sample. -/
theorem Thm18Asm.wedgeRegSampleStmt_holds : Thm18Asm.WedgeRegSampleStmt := by
  intro γ Ω _ P _ Y hγ hγ2 hW
  filter_upwards [Wire2.isQuantumWedge_ae_unitArea hγ hγ2 hW.1 hW] with ω hω
  exact hω.1.1

end QuantumZipper
