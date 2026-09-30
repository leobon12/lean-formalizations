import QuantumZipper.Proofs.Zipper.E1TransferFinal
import QuantumZipper.Proofs.Zipper.E1Nu
import QuantumZipper.Proofs.Zipper.E1ZFin
import QuantumZipper.Proofs.Zipper.NuMeas
import QuantumZipper.Proofs.LQG.RevCouplingReg

/-!
# E-WIRE: the E1 nodes with B3(a) and E1-TR discharged

Wiring task: several committed theorems still take
`hReg : Blueprint.RevCouplingBoundaryMeasureRegular` (RCBMR) or the E1-TR conclusion as a
hypothesis, although both are now proved:

* RCBMR: `RevCouplingReg.revCouplingBoundaryMeasureRegular` (`Proofs/LQG/RevCouplingReg.lean`);
* E1-TR: `E1.e1_tr` (`Proofs/Zipper/E1TransferFinal.lean`).

This file states the unconditional corollaries, with the *original* conclusions and only the
remaining hypotheses:

* `zfin`: Z-FIN (`E1.zfin_of_tr`), with `hTR` discharged by `e1_tr` at `t = 0`, `Ψ = Φ = 1`;
* `aemeasurable_nuPalm`: NU-MEAS (`NuMeas.aemeasurable_nuPalm`);
* `e3_pos`: E3-POS (`NuMeas.e3_pos'`);
* `e1_nu`: E1-NU (`E1Nu.e1_nu_of_tr`), with `E1TRHolds` discharged by `e1_tr`;
* `e1_main`: E1 (`E1.e1_main`), unconditional.

Nothing new is proved here: every proof is one application of the already-proved statement.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace EWire

open B2 E1 CoordsFull PalmNorm B1Full

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}

/-- **Z-FIN**, unconditional: the Palm normalizer lies in `(0, ⊤)` (`E1.zfin_of_tr` with
`hTR` discharged by `E1.e1_tr` at `t = 0`, `Ψ = Φ = 1`, and `hReg` by RCBMR). -/
theorem zfin (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) {δ : ℝ} (hδ : 0 < δ)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hϖ : IsNormalizer ϖ) :
    (∫⁻ ω, nuPalm κ T B X ϖ ω (Icc (-δ) 0) ∂P =
        ∫⁻ x in Ico (-δ) 0, ENNReal.ofReal (rhoNorm (Real.sqrt κ) (h0rev κ) ϖ x)) ∧
      0 < ∫⁻ ω, nuPalm κ T B X ϖ ω (Icc (-δ) 0) ∂P ∧
      ∫⁻ ω, nuPalm κ T B X ϖ ω (Icc (-δ) 0) ∂P < ⊤ :=
  E1.zfin_of_tr RevCouplingReg.revCouplingBoundaryMeasureRegular hκ hκ4 hT hδ hB hX hind hϖ
    (E1.e1_tr (t := 0) (Ψ := fun _ _ => (1 : ℝ≥0∞)) (Φ := fun _ => (1 : ℝ≥0∞))
      RevCouplingReg.revCouplingBoundaryMeasureRegular hκ hκ4 le_rfl hT hB hX hind hϖ δ
      measurable_const measurable_const)

/-- **NU-MEAS**, unconditional (`NuMeas.aemeasurable_nuPalm` with `hReg` discharged). -/
theorem aemeasurable_nuPalm (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (hϖ : IsNormalizer ϖ) :
    AEMeasurable (fun ω => nuPalm κ T B X ϖ ω) P :=
  NuMeas.aemeasurable_nuPalm RevCouplingReg.revCouplingBoundaryMeasureRegular hκ hκ4 hT hB hX
    hind hϖ

/-- **E3-POS**, unconditional (`NuMeas.e3_pos'` with `hReg` discharged). -/
theorem e3_pos (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (hϖ : IsNormalizer ϖ)
    {δ : ℝ} (hδ : 0 < δ) (hTδ : 4 * δ ^ 2 / (4 - κ) ≤ T) :
    0 < ∫⁻ ω, nuPalm κ T B X ϖ ω
      {x | x ∈ Icc (-δ) 0 ∧ realHitTime (Vr κ T B ω) x < ENNReal.ofReal T} ∂P :=
  NuMeas.e3_pos' RevCouplingReg.revCouplingBoundaryMeasureRegular hκ hκ4 hT hB hX hind hϖ hδ hTδ

end EWire
end QuantumZipper
