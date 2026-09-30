import QuantumZipper.Proofs.Thm18.G1ZSplitWire
import QuantumZipper.Proofs.Zipper.E4L3i
import QuantumZipper.Proofs.Zipper.E5Model1
import QuantumZipper.Proofs.Zipper.E6LocAbsBasic
import QuantumZipper.Proofs.Zipper.F1Embed
import QuantumZipper.Proofs.Zipper.F1LenScale
import QuantumZipper.Proofs.Zipper.F1LenRead
import QuantumZipper.Proofs.Zipper.F1ABJensen
import QuantumZipper.Proofs.Zipper.F1GermFam
import QuantumZipper.Proofs.Zipper.F1ReadTimeRed
import QuantumZipper.Proofs.Zipper.F2Gamma0ScaleDet
import QuantumZipper.Proofs.Zipper.F2LocalScale
import QuantumZipper.Proofs.Zipper.F2LocalSteps
import QuantumZipper.Proofs.Zipper.F2Reduce
import QuantumZipper.Proofs.Zipper.F2Step2b
import QuantumZipper.Proofs.Zipper.F2Step3
import QuantumZipper.Proofs.Zipper.F2Step3DensUnif
import QuantumZipper.Proofs.Zipper.F2Weld
import QuantumZipper.Proofs.Zipper.F2WedgeCouple
import QuantumZipper.Proofs.Zipper.F2WeldTimes
import QuantumZipper.Proofs.Zipper.FSMeasF2
import QuantumZipper.Proofs.Zipper.HitScaleZipScale
import QuantumZipper.Proofs.Zipper.LocHitScalePStar
import QuantumZipper.Proofs.Zipper.LocRichE6
import QuantumZipper.Proofs.Zipper.UnifClAnchor
import QuantumZipper.Proofs.Zipper.UnifRCSplit
import QuantumZipper.Proofs.Zipper.WedgeRC3All2
import QuantumZipper.Proofs.Zipper.WedgeUnzipXC
import QuantumZipper.Proofs.LQG.GoodTransforms
import QuantumZipper.Proofs.Zipper.F1NodeAsm
import QuantumZipper.Proofs.Zipper.E1TransferM4Ae
import QuantumZipper.Proofs.LQG.LogSingularity
import QuantumZipper.Proofs.Zipper.F1CanonLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-B2C (1): the configuration law of the canonicalized shifted wedge configuration

Theorem 1.8, G1 zoom, node B2-C (`G1SideConstInvStmt`). Sheffield, arXiv:1012.4797, proof of
Proposition 1.7 (pp. 25–26: zoom in by adding a constant `C`; the `(γ−2/γ)`-wedge is invariant
in law under adding a constant and re-embedding, and the SLE, being scale invariant and independent
of the field, absorbs the re-embedding scale).

For the Theorem 1.8 setting `(Y, B)` with `κ = γ²` and a constant `C`, the canonicalized
configuration `canonConfig γ (Y + C, drive κ B) = (canonical (Y+C), W(a² ·)/a)`, `a = scaleParam γ
(Y + C)`, has the same `configLawFull` as `(Y, drive κ B)` (`F1.pStarCanonLawStmt_of`, proved from
`F1.wedgeAddConstLawStmt_holds`), and a.s. a good driver (it is the driver of the Brownian motion
`rscale`, whose good set is the Rohde–Schramm one).

Own bookkeeping; the two proved inputs are the cited nodes above (copy of the first half of
`F1.pStarCanonLawStmt_of`, which does not export the driver identification).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open Factorization CoordsFull

/-- A.s. the driver of a Brownian motion is good (Rohde–Schramm, `κ = γ² < 4`). -/
theorem ae_g1zDrvGood_of_brownian {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) : ∀ᵐ ω ∂P, G1zDrvGood (drive (γ ^ 2) B ω) := by
  have hκ4 : γ ^ 2 ≤ 4 := by nlinarith
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero,
    RS.rohdeSchrammSimple (γ ^ 2) (by positivity) hκ4 P B hB] with ω hc h0 hin
  refine ⟨?_, ?_, fun s => ?_, hin.1, hin.2⟩
  · exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  · simp only [drive, Real.toNNReal_zero]
    rw [h0]; simp
  · simp only [drive]
    congr 2
    apply NNReal.eq
    simp [Real.coe_toNNReal']

/-- **The canonicalized shifted configuration** of the Theorem 1.8 setting: positive scale,
same configuration law, a.e.-measurable data, good driver. -/
theorem canonConfig_shift_facts {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (C : ℝ) :
    (∀ᵐ ω ∂P, 0 < scaleParam γ (addConst (Y ω) C)) ∧
    configLawFull (fun ω => canonConfig γ (addConst (Y ω) C, drive (γ ^ 2) B ω)) P =
      configLawFull (wedgeConfig γ B Y) P ∧
    AEMeasurable (fun ω => g1zCfgData (canonConfig γ (addConst (Y ω) C, drive (γ ^ 2) B ω))) P ∧
    ∀ᵐ ω ∂P, G1zDrvGood (canonConfig γ (addConst (Y ω) C, drive (γ ^ 2) B ω)).2 := by
  have hP := isPStarSample_of_setting hS
  obtain ⟨hγ, hγ2, hB, hW, hI⟩ := hS
  have hsq : Real.sqrt (γ ^ 2) = γ := Real.sqrt_sq hγ.le
  have hα : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  obtain ⟨hpos, -⟩ := F1.wedgeAddConstLawStmt_holds γ (γ - 2 / γ) hγ hγ2 hα P Y hW C
  obtain ⟨hlaw, hmeas⟩ := F1.pStarCanonLawStmt_of F1.wedgeAddConstLawStmt_holds (γ ^ 2) P Y B hP C
  have hlaw' : configLawFull (fun ω => canonConfig (Real.sqrt (γ ^ 2))
      (addConst (Y ω) C, drive (γ ^ 2) B ω)) P = configLawFull (wedgeConfig γ B Y) P := hlaw
  have hmeas' : AEMeasurable (fun ω => g1zCfgData (canonConfig (Real.sqrt (γ ^ 2))
      (addConst (Y ω) C, drive (γ ^ 2) B ω))) P := hmeas
  rw [hsq] at hlaw' hmeas'
  refine ⟨hpos, hlaw', hmeas', ?_⟩
  -- the driver identification (first half of `F1.pStarCanonLawStmt_of`)
  have hYm : AEMeasurable (fun ω => F1.dataH (Y ω)) P :=
    Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hα hW
  have hgood : ∀ᵐ ω ∂P, IsLQGGood γ (Y ω) := Wire2.wedgeGoodStmt hγ hγ2 hα P Y hW
  obtain ⟨ξ, hξ⟩ : ∃ ξ : Ω → ((ℕ → ℝ) × (TestFun H → ℝ)) × ℝ,
      ξ = fun ω => F1.canonAddFactor γ C (coordsFull (Y ω)) := ⟨_, rfl⟩
  have hcY : AEMeasurable (fun ω => coordsFull (Y ω)) P := hYm.fst
  have hξm : AEMeasurable ξ P := by
    rw [hξ]
    exact AEMeasurable.comp_aemeasurable (g := F1.canonAddFactor γ C)
      (f := fun ω => coordsFull (Y ω)) (F1.measurable_canonAddFactor γ C).aemeasurable hcY
  have hFm : Measurable fun x : FieldSample => F1.canonAddFactor γ C (coordsFull x) :=
    Measurable.comp (g := F1.canonAddFactor γ C) (f := coordsFull)
      (F1.measurable_canonAddFactor γ C) measurable_coordsFull
  have hξI : IndepFun ξ (pathOf B) P := by
    rw [hξ]
    exact IndepFun.comp (φ := fun x : FieldSample => F1.canonAddFactor γ C (coordsFull x))
      (ψ := id) hI.symm hFm measurable_id
  have hξae : ∀ᵐ ω ∂P, ξ ω = (F1.dataH (canonical γ (addConst (Y ω) C)),
      scaleParam γ (addConst (Y ω) C)) := by
    filter_upwards [hgood] with ω h
    rw [hξ]
    show F1.canonAddFactor _ C (coordsFull (Y ω)) = _
    rw [F1.canonAddFactor_coordsFull, F1.canonData_of_good (h.addConst C)]
  obtain ⟨hBr, -⟩ := F2.randScale_of_aemeasurable hB hξm F1.measurable_sqScaleG
    F1.sqScaleG_ne_zero hξI
  obtain ⟨B'', hB''⟩ : ∃ B'' : ℝ≥0 → Ω → ℝ, B'' = F2.rscale (F1.sqScaleG ∘ ξ) B := ⟨_, rfl⟩
  rw [← hB''] at hBr
  filter_upwards [hξae, hpos, ae_g1zDrvGood_of_brownian hγ hγ2 hBr] with ω h1 h2 hg
  have hB'ω : drive (γ ^ 2) B'' ω =
      drive (γ ^ 2) (F2.rscale (fun _ =>
        (scaleParam γ (addConst (Y ω) C) ^ 2).toNNReal) B) ω := by
    funext r
    simp only [drive, F2.rscale, hB'', Function.comp, h1, F1.sqScaleG, h2, ↓reduceIte]
  have e : canonConfig γ (addConst (Y ω) C, drive (γ ^ 2) B ω) =
      (canonical γ (addConst (Y ω) C), drive (γ ^ 2) B'' ω) := by
    rw [F2.canonConfig_eq_drive γ (γ ^ 2) _ B ω h2, hB'ω]
  rw [e]
  exact hg

end Thm18Asm
end QuantumZipper
