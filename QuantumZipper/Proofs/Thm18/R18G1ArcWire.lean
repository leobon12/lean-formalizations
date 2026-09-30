import QuantumZipper.Proofs.Thm18.R18G1ArcDefs
import QuantumZipper.Proofs.Thm18.R18Arc
import QuantumZipper.Proofs.Thm18.G1ZA1bArea
import QuantumZipper.Proofs.Thm18.G1Z2MeasMain
import QuantumZipper.Proofs.Thm18.G1CoreScale
import QuantumZipper.Proofs.Thm18.G1FM2Final
import QuantumZipper.Proofs.Thm18.G1ZSplitWire

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G1ARC: rerooting invariance (G1 node A) from the open-arc Theorem 1.3 nodes

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Theorem 1.8
(§5.4, pp. 69–71): "the configuration must be invariant under unzipping by a fixed quantity of
quantum length", hence the side surface is invariant under rerooting by quantum length.

Copies (substitution rule of `handoff/FOLLOW-PAPER-13.md` §1) of the proofs in
`G1ZSplitWire.lean` (`g1RerootPathStmt_of_parts`, `g1RerootStmt_of`) and `G1ZA1bMain.lean`
(`g1RerootRegStmt_of`), with `E6 ↦ LocLen.E6StmtArc`, `F1 ↦ R18.F1ArcStmt`,
`UnzipMeas ↦ LocLen.UnzipMeasArcStmt`. The old proofs used the old nodes only through the law
identity, the measurability of the unzipped data and the length identity, so the copies are
verbatim up to the substitution. Own bookkeeping, as the originals.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm LocLen D3Plus

/-- `UnzipMeasArcStmt` from X1 (the chain of `R18.e6StmtArc_of_X1`). -/
theorem unzipMeasArc_of_X1 (hX1 : BaseFin.BaseFiniteStmt) : LocLen.UnzipMeasArcStmt := by
  have hYO := SWCore.yMergeOffTipStmt_holds
  have hC : LenPairCocycleArcStmt := lenPairCocycleArc_of_yMergeOffTip hYO
  have hF : LenFiniteArcStmt :=
    lenFiniteArc_of_baseFinite hX1 (wedgePairCocycleArc_of_yMergeOffTip hYO)
  have hsm : LenStrictMonoArcStmt := lenStrictMonoArc_of_yMergeOffTip hYO hC hF
  exact R5c.unzipMeasArc_of_hitScaleZip
    (R5c.hitScaleZipArcStmt_of_nodes hsm hF (pStarAreaAll_of_yMergeOffTip hYO))

/-- Open-arc E6 in the Theorem 1.8 variables (copy of `Thm18Asm.e6_thm18`). -/
theorem e6Arc_thm18 (hE6 : LocLen.E6StmtArc) {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (ℓ : ℝ) (hℓ : 0 < ℓ) :
    configLawFull (fun ω => zipLenDownArc γ ℓ (wedgeConfig γ B Y ω)) P =
      configLawFull (wedgeConfig γ B Y) P := by
  have h := hE6 (γ ^ 2) P Y B (isPStarSample_of_setting hS) ℓ hℓ
  rw [Real.sqrt_sq hS.1.le] at h
  exact h

/-- The data of `Z^LEN_{−t} c` (open arcs) is a.e.-measurable (copy of
`Thm18Asm.aemeasurable_cfgData_zipLenDown`). -/
theorem aemeasurable_cfgData_zipLenDownArc (hum : LocLen.UnzipMeasArcStmt) {γ : ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {Y : Ω → FieldSample} (hS : Thm18Setting γ P B Y) {t : ℝ} (ht : 0 < t) :
    AEMeasurable (fun ω => cfgData (zipLenDownArc γ t (wedgeConfig γ B Y ω))) P := by
  have h := hum (γ ^ 2) P Y B (isPStarSample_of_setting hS) t ht
  rw [Real.sqrt_sq hS.1.le] at h
  exact h

/-- **A1 (open arcs) from A1a, A1b, A1c** (copy of `g1RerootPathStmt_of_parts`). -/
theorem g1RerootPathArcStmt_of_parts (hA : G1RerootAffineStmt) (hR : G1RerootRegArcStmt)
    (hL : G1RerootLenArcStmt) : G1RerootPathArcStmt := by
  intro γ Ω _ P _ B Y hS hIn hEq ℓ hℓ left
  filter_upwards [ae_g1zDrvGood hS hIn, hR γ P B Y hS hIn ℓ hℓ left,
    hL γ P B Y hS hIn hEq ℓ hℓ left] with ω hW hreg hlen
  obtain ⟨ht, ha, hLen⟩ := hlen
  obtain ⟨-, lam, β, hlam, hβ, hEqOn, hlim⟩ := hA _ hW _ _ ht ha left
  obtain ⟨hl, hpos⟩ := hLen β hβ hlim
  rw [g1SidePt_eq_of_len hβ hpos hl]
  exact hreg lam β hlam hEqOn

/-- **A (rerooting invariance) from the open-arc E6, F1, A1, A1a, A1c and A2** (copy of
`Thm18Asm.g1RerootStmt_of`). -/
theorem g1RerootStmt_of_arc (hE6 : LocLen.E6StmtArc) (hF1 : F1ArcStmt)
    (hum : LocLen.UnzipMeasArcStmt) (hP : G1RerootPathArcStmt) (hA : G1RerootAffineStmt)
    (hL : G1RerootLenArcStmt) (hF : G1RerootFactorStmt) : G1RerootStmt := by
  intro γ Ω _ P _ B Y hS hIn left
  have hEq : LenEqArc γ P B Y := hF1 γ P B Y hS hIn
  set c := wedgeConfig γ B Y with hc
  have hpath : AEMeasurable (fun ω => fun t : ℝ≥0 => (c ω).2 t) P := by
    have hm : Measurable fun a : ℝ≥0 → ℝ => fun t : ℝ≥0 =>
        Real.sqrt (γ ^ 2) * a ((t : ℝ).toNNReal) :=
      measurable_pi_iff.2 fun t => (measurable_pi_apply _).const_mul _
    exact hm.comp_aemeasurable (QuantumZipper.IsBrownianReal.aemeasurable_pathOf hS.2.2.1)
  have hmc : AEMeasurable (fun ω => g1zCfgData (c ω)) P := hIn.2.1.prodMk hpath
  refine ⟨?_, fun ℓ hℓ R Γ hΓ hΓ1 => ?_⟩
  · obtain ⟨G, G₀, E, _hGm, hG₀, _hEm, hdet, hE⟩ := hF γ P B Y hS hIn left 1 one_pos 0 (fun _ => 0)
      measurable_const fun _ => zero_le_one
    refine (hG₀.comp_aemeasurable hmc).congr ?_
    filter_upwards [hE, ae_g1zDrvGood hS hIn] with ω h1 h2
    exact ((hdet _ h1 h2).2).symm
  obtain ⟨G, G₀, E, hG, _hG₀, hEm, hdet, hE⟩ := hF γ P B Y hS hIn left ℓ hℓ R Γ hΓ hΓ1
  set c' := fun ω => zipLenDownArc γ ℓ (c ω) with hc'
  have hlaw : P.map (fun ω => g1zCfgData (c' ω)) = P.map (fun ω => g1zCfgData (c ω)) :=
    e6Arc_thm18 hE6 hS ℓ hℓ
  have hmc' : AEMeasurable (fun ω => g1zCfgData (c' ω)) P :=
    aemeasurable_cfgData_zipLenDownArc hum hS hℓ
  have hE' : ∀ᵐ ω ∂P, g1zCfgData (c' ω) ∈ E := by
    have h : ∀ᵐ p ∂(P.map fun ω => g1zCfgData (c ω)), p ∈ E := (ae_map_iff hmc hEm).2 hE
    rw [← hlaw] at h
    exact (ae_map_iff hmc' hEm).1 h
  have hgood' : ∀ᵐ ω ∂P, G1zDrvGood (c' ω).2 := by
    filter_upwards [ae_g1zDrvGood hS hIn, hL γ P B Y hS hIn hEq ℓ hℓ left] with ω hW hl
    exact (hA _ hW _ _ hl.1 hl.2.1 left).1
  calc g1RerootInt γ P (g1SideField γ B Y left) left ℓ R Γ
      = ∫⁻ ω, G (g1zCfgData (c ω)) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hE, ae_g1zDrvGood hS hIn] with ω h1 h2
        exact (hdet _ h1 h2).1
    _ = ∫⁻ p, G p ∂(P.map fun ω => g1zCfgData (c ω)) := (lintegral_map' hG.aemeasurable hmc).symm
    _ = ∫⁻ p, G p ∂(P.map fun ω => g1zCfgData (c' ω)) := by rw [hlaw]
    _ = ∫⁻ ω, G (g1zCfgData (c' ω)) ∂P := lintegral_map' hG.aemeasurable hmc'
    _ = ∫⁻ ω, g1zRerootF γ left ℓ R Γ (c' ω) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hE', hgood'] with ω h1 h2
        exact ((hdet _ h1 h2).1).symm
    _ = ∫⁻ ω, Γ (locFieldFull R (canonical γ (g1SideField γ B Y left ω))) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hP γ P B Y hS hIn hEq ℓ hℓ left] with ω h
        simp only [g1zRerootF]
        rw [locFieldFull_congr_dataFull h.symm R]
        rfl

end R18
end QuantumZipper
