import QuantumZipper.Proofs.Zipper.F1LenScale
import QuantumZipper.Proofs.Zipper.F2Unscaled
import QuantumZipper.Proofs.Zipper.F1ReflLaw
import QuantumZipper.Proofs.LQG.GoodMeasurable
import QuantumZipper.Proofs.Section5.Prop16MeasCoords
import QuantumZipper.Proofs.Wire2b
import QuantumZipper.Proofs.Probability.BrownianPathMeas

/-!
# Theorem 1.3, node F1: `PStarCanonLawStmt` from the field-level B4(c)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §1.6 (canonical
description (1.8) of a quantum wedge; the wedge is defined as a quantum surface, i.e. modulo
`h ↦ h(a·) + Q log a`) and §5.4 (proof of Theorem 1.3, p. 71, "by scaling"); Duplantier–Miller–
Sheffield, *Liouville quantum gravity as a mating of trees*, arXiv:1409.7055, Def. 4.5 and
Prop. 4.6 (the circle-average embedding of a wedge; adding a constant to the field and
re-embedding gives the same law). Blueprint `E_BRANCH_BLUEPRINT.md` §F1 (F1b).

`PStarCanonLawStmt` (in `F1LenScale.lean`) asks, for a `P_*` sample `(Y, B')` and a constant
`k`, that `c' = canonConfig γ (Y + k, √κ B')` has the `configLawFull` of `(Y, √κ B')`, with
a.e.-measurable data. This file proves it from the **field-level B4(c)** statement
`WedgeAddConstLawStmt`: for an `α`-wedge `Y`, a.s. `scaleParam γ (Y + k) > 0`, and the canonical
description `canonical γ (Y + k)` has the field law (`fieldLawFull H`) of `Y`.

Argument (own bookkeeping around the cited scaling facts):
* the canonical data of `Y + k` and the scale `a = scaleParam γ (Y + k)` are a measurable function
  (`canonAddFactor`) of the circle coordinates `coordsFull Y`, on the a.s. event that `Y` is good
  (`Factorization`, `GoodMeas.measurable_scaleParam_global`); hence `ξ = (data, a)` is
  a.e.-measurable and independent of `B'`;
* Brownian scaling by the independent random factor `a` (`F2.randScale_of_aemeasurable`, built on
  `randScale_isBrownian_indep`): `B'' = a⁻¹ B'(a² ·)` is a Brownian motion independent of `ξ`, and
  pointwise `c' = (canonical γ (Y + k), √κ B'')` (`F2.canonConfig_eq_drive`);
* independence factorizes both configuration laws into products; the field factors agree by
  B4(c), the path factors because all Brownian motions have the same path law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

open Factorization CoordsFull
open Classical

/-! ## 1. The canonical data of `x + k` as a measurable function of `coordsFull x` -/

/-- The scale parameter, with junk value `0` off good samples (measurable). -/
def goodScale (γ : ℝ) (z : FieldSample) : ℝ := if IsLQGGood γ z then scaleParam γ z else 0

theorem goodScale_eq (γ : ℝ) (z : FieldSample) :
    goodScale γ z = if IsLQGGood γ z then scaleParam γ z else 0 := by
  classical
  by_cases hz : IsLQGGood γ z <;> simp [goodScale, hz]

theorem goodScale_of_good {γ : ℝ} {z : FieldSample} (hz : IsLQGGood γ z) :
    goodScale γ z = scaleParam γ z := by
  classical
  simp [goodScale, hz]

theorem measurable_goodScale (γ : ℝ) : Measurable (goodScale γ) := by
  have h := GoodMeas.measurable_scaleParam_global γ
  have e : goodScale γ = fun x => if IsLQGGood γ x then scaleParam γ x else 0 :=
    funext (goodScale_eq γ)
  rw [e]
  exact h

/-- The data of the canonical description of `z` (junk scale off good samples), with its scale. -/
def canonData (γ : ℝ) (z : FieldSample) : ((ℕ → ℝ) × (TestFun H → ℝ)) × ℝ :=
  (dataH (rescale z (Qc γ) (goodScale γ z)), goodScale γ z)

theorem measurable_canonData (γ : ℝ) : Measurable (canonData γ) := by
  refine (measurable_dataH_of (g := fun z => rescale z (Qc γ) (goodScale γ z))
    fun μ hμ => ?_).prodMk (measurable_goodScale γ)
  exact Measurable.comp (g := fun p : FieldSample × ℝ => rescale p.1 (Qc γ) p.2 μ)
    (f := fun z : FieldSample => (z, goodScale γ z))
    (Prop16Area.measurable_rescale_apply_joint (Qc γ) μ)
    (measurable_id.prodMk (measurable_goodScale γ))

theorem canonData_reconstruct (γ : ℝ) (z : FieldSample) :
    canonData γ (reconstruct (coords z)) = canonData γ z := by
  have hg : goodScale γ (reconstruct (coords z)) = goodScale γ z := by
    rw [goodScale_eq, goodScale_eq, GoodSample.isLQGGood_iff_reconstruct,
      scaleParam_congr (avgReg_reconstruct_coords z)]
  simp only [canonData, hg, Prop16Area.rescale_reconstruct_coords]

theorem canonData_of_good {γ : ℝ} {z : FieldSample} (hz : IsLQGGood γ z) :
    canonData γ z = (dataH (canonical γ z), scaleParam γ z) := by
  simp only [canonData, goodScale_of_good hz, canonical]

theorem coords_addConst (x : FieldSample) (k : ℝ) :
    coords (addConst x k) = fun j => coords x j + k := by
  funext j
  simp [coords, addConst, measure_univ]

/-- The canonical data of `x + k` read from `coordsFull x`. -/
def canonAddFactor (γ k : ℝ) (c : ℕ → ℝ) : ((ℕ → ℝ) × (TestFun H → ℝ)) × ℝ :=
  canonData γ (reconstruct (fun j => WedgeCan4.piC c j + k))

theorem measurable_canonAddFactor (γ k : ℝ) : Measurable (canonAddFactor γ k) :=
  (measurable_canonData γ).comp (measurable_reconstruct.comp
    (measurable_pi_iff.2 fun j =>
      ((measurable_pi_apply j).comp WedgeCan4.measurable_piC).add_const k))

theorem canonAddFactor_coordsFull (γ k : ℝ) (x : FieldSample) :
    canonAddFactor γ k (coordsFull x) = canonData γ (addConst x k) := by
  simp only [canonAddFactor, WedgeCan4.piC_coordsFull]
  rw [← coords_addConst, canonData_reconstruct]

/-! ## 2. The field-level B4(c) input -/

/-- **B4(c) at the field level** (open input; Sheffield §1.6, DMS arXiv:1409.7055 Prop. 4.6):
for an `α`-quantum wedge `Y` and a constant `k`, a.s. the canonical scale of `Y + k` is
positive, and the canonical description `canonical γ (Y + k)` has the field law of `Y`. -/
def WedgeAddConstLawStmt : Prop :=
  ∀ (γ α : ℝ), 0 < γ → γ < 2 → α < Qc γ →
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (Y : Ω' → FieldSample), IsQuantumWedge γ α Y P' → ∀ k : ℝ,
      (∀ᵐ ω ∂P', 0 < scaleParam γ (addConst (Y ω) k)) ∧
        fieldLawFull H (fun ω => canonical γ (addConst (Y ω) k)) P' = fieldLawFull H Y P'

/-! ## 3. The reduction -/

/-- The measurable nowhere-zero squared scale `(d, a) ↦ a²` (junk `1` for `a ≤ 0`). -/
def sqScaleG {β : Type*} (p : β × ℝ) : ℝ≥0 := if 0 < p.2 then (p.2 ^ 2).toNNReal else 1

theorem measurable_sqScaleG {β : Type*} [MeasurableSpace β] :
    Measurable (sqScaleG (β := β)) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_snd)
    (measurable_snd.pow_const 2).real_toNNReal measurable_const

theorem sqScaleG_ne_zero {β : Type*} (p : β × ℝ) : sqScaleG p ≠ 0 := by
  unfold sqScaleG
  split_ifs with h
  · exact (Real.toNNReal_pos.2 (by positivity)).ne'
  · exact one_ne_zero

/-- **`PStarCanonLawStmt` from the field-level B4(c).** -/
theorem pStarCanonLawStmt_of (hB4 : WedgeAddConstLawStmt) : PStarCanonLawStmt := by
  intro κ Ω' _ P' _ Y B' hP k
  obtain ⟨hκ, hκ4, hW, hB, hI⟩ := hP
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  have hα : Real.sqrt κ - 2 / Real.sqrt κ < Qc (Real.sqrt κ) := F2.alpha_lt_Qc' hγ hγ2
  obtain ⟨hpos, hlaw⟩ := hB4 (Real.sqrt κ) _ hγ hγ2 hα P' Y hW k
  have hYm : AEMeasurable (fun ω => dataH (Y ω)) P' :=
    Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hα hW
  have hgood : ∀ᵐ ω ∂P', IsLQGGood (Real.sqrt κ) (Y ω) := Wire2.wedgeGoodStmt hγ hγ2 hα P' Y hW
  obtain ⟨ξ, hξ⟩ : ∃ ξ : Ω' → ((ℕ → ℝ) × (TestFun H → ℝ)) × ℝ,
      ξ = fun ω => canonAddFactor (Real.sqrt κ) k (coordsFull (Y ω)) := ⟨_, rfl⟩
  have hFm : Measurable fun x : FieldSample => canonAddFactor (Real.sqrt κ) k (coordsFull x) :=
    Measurable.comp (g := canonAddFactor (Real.sqrt κ) k) (f := coordsFull)
      (measurable_canonAddFactor (Real.sqrt κ) k) measurable_coordsFull
  have hcY : AEMeasurable (fun ω => coordsFull (Y ω)) P' := hYm.fst
  have hξm : AEMeasurable ξ P' := by
    rw [hξ]
    exact AEMeasurable.comp_aemeasurable (g := canonAddFactor (Real.sqrt κ) k)
      (f := fun ω => coordsFull (Y ω)) (measurable_canonAddFactor (Real.sqrt κ) k).aemeasurable hcY
  have hξI : IndepFun ξ (pathOf B') P' := by
    rw [hξ]
    exact IndepFun.comp (φ := fun x : FieldSample => canonAddFactor (Real.sqrt κ) k (coordsFull x))
      (ψ := id) hI hFm measurable_id
  have hξae : ∀ᵐ ω ∂P', ξ ω =
      (dataH (canonical (Real.sqrt κ) (addConst (Y ω) k)),
        scaleParam (Real.sqrt κ) (addConst (Y ω) k)) := by
    filter_upwards [hgood] with ω h
    rw [hξ]
    show canonAddFactor _ k (coordsFull (Y ω)) = _
    rw [canonAddFactor_coordsFull, canonData_of_good (h.addConst k)]
  obtain ⟨hBr, hBI⟩ := F2.randScale_of_aemeasurable hB hξm measurable_sqScaleG
    sqScaleG_ne_zero hξI
  obtain ⟨B'', hB''⟩ : ∃ B'' : ℝ≥0 → Ω' → ℝ, B'' = F2.rscale (sqScaleG ∘ ξ) B' := ⟨_, rfl⟩
  rw [← hB''] at hBr hBI
  have hcfg : ∀ᵐ ω ∂P', cfgData (scCfg κ k Y B' ω) = ((ξ ω).1, drivePath κ (pathOf B'' ω)) := by
    filter_upwards [hξae, hpos] with ω h1 h2
    have hB'ω : drive κ B'' ω =
        drive κ (F2.rscale (fun _ =>
          (scaleParam (Real.sqrt κ) (addConst (Y ω) k) ^ 2).toNNReal) B') ω := by
      funext r
      simp only [drive, F2.rscale, hB'', Function.comp, h1, sqScaleG, h2, ↓reduceIte]
    have e : scCfg κ k Y B' ω =
        (canonical (Real.sqrt κ) (addConst (Y ω) k), drive κ B'' ω) := by
      simp only [scCfg]
      rw [F2.canonConfig_eq_drive (Real.sqrt κ) κ _ B' ω h2, hB'ω]
    rw [e, h1]
    exact Prod.ext rfl (drive_nnreal κ B'' ω)
  have hD'' : AEMeasurable (fun ω => drivePath κ (pathOf B'' ω)) P' :=
    (measurable_drivePath κ).comp_aemeasurable (IsBrownianReal.aemeasurable_pathOf hBr)
  have hD' : AEMeasurable (fun ω => drivePath κ (pathOf B' ω)) P' :=
    (measurable_drivePath κ).comp_aemeasurable (IsBrownianReal.aemeasurable_pathOf hB)
  have hξ1 : AEMeasurable (fun ω => (ξ ω).1) P' := hξm.fst
  refine ⟨?_, (hξ1.prodMk hD'').congr (hcfg.mono fun ω h => h.symm)⟩
  -- the two product decompositions
  have e1 : configLawFull (scCfg κ k Y B') P' =
      (P'.map fun ω => (ξ ω).1).prod (P'.map fun ω => drivePath κ (pathOf B'' ω)) := by
    rw [configLawFull_eq_map_cfgData, Measure.map_congr hcfg]
    exact (indepFun_iff_map_prod_eq_prod_map_map hξ1 hD'').1
      (IndepFun.comp (φ := Prod.fst) (ψ := drivePath κ) hBI measurable_fst
        (measurable_drivePath κ))
  have e2 : configLawFull (pcfg κ Y B') P' =
      (P'.map fun ω => dataH (Y ω)).prod (P'.map fun ω => drivePath κ (pathOf B' ω)) := by
    have : configLawFull (pcfg κ Y B') P' =
        P'.map fun ω => (dataH (Y ω), drivePath κ (pathOf B' ω)) := by
      show P'.map _ = _
      congr 1
      funext ω
      exact Prod.ext rfl (drive_nnreal κ B' ω)
    rw [this]
    exact (indepFun_iff_map_prod_eq_prod_map_map hYm hD').1
      (IndepFun.comp (φ := dataH) (ψ := drivePath κ) hI measurable_dataH
        (measurable_drivePath κ))
  -- field factors: B4(c)
  have hf : (P'.map fun ω => (ξ ω).1) = P'.map fun ω => dataH (Y ω) := by
    rw [Measure.map_congr (hξae.mono fun ω h => congrArg Prod.fst h)]
    exact hlaw
  -- path factors: Brownian path law
  have hp : (P'.map fun ω => drivePath κ (pathOf B'' ω)) =
      P'.map fun ω => drivePath κ (pathOf B' ω) := by
    rw [show (fun ω => drivePath κ (pathOf B'' ω)) = drivePath κ ∘ pathOf B'' from rfl,
      show (fun ω => drivePath κ (pathOf B' ω)) = drivePath κ ∘ pathOf B' from rfl,
      ← AEMeasurable.map_map_of_aemeasurable (measurable_drivePath κ).aemeasurable
        (IsBrownianReal.aemeasurable_pathOf hBr),
      ← AEMeasurable.map_map_of_aemeasurable (measurable_drivePath κ).aemeasurable
        (IsBrownianReal.aemeasurable_pathOf hB),
      map_pathOf_eq_of_isPreBrownianReal hBr.toIsPreBrownianReal hB.toIsPreBrownianReal
        (IsBrownianReal.aemeasurable_pathOf hBr) (IsBrownianReal.aemeasurable_pathOf hB)]
  rw [e1, e2, hf, hp]

end F1
end QuantumZipper
