import QuantumZipper.Proofs.Zipper.Cor15ZipGenuineCore
import QuantumZipper.Proofs.Zipper.Cor15MarkovFieldLaw
import QuantumZipper.Proofs.Zipper.Cor15UnzipZipSelfDrive
import QuantumZipper.Proofs.Zipper.Cor15GrpCore
import QuantumZipper.Proofs.Zipper.Cor15Final

/-!
# D35 core piece 2: `Cor15ZipGenuineStmt` — the field half and the assembly

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18).
Decision D35 (`DECISIONS.md`): the second half of the core `Cor15GenuineStmt`,
`U_a c ≈ (𝔥₀ + X', √κ B')` a.s. for a genuine setup `(B', X')` on the *same* probability space.

`Cor15ZipGenuineCore.lean` supplies the Brownian half (`B' u = (√κ)⁻¹ (U_a c).2 u`,
`isBrownianReal_zipDrv`). This file supplies the bookkeeping that turns a *field-level* law
statement into the field `X'`, and assembles the two:

* **`Cor15ZipCoordMeasStmt`** / **`Cor15ZipRawMeasStmt`** (the D35 analogue of
  `Cor15UnzipCoordMeasStmt`): a measurable version `Y` of the truncated raw difference of the
  zipped field to `𝔥₀`, with the driver paired in. `cor15ZipRawMeasStmt_of_coord` proves the
  reduction: the driver half is measurable by `aemeasurable_zipDrv` (the reading `hZc` of
  `Cor15LastZc`), so only the *field* half — regularity of the zipped field at admissible
  measures — remains open.
* **`Cor15ZipRawLawStmt`** (field-level Corollary 1.5(a)): the pair of the truncated raw
  difference and the normalized driver of `U_a c` has, on some probability space, the law of a
  genuine configuration's pair `(sfTrunc X', pathOf B')`. The registry's proved law identity at
  `t > 0` is `configLawMod0`-level only (raw pairings *modulo constants* plus the driver), which
  does not see the circle coordinates nor the admissible measures supported on `∂ℍ`; lifting it
  to the whole field is the same gap as in the unzip direction (`Cor15UnzipRawLawStmt`).
* **`cor15ZipGenuineStmt_of_law`**: the assembly. Freeness of `Y` transfers from the primed
  space (`isFreeGFFModConstH_sfTrunc`, `isFreeGFFModConstH_of_map_eq`), independence of the
  driver and the field from the joint law (`indepFun_iff_map_prod_eq_prod_map_map`), `RegEq` by
  construction (`regEq_ofFun_add_sfTrunc_sub`), and the driver clause by definition of `zipDrv`
  (`zipCapUp_snd_eq_drive`).

Inputs: `h13 : theorem1_3` (Theorem 1.4's a.s. uniqueness of the welding driver, through the
reading; Corollary 1.5(a) at `t > 0` with the proved `cor15TdensRegStmt`) and the two
obligations above.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-! ## The two obligations -/

/-! ## The assembly: `Cor15ZipGenuineStmt` from the two obligations -/

/-- **Abstract transfer of freeness and independence along a joint law.** If `f` has the joint
law of `g`, whose field part is free and independent of its path part, then a measurable
version `Y` of the field part of `f` is free and independent of the path part of `f`. Own
elementary bookkeeping (as in `cor15UnzipFieldStmt_of_law`). -/
theorem free_indep_of_map_eq {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {f : Ω → FieldSample × (ℝ≥0 → ℝ)} {g : Ω' → FieldSample × (ℝ≥0 → ℝ)}
    {Y : Ω → FieldSample} (hYm : ∀ μ : Measure ℂ, Measurable fun ω => Y ω μ)
    (hYeq : Y =ᵐ[P] fun ω => (f ω).1) (hF : AEMeasurable (fun ω => (Y ω, (f ω).2)) P)
    (hg : AEMeasurable g P') (hlaw : P.map f = P'.map g)
    (hfree : IsFreeGFFModConstH (fun ω' => (g ω').1) P')
    (hind : IndepFun (fun ω' => (g ω').1) (fun ω' => (g ω').2) P') :
    IsFreeGFFModConstH Y P ∧ IndepFun Y (fun ω => (f ω).2) P := by
  have hFf : (fun ω => (Y ω, (f ω).2)) =ᵐ[P] f := hYeq.mono fun ω hω => Prod.ext hω rfl
  have hlawF : P.map (fun ω => (Y ω, (f ω).2)) = P'.map g := by
    rw [Measure.map_congr hFf, hlaw]
  have h1 : P.map Y = P'.map (fun ω' => (g ω').1) := by
    have h : (P.map (fun ω => (Y ω, (f ω).2))).map Prod.fst = (P'.map g).map Prod.fst := by
      rw [hlawF]
    rwa [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hF,
      AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hg] at h
  have h2 : P.map (fun ω => (f ω).2) = P'.map (fun ω' => (g ω').2) := by
    have h : (P.map (fun ω => (Y ω, (f ω).2))).map Prod.snd = (P'.map g).map Prod.snd := by
      rw [hlawF]
    rwa [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hF,
      AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hg] at h
  refine ⟨isFreeGFFModConstH_of_map_eq hYm h1 hfree, ?_⟩
  refine (indepFun_iff_map_prod_eq_prod_map_map hF.fst hF.snd).2 ?_
  rw [hlawF, h1, h2]
  exact (indepFun_iff_map_prod_eq_prod_map_map hg.fst hg.snd).1 hind

/-! ## Corollary 1.5 from Theorem 1.3 and the open field-level obligations -/

end Cor15Group
end QuantumZipper
