import QuantumZipper.Proofs.Zipper.Cor15RegBasic

/-!
# COR15-HREG (2), first reductions for `hZc`, `hZy`

* `zipCapUp_eq_fromC`: `Z_t x` reads `x.1` only through its full circle coordinates, exactly
  (no additive constant, hence no `RegShift` condition): `Z_t x = Z_t (fromC (coordsFull x.1), x.2)`.
  So `mod0Data (Z_t x)` is a function of `(coordsFull x.1, x.2)`.
* `aemeasurable_coordsFull_c`, `aemeasurable_coordsFull_unzip`: the full circle coordinates of
  `c.1 = 𝔥₀ + X` and of the unzipped field `(D_t c).1` are a.e.-measurable (the second as in the
  proof of `B2.aemeasurable_data_unzip`).

Own elementary arguments.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open B1Full CoordsFull CharFun UnzipInvariance UnzipFull

theorem regEq_fromC_coordsFull (x : FieldSample) : RegEq x (E1.fromC (coordsFull x)) :=
  fun k z => by rw [avgReg_congr_full (E1.coordsFull_fromC x).symm]

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

omit [IsProbabilityMeasure P] in
theorem measurable_coordsFull_c (κ : ℝ) (hX : IsFreeGFFModConstH X P) :
    Measurable fun ω => coordsFull (ofFun (h0rev κ) + X ω) :=
  measurable_pi_iff.2 fun _ => measurable_const.add (hX.measurable_coord _)

theorem aemeasurable_coordsFull_unzip (κ : ℝ) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {s : ℝ} (hs : 0 ≤ s) :
    AEMeasurable (fun ω => coordsFull
      (zipCapDown (Real.sqrt κ) s (ofFun (h0rev κ) + X ω, drive κ B ω)).1) P := by
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  obtain ⟨B', -, hB'm, hB'c, -, hEq⟩ := exists_unzip_driver κ hB hind hs
  obtain ⟨g, hg⟩ : ∃ g : Ω → C(Icc (0 : ℝ) s, ℝ), g = pathC s B' hB'c := ⟨_, rfl⟩
  have hgm : Measurable g := hg ▸ measurable_pathC s hB'm hB'c
  have hgood : ∀ᵐ ω ∂P, EqOn (fwdMapInv (drive κ B ω) s) (revMap (Wof κ s hs (g ω)) s) H := by
    filter_upwards [hEq] with ω h
    rwa [revMap_drive_eq κ s hs B' hB'c ω, ← hg] at h
  have hfcH : ∀ i, foldedCircle (fullIndex i).1 (fullIndex i).2 Hᶜ = 0 := fun i =>
    ae_iff.1 (TwoPoint.foldedCircle_ae_mem_H _ (fullIndex_radius_pos i))
  have hm : Measurable fun ω => coordsFull (coordChange (ofFun (h0rev κ) + X ω)
      (revMap (Wof κ s hs (g ω)) s) (Qc (Real.sqrt κ))) :=
    measurable_pi_iff.2 fun i => by
      have key := (measurable_unzip_apply κ s hs _ (hfcH i)).comp (hgm.prodMk hXm)
      simp only [Function.comp_def] at key
      exact key
  refine hm.aemeasurable.congr ?_
  filter_upwards [hgood] with ω hgd
  funext i
  exact (coordChange_congr_of_eqOn hgd (hfcH i) _ _).symm

end Cor15Group
end QuantumZipper
