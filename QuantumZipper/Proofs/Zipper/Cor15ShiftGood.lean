import QuantumZipper.Proofs.Zipper.Cor15ShiftGoodReg
import QuantumZipper.Proofs.Zipper.Cor15ZipFixLaw
import QuantumZipper.Proofs.Zipper.RegShiftUnif
import QuantumZipper.Proofs.Zipper.JointModFinal
import QuantumZipper.Proofs.Zipper.Cor15PosDriver
import QuantumZipper.Proofs.Zipper.Cor15PosZip
import QuantumZipper.Proofs.RS.RohdeSchrammSimple

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# COR15-SHIFTGOOD (3): the a.s. good set `Cor15ShiftGoodStmt` (D42), from Theorem 1.3

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18),
§5.1 (rule (5.1): the field is regular at the pushed circles). Decision D42 (`DECISIONS.md`).

`cor15ShiftGoodStmt_of_theorem1_3 : theorem1_3 → Cor15ShiftGoodStmt`. At a genuine
configuration `c = (𝔥₀ + X, W)`, `W = √κ B`, `CCGood` (`Cor15ZipFixBasic`) holds a.s.:

* **`D_t`** (`ψ = fwdMapInv W t`): the regularized part is the proved gauge statement
  `RegUnif.gaugeRegDyStmt_holds` (`E1.RegShift` of `𝔥₀ + X` at the pushed dyadic circles, from the
  D33 uniform-Cauchy closure), and the raw part is the raw convergence of the unzipped field
  (`RegUnif.ae_forall_isRegularSample`, joint modulus; Duplantier–Sheffield 2011, Prop. 3.1);
* **`U_0`** (`ψ = revMapInv (weldDriver …) 0 = id` on `ℍ`): the same two facts at `t = 0`;
* **`U_t` at `D_t c`**: a.s. the welding driver of the unzipped field is `V = vrev W t` on `[0,t]`
  (`ae_eqOn_weldDriver_zipCapDown`, Theorem 1.3 + Rohde–Schramm simplicity, proved), so
  `ψ = f_t = revMapInv V t`. The regularized part is `ae_regShift_unzip_pushed_fc`
  (`Cor15ShiftGoodReg`); the raw part is the raw re-zip identity at the enumerated dyadic
  circles (`rezip_apply` with the proved (K0) `cor15HullNullStmt` and (R) `cor15RezipRegStmt`):
  the zipped raw values are `evalReg (𝔥₀ + X) σ = y₀ σ`, `y₀` the (regular) unzipped field at
  time `0`, whose raw averages converge.

Also `theorem1_5_of_theorem1_3_of_fieldGood_read`: Corollary 1.5 from Theorem 1.3 and the two
remaining D42 nodes. **Own elementary assembly** (`CCGood` bookkeeping).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open CharFun B2

/-- **Deterministic criterion for `CCGood`**: `ψ = φ` on `ℍ`, `E1.RegShift` of `y` at every
`φ`-pushed dyadic folded circle centred in `Dy`, and raw convergence of `coordChange y φ Q`. -/
theorem ccGood_of_regShift {y : FieldSample} {ψ φ : ℂ → ℂ} {Q : ℝ} (hψ : EqOn ψ φ H)
    (hA : ∀ k : ℕ, ∀ d ∈ RegUnif.Dy, E1.RegShift y ((foldedCircle d (radius k)).map φ))
    (hraw : LocalRule.RawConverges (coordChange y φ Q) univ) : CCGood y ψ Q := by
  refine ⟨fun k n z => ?_, fun k z => ?_⟩
  · have e : (foldedCircle (dyadicRoundC n z) (radius k)).map ψ =
        (foldedCircle (foldH (dyadicRoundC n z)) (radius k)).map φ := by
      rw [CoordReg.foldedCircle_foldH]
      exact Measure.map_congr
        ((TwoPoint.foldedCircle_ae_mem_H _ (radius_pos k)).mono fun w hw => hψ hw)
    have h := (hA k _ (RegUnif.foldH_dyadicRoundC_mem_Dy n z)).2
    rw [← e] at h
    exact h
  · obtain ⟨l, hl⟩ := hraw k z (mem_univ z)
    exact ⟨l, hl.congr fun n => (CoordReg.coordChange_fc_congr y hψ Q _ (radius_pos k)).symm⟩

/-- At time `0` the inverse forward map is the identity on `ℍ`. -/
theorem fwdMapInv_zero_eqOn_id {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) :
    EqOn (fwdMapInv W 0) id H := fun w hw => by
  rw [fwdMapInv_eq_revMap_vrev hW hW0 le_rfl hw]
  exact CharFun.revMap_zero_eq (continuous_vrev hW 0) (by simp [vrev]) hw

/-- The regularized value of the field at a folded circle is the raw value of the time-`0`
unzipped field there. -/
theorem evalReg_fc_eq_unzip_zero (γ : ℝ) {x : FieldSample × (ℝ → ℝ)} (hW : Continuous x.2)
    (hW0 : x.2 0 = 0) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    evalReg x.1 (foldedCircle w r) = unzippedField γ x 0 (foldedCircle w r) := by
  show _ = coordChange x.1 (fwdMapInv x.2 0) (Qc γ) _
  rw [CoordReg.coordChange_fc_congr x.1 (fwdMapInv_zero_eqOn_id hW hW0) _ w hr,
    Cor15Partial.coordChange_id_apply]

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **Raw re-zip identity at the enumerated dyadic circles** (from the proved (K0) and (R)). -/
theorem ae_rezip_raw_fc (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ∀ i : ℕ,
      coordChange (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t)
          (revMapInv (vrev (drive κ B ω) t) t) (Qc (Real.sqrt κ))
          (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
        evalReg (ofFun (h0rev κ) + X ω)
          (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) := by
  filter_upwards [ae_all_iff.2 (cor15HullNullStmt κ hκ hκ4 t ht P B hB),
    ae_all_iff.2 (cor15RezipRegStmt κ hκ hκ4 t ht P B X hB hX hind), hB.cont,
    hB.eval_zero_ae_eq_zero] with ω hk hr hc h0 i
  have hWc : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  have hVc : Continuous (vrev (drive κ B ω) t) := continuous_vrev hWc t
  have hri := UnzipFull.fullIndex_radius_pos i
  have hHc : foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 Hᶜ = 0 :=
    ae_iff.1 (TwoPoint.foldedCircle_ae_mem_H _ hri)
  have hμ : foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2
      (revMap (vrev (drive κ B ω) t) t '' H)ᶜ = 0 := by
    refine measure_mono_null (fun z hz => ?_) (measure_union_null hHc (hk i))
    by_cases hzH : z ∈ H
    · exact Or.inr ⟨hzH, hz⟩
    · exact Or.inl hzH
  exact rezip_apply hVc ht.le _ _ (fun z hz => fwdMapInv_eq_revMap_vrev hWc hW0 ht.le hz) hμ
    (hr i)

/-- **`Cor15ShiftGoodStmt` from Theorem 1.3.** -/
theorem cor15ShiftGoodStmt_of_theorem1_3 (h13 : theorem1_3) : Cor15ShiftGoodStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hS
  obtain ⟨hB, hX, hind⟩ := hS
  have hreg := RegUnif.ae_forall_isRegularSample (κ := κ) (γ := Real.sqrt κ) hB hX hind
  refine ⟨?_, fun t ht => ?_⟩
  · filter_upwards [RegUnif.gaugeRegDyStmt_holds (κ := κ) hB hX hind one_pos, hreg, hB.cont,
      hB.eval_zero_ae_eq_zero] with ω hG hR hc h0
    have hWc : Continuous (drive κ B ω) := drive_continuous hc
    have hW0 : drive κ B ω 0 = 0 := drive_zero h0
    obtain ⟨hVc, hV0, -, -⟩ := weldDriver_spec
      ⟨_, Cor15Partial.isWeldingDriver_zero (Real.sqrt κ) (grpCfg κ B X ω).1⟩
    have hψ : EqOn (revMapInv (weldDriver (Real.sqrt κ) (grpCfg κ B X ω).1 0) 0)
        (fwdMapInv (drive κ B ω) 0) H := fun w hw => by
      rw [Cor15Partial.revMapInv_zero_eqOn hVc hV0 hw, fwdMapInv_zero_eqOn_id hWc hW0 hw]
    exact ccGood_of_regShift hψ (hG 0 ⟨le_rfl, zero_le_one⟩).1 (hR 0 le_rfl).2
  have hA : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ d ∈ RegUnif.Dy,
      E1.RegShift (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t)
        ((foldedCircle d (radius k)).map (revMapInv (vrev (drive κ B ω) t) t)) :=
    ae_all_iff.2 fun k => (eventually_countable_ball RegUnif.countable_Dy).2 fun d _ =>
      ae_regShift_unzip_pushed_fc hB hX hind hκ hκ4 ht d (radius_pos k)
  filter_upwards [RegUnif.gaugeRegDyStmt_holds (κ := κ) hB hX hind ht, hreg, hB.cont,
    hB.eval_zero_ae_eq_zero,
    ae_eqOn_weldDriver_zipCapDown h13 RS.rohdeSchrammSimple hκ hκ4 P B X hB hX hind ht, hA,
    ae_rezip_raw_fc hB hX hind hκ hκ4 ht] with ω hG hR hc h0 hE hAω hZω
  have hWc : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  refine ⟨ccGood_of_regShift (fun _ _ => rfl) (hG t ⟨ht.le, le_rfl⟩).1 (hR t ht.le).2, ?_⟩
  have e := revMapInv_congr_drive hE
  show CCGood (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1
    (revMapInv (weldDriver (Real.sqrt κ)
      (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1 t) t)
    (Qc (Real.sqrt κ))
  rw [e]
  refine ccGood_of_regShift (fun _ _ => rfl) hAω fun k z _ => ?_
  obtain ⟨l, hl⟩ := (hR 0 le_rfl).2 k z (mem_univ z)
  refine ⟨l, hl.congr fun n => ?_⟩
  obtain ⟨i, hi⟩ := CoordsFull.fullIndex_surj n z 1 one_pos k
  have hfc : foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 =
      foldedCircle (dyadicRoundC n z) (radius k) := by
    rw [hi]
    congr 1
    simp [radius, inv_pow]
  have hZ := hZω i
  rw [hfc] at hZ
  exact (evalReg_fc_eq_unzip_zero (Real.sqrt κ) (x := (ofFun (h0rev κ) + X ω, drive κ B ω))
    hWc hW0 _ (radius_pos k)).symm.trans hZ.symm

end Cor15Group
end QuantumZipper
