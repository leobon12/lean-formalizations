import QuantumZipper.Proofs.Zipper.Cor15FieldGood2Det

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# COR15-FIELDGOOD2 (2): the corrected round-trip node `Cor15UnzipZipFieldGoodStmt'` (D47)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18;
no proof in the paper). Decision D47. Task COR15-FIELDGOOD2.

`cor15UnzipZipFieldGoodStmt'_holds`: for every genuine setup, `0 < κ < 4`, `a > 0`, from
Theorem 1.3. The good set is `A ∩ FG2Set Vp … a Q` (`Cor15FieldGood2Det`), with `(Vp, A)` the
welding-driver reading of `exists_readVp`. On the unzipped configuration `D_a c`,
`c = (𝔥₀ + X, W)`, the reading is `vrev W a` on `[0,a]`, and the conditions of `FG2Set` hold a.s.:

* hull clause: `cor15HullNullStmt` (K0; as in `cor15ZipRead`);
* `RegShift` of the unzipped field at the re-zip-pushed circles: `ae_regShift_unzip_pushed_fc`;
* the zipped raw values are those of `𝔥₀ + X` minus the constant of the unzipped field
  (`ae_rezip_raw_fc`, `ae_evalReg_fc_h0rev_add`), so the last two clauses are the gauge
  regularity `RegUnif.gaugeRegDyStmt_holds` of `𝔥₀ + X` at the circles pushed by
  `fwdMapInv W a = revMap (vrev W a) a` and the definition of the unzipped field.

**Own assembly** of proved repository results (the pattern of `cor15ShiftGoodStmt_of_theorem1_3`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open B1Full CoordsFull B2

/-- **The corrected round-trip node (D47) holds**, from Theorem 1.3. -/
theorem cor15UnzipZipFieldGoodStmt'_holds (h13 : theorem1_3) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} (hS : IsGrpSetup P B X) {a : ℝ} (ha : 0 < a) :
    Cor15UnzipZipFieldGoodStmt' κ a P B X := by
  obtain ⟨hB, hX, hind⟩ := hS
  obtain ⟨Vp, hVc, hV0, hVm, A, hAm, hdet, hyA, -⟩ :=
    exists_readVp h13 RS.rohdeSchrammSimple hκ hκ4 hB hX hind ha
  refine ⟨A ∩ FG2Set Vp hVc a (Qc (Real.sqrt κ)) ha.le,
    hAm.inter (measurableSet_FG2Set hVc hV0 hVm ha _),
    fun x hxc hx => regEq_roundTrip_of_fg2 hVc hV0 ha hxc (hdet x hx.1).1 hx.2, ?_⟩
  have hK0 : ∀ᵐ ω ∂P, ∀ i : ℕ, foldedCircle (fullIndex i).1 (fullIndex i).2
      (revHull (vrev (drive κ B ω) a) a) = 0 :=
    ae_all_iff.2 fun i => cor15HullNullStmt κ hκ hκ4 a ha P B hB i
  have hA3 : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ d ∈ RegUnif.Dy,
      E1.RegShift (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) a)
        ((foldedCircle d (radius k)).map (revMapInv (vrev (drive κ B ω) a) a)) :=
    ae_all_iff.2 fun k => (eventually_countable_ball RegUnif.countable_Dy).2 fun d _ =>
      ae_regShift_unzip_pushed_fc hB hX hind hκ hκ4 ha d (radius_pos k)
  filter_upwards [hyA, b1Data_zipCapDown_snd_zero_ae (κ := κ) (a := a) (B := B) (X := X) (P := P),
    hK0, hA3, ae_rezip_raw_fc hB hX hind hκ hκ4 ha, ae_evalReg_fc_h0rev_add κ hX,
    RegUnif.gaugeRegDyStmt_holds (κ := κ) hB hX hind ha, hB.cont, hB.eval_zero_ae_eq_zero]
    with ω ⟨hA, hE⟩ h0d hK hA3ω hZ hEv hG hc h0
  refine ⟨hA, h0d, mem_iInter.2 fun k => mem_iInter₂.2 fun d hd => ?_⟩
  set W := drive κ B ω with hWdef
  set Y := ofFun (h0rev κ) + X ω with hYdef
  set e := b1Data (zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω)) with he
  set h := (zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω)).1 with hh
  set Q := Qc (Real.sqrt κ) with hQ
  set c' := h (foldedCircle 0 1) with hc'
  have hWc : Continuous W := drive_continuous hc
  have hW0 : W 0 = 0 := drive_zero h0
  have hvc : Continuous (vrev W a) := by unfold vrev; fun_prop
  have hψ : revMapInv (Vp e) a = revMapInv (vrev W a) a := revMapInv_congr_drive hE
  -- the hull clause at every dyadic circle
  have hnull : ∀ n' k' w', foldedCircle (dyadicRoundC n' w') (radius k')
      (fwdHull (ArcDriver.trev (Vp e) a) a) = 0 := by
    intro n' k' w'
    rw [fwdHull_trev_eq_of_eqOn (hVc _) hvc ha.le hE,
      CharFunRhs.fwdHull_eq_of_eqOn (ArcDriver.continuous_trev hvc a) hWc ha.le
        (trev_vrev_eqOn hW0 ha.le), ← revHull_vrev_eq_fwdHull hWc hW0 ha]
    obtain ⟨i, hi⟩ := fg2_exists_index n' k' w'
    rw [← hi]
    exact hK i
  -- `RegShift` of the unzipped field at the re-zip-pushed dyadic circles
  have hRS : ∀ n' k' w', E1.RegShift h
      ((foldedCircle (dyadicRoundC n' w') (radius k')).map (revMapInv (vrev W a) a)) := by
    intro n' k' w'
    have := hA3ω k' _ (RegUnif.foldH_dyadicRoundC_mem_Dy n' w')
    rwa [CoordReg.foldedCircle_foldH] at this
  -- the normalized unzipped field
  have hfo : RegEq (E1.fromC e.1.1) (addConst h (-c')) := fg2_regEq_of_dyadic fun n' k' w' => by
    rw [fg2_addConst_prob]
    change fieldOf h _ = _
    rw [fieldOf_apply_fc]
    ring
  -- the zipped raw values are those of `Y` minus `c'`
  have hYv : ∀ n' k' w', E1.fromC (fg2V Vp a Q e) (foldedCircle (dyadicRoundC n' w') (radius k')) =
      addConst Y (-c') (foldedCircle (dyadicRoundC n' w') (radius k')) := by
    intro n' k' w'
    obtain ⟨i, hi⟩ := fg2_exists_index n' k' w'
    have hμH : foldedCircle (dyadicRoundC n' w') (radius k') Hᶜ = 0 :=
      ae_iff.1 (TwoPoint.foldedCircle_ae_mem_H _ (radius_pos k'))
    rw [fromC_fg2V_eq hVc hV0 ha Q e ⟨i, hi⟩ hμH (hnull n' k' w'), fg2_addConst_prob, hψ]
    have : IsProbabilityMeasure ((foldedCircle (dyadicRoundC n' w') (radius k')).map
        (revMapInv (vrev W a) a)) :=
      (Measure.isProbabilityMeasure_map_iff (measurable_revMapInv hvc ha.le).aemeasurable).2
        inferInstance
    have hz := hZ i
    have hy := hEv i
    rw [hi] at hz hy
    unfold coordChange at hz ⊢
    rw [evalReg_congr_regEq hfo, E1.evalReg_addConst_of_regShift (hRS n' k' w')]
    change evalReg h _ + Q * _ = evalReg Y _ at hz
    rw [← hy, ← hz]
    ring
  have hvY : RegEq (E1.fromC (fg2V Vp a Q e)) (addConst Y (-c')) := fg2_regEq_of_dyadic hYv
  -- the unzipping map
  have hφ : EqOn (fwdMapInv W a) (fg2Phi Vp hVc a ha.le e) H := fun u hu => by
    rw [fwdMapInv_eq_revMap_vrev hWc hW0 ha.le hu]
    show _ = revMap (CharFun.Wof 1 a ha.le (fg2Path Vp hVc a e)) a u
    refine ReverseFlow.revMap_congr_drive u fun r hr => ?_
    simp [CharFun.Wof, fg2Path, projIcc_of_mem ha.le hr, hE hr]
  obtain ⟨n, w, hμ⟩ := fg2_Dy_form hd k
  show FG2At Vp hVc a Q ha.le (foldedCircle d (radius k)) e
  rw [hμ]
  have hmap : (foldedCircle (dyadicRoundC n w) (radius k)).map (fg2Phi Vp hVc a ha.le e) =
      (foldedCircle (dyadicRoundC n w) (radius k)).map (fwdMapInv W a) :=
    Measure.map_congr ((TwoPoint.foldedCircle_ae_mem_H _ (radius_pos k)).mono
      fun u hu => (hφ hu).symm)
  have hGY : E1.RegShift Y
      ((foldedCircle (dyadicRoundC n w) (radius k)).map (fg2Phi Vp hVc a ha.le e)) := by
    have := (hG a ⟨ha.le, le_rfl⟩).1 k _ (RegUnif.foldH_dyadicRoundC_mem_Dy n w)
    rw [CoordReg.foldedCircle_foldH] at this
    rw [hmap]
    exact this
  have hA3' : E1.RegShift (E1.fromC e.1.1)
      ((foldedCircle (dyadicRoundC n w) (radius k)).map (revMapInv (Vp e) a)) := by
    rw [hψ]
    exact regShift_fieldOf_iff.2 (hRS n k w)
  refine ⟨hnull n k w, hA3', regShift_congr_dyadic (fun n' k' w' => (hYv n' k' w').symm)
    (regShift_addConst hGY _), ?_⟩
  have : IsProbabilityMeasure
      ((foldedCircle (dyadicRoundC n w) (radius k)).map (fg2Phi Vp hVc a ha.le e)) :=
    (Measure.isProbabilityMeasure_map_iff
      (CharFun.measurable_revMap_Wof 1 a ha.le _).aemeasurable).2 inferInstance
  have hint : ∫ u, Real.log ‖deriv (fg2Phi Vp hVc a ha.le e) u‖
      ∂(foldedCircle (dyadicRoundC n w) (radius k)) =
      ∫ u, Real.log ‖CharFun.Dm 1 a ha.le (fg2Path Vp hVc a e, u)‖
        ∂(foldedCircle (dyadicRoundC n w) (radius k)) := by
    refine integral_congr_ae ((TwoPoint.foldedCircle_ae_mem_H _ (radius_pos k)).mono
      fun u hu => ?_)
    dsimp only
    rw [CharFun.Dm_eq 1 a ha.le _ hu]
    rfl
  have hhμ : h (foldedCircle (dyadicRoundC n w) (radius k)) =
      coordChange Y (fg2Phi Vp hVc a ha.le e) Q (foldedCircle (dyadicRoundC n w) (radius k)) :=
    CoordReg.coordChange_fc_congr Y hφ Q _ (radius_pos k)
  rw [evalReg_congr_regEq hvY, E1.evalReg_addConst_of_regShift hGY, ← hint]
  change _ = fieldOf h _
  rw [fieldOf_apply_fc, hhμ]
  unfold coordChange
  ring

end Cor15Group
end QuantumZipper
