import QuantumZipper.Proofs.Zipper.T13Hard3RealizeBasic
import QuantumZipper.Proofs.Zipper.WedgePStarRealize
import QuantumZipper.Proofs.Zipper.WedgeLawRef
import QuantumZipper.Proofs.Probability.BMExistence
import QuantumZipper.Proofs.Probability.BrownianPathMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# T13-HARD3, part 2: realization of `P_*` samples (`PStarWitnessRealizeStmt`, core P)

**Theorem.** `WedgeUnzip.pStarWitnessRealizeStmt_holds : WedgeUnzip.PStarWitnessRealizeStmt`, hence
`WedgeUnzip.pStarRealizeStmt_holds : WedgeUnzip.PStarRealizeStmt`.

Source: the transfer theorem, Kallenberg, *Foundations of Modern Probability*, 2nd ed.,
Thm. 6.10 (with Thm. 6.3, disintegration, and Lemma 3.22, randomization), in the form
`T13Hard3.exists_transfer` (part 1). The argument:

1. A reference witness `(X₀, A₀)` (free field mod constants ⊥ wedge process) on the *standard
   Borel* space `RefΩ = (ℕ → ℝ)³` with `P₀ = stdP ⊗ stdP ⊗ stdP` (`exists_freeGFF_stdP`,
   `BMExist.exists_isBrownianReal_stdP`, bookkeeping as in `NonVacuity.exists_wedge_indep_BM`).
2. The sample coordinate `coordsFull ∘ Y` and the reference coordinate
   `coordsFull ∘ canonical γ ∘ zU γ X₀ A₀` (a.e. equal to the measurable `FSMeas.xiU`) have the
   same law: the first marginals of `fieldLawFull H`, equal by `IsQuantumWedge` and
   `Prop16Asm.refWedgeLawUnique_holds`.
3. Transfer gives `G : Ω' × I → RefΩ`, measure preserving, of the form `f (coord(Y ω.1), ω.2)`,
   with the reference coordinate of `G ω` equal to the sample coordinate a.s.; put
   `X' = X₀ ∘ G`, `A = A₀ ∘ G`. Independence from the lifted driver holds because `G` is a
   measurable function of `(coord(Y ω.1), ω.2)`, independent of `pathOf B' ω.1`.
4. `avgReg` is read from `coordsFull` (`CoordsFull.coordsFull_apply_eq`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal

namespace QuantumZipper
namespace T13Hard3

open CoordsFull LQGDimension.ExistAsm

/-- The reference carrier: three i.i.d. Gaussian sequences (a standard Borel space). -/
abbrev RefΩ : Type := (ℕ → ℝ) × ((ℕ → ℝ) × (ℕ → ℝ))

/-- The reference probability measure. -/
abbrev refP : Measure RefΩ := stdP.prod (stdP.prod stdP)

theorem coordsFull_sfTrunc (y : FieldSample) : coordsFull (FSMeas.sfTrunc y) = coordsFull y := by
  funext i
  exact FSMeas.sfTrunc_apply _ _

/-- `avgReg` is determined by the full coordinates. -/
theorem avgReg_eq_of_coordsFull {x x' : FieldSample} (h : coordsFull x = coordsFull x') :
    avgReg x = avgReg x' := by
  funext k z
  have hr : radius k = ((1 : ℤ) : ℝ) / (2 : ℝ) ^ k := by simp [radius, inv_pow]
  unfold avgReg
  congr 1
  funext n
  rw [hr]
  exact coordsFull_apply_eq h n z 1 one_pos k

/-- The first marginal of `fieldLawFull` is the law of the full coordinates. -/
theorem map_fst_fieldLawFull {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : Ω → FieldSample} (h : AEMeasurable (fun ω => WedgeMeas.dataFull H (Z ω)) P) :
    (fieldLawFull H Z P).map Prod.fst = P.map (fun ω => coordsFull (Z ω)) := by
  exact AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable h

/-- Wedge processes are transported by measure-preserving maps. -/
theorem isWedgeProcess_comp_mp {Ω Ω₀ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀]
    {μ : Measure Ω} {P₀ : Measure Ω₀} {G : Ω → Ω₀} (hG : MeasurePreserving G μ P₀)
    {α Q : ℝ} {A₀ : ℝ → Ω₀ → ℝ} (h : IsWedgeProcess α Q A₀ P₀) :
    IsWedgeProcess α Q (fun t ω => A₀ t (G ω)) μ := by
  obtain ⟨B1, B2, h1, h2, h12, hA⟩ := h
  exact ⟨fun t ω => B1 t (G ω), fun t ω => B2 t (G ω), NonVacuity.nv_isBrownianReal hG h1,
    NonVacuity.nv_isBrownianReal hG h2,
    indepFun_comp_mp hG (IsBrownianReal.aemeasurable_pathOf h1)
      (IsBrownianReal.aemeasurable_pathOf h2) h12,
    fun ω t => hA (G ω) t⟩

/-- The reference witness on the standard Borel carrier. -/
theorem exists_ref_witness (α Q : ℝ) :
    ∃ (X₀ : RefΩ → FieldSample) (A₀ : ℝ → RefΩ → ℝ), IsFreeGFFModConstH X₀ refP ∧
      IsWedgeProcess α Q A₀ refP ∧ IndepFun X₀ (fun ω t => A₀ t ω) refP := by
  obtain ⟨X, hX⟩ := exists_freeGFF_stdP
  obtain ⟨B, hB⟩ := BMExist.exists_isBrownianReal_stdP
  have h1 : MeasurePreserving (fun ω : RefΩ => ω.2.1) refP stdP :=
    measurePreserving_fst.comp measurePreserving_snd
  have h2 : MeasurePreserving (fun ω : RefΩ => ω.2.2) refP stdP :=
    measurePreserving_snd.comp measurePreserving_snd
  refine ⟨fun ω => X ω.1, fun t ω =>
    wedgePath α Q (fun s => B s ω.2.1) (fun s => B s ω.2.2) t,
    NonVacuity.nv_freeGFF measurePreserving_fst hX, ?_, ?_⟩
  · refine ⟨fun t ω => B t ω.2.1, fun t ω => B t ω.2.2, NonVacuity.nv_isBrownianReal h1 hB,
      NonVacuity.nv_isBrownianReal h2 hB, ?_, fun ω t => rfl⟩
    exact NonVacuity.nv_indepFun_snd (NonVacuity.nv_indepFun_prod (pathOf B) (pathOf B))
  · exact NonVacuity.nv_indepFun_prod (μ := stdP) (ν := stdP.prod stdP) X
      (fun (ω : (ℕ → ℝ) × (ℕ → ℝ)) (t : ℝ) =>
        wedgePath α Q (fun s => B s ω.1) (fun s => B s ω.2) t)

end T13Hard3

namespace WedgeUnzip

open T13Hard3 CoordsFull

/-- **Core P-witness holds** (transfer theorem, Kallenberg FMP Thm. 6.10). -/
theorem pStarWitnessRealizeStmt_holds : PStarWitnessRealizeStmt := by
  intro κ Ω' _ P' _ Y B' hPS
  obtain ⟨hκ, hκ4, hW, hB', hYB⟩ := hPS
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  have hα : Real.sqrt κ - 2 / Real.sqrt κ < Qc (Real.sqrt κ) := F2.alpha_lt_Qc' hγ hγ2
  set γ := Real.sqrt κ with hγdef
  obtain ⟨X₀, A₀, hX₀, hA₀, hI₀⟩ := exists_ref_witness (γ - 2 / γ) (Qc γ)
  -- the reference coordinate
  obtain ⟨hxiM, -, hxiE⟩ := FSMeas.xiU_spec hγ hγ2 hα hX₀ hA₀ hI₀
    (indepFun_const_right (fun ω => (X₀ ω, fun t => A₀ t ω)) (0 : ℝ))
  set ξ₀ : RefΩ → (ℕ → ℝ) := fun ω => coordsFull (FSMeas.xiU γ X₀ A₀ ω).1 with hξ₀def
  have hξ₀ : AEMeasurable ξ₀ refP :=
    measurable_coordsFull.comp_aemeasurable (measurable_fst.comp_aemeasurable hxiM)
  have hξ₀e : ∀ᵐ ω ∂refP, hξ₀.mk ξ₀ ω = coordsFull (canonical γ (F2.zU γ X₀ A₀ ω)) := by
    filter_upwards [hξ₀.ae_eq_mk, hxiE] with ω h1 h2
    rw [← h1, hξ₀def]
    simp only [h2, coordsFull_sfTrunc]
  -- the sample coordinate
  have hdata := Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hα hW
  have hYc : AEMeasurable (fun ω => coordsFull (Y ω)) P' :=
    measurable_fst.comp_aemeasurable hdata
  -- same law
  have hW₀ : IsQuantumWedge γ (γ - 2 / γ) (WedgeMeas.wedgeRef γ X₀ A₀) refP :=
    ⟨hα, RefΩ, inferInstance, refP, X₀, A₀, inferInstance, hX₀, hA₀, hI₀, rfl⟩
  have hdata₀ := Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hα hW₀
  have hlaw : P'.map (hYc.mk _) = refP.map (hξ₀.mk ξ₀) := by
    obtain ⟨-, Ω'', _, P'', Xw, Aw, hP'', hXw, hAw, hIw, hlawW⟩ := hW
    calc P'.map (hYc.mk _) = P'.map (fun ω => coordsFull (Y ω)) :=
          Measure.map_congr hYc.ae_eq_mk.symm
      _ = (fieldLawFull H Y P').map Prod.fst := (map_fst_fieldLawFull hdata).symm
      _ = (fieldLawFull H (WedgeMeas.wedgeRef γ X₀ A₀) refP).map Prod.fst := by
          rw [hlawW]
          exact congrArg _ (Prop16Asm.refWedgeLawUnique_holds hγ hγ2 hα Ω'' RefΩ _ _ P'' refP
            Xw Aw X₀ A₀ hP'' hXw hAw hIw inferInstance hX₀ hA₀ hI₀)
      _ = refP.map (fun ω => coordsFull (WedgeMeas.wedgeRef γ X₀ A₀ ω)) :=
          map_fst_fieldLawFull hdata₀
      _ = refP.map (hξ₀.mk ξ₀) := Measure.map_congr (hξ₀e.mono fun ω h => h.symm)
  -- transfer
  obtain ⟨f, hf, hGmp, hGae⟩ := exists_transfer hξ₀.measurable_mk hYc.measurable_mk hlaw
  refine ⟨unitInterval, inferInstance, volume, inferInstance,
    fun ω => X₀ (f (hYc.mk _ ω.1) ω.2), fun t ω => A₀ t (f (hYc.mk _ ω.1) ω.2),
    NonVacuity.nv_freeGFF hGmp hX₀, isWedgeProcess_comp_mp hGmp hA₀,
    indepFun_comp_mp hGmp (WedgeTK.measurable_X_pi hX₀).aemeasurable
      (ZoomRadial.aemeasurable_wedgePath hA₀) hI₀, ?_, ?_⟩
  · -- independence from the lifted driver
    have hw₀ : AEMeasurable (fun ω => (X₀ ω, fun t => A₀ t ω)) refP :=
      (WedgeTK.measurable_X_pi hX₀).aemeasurable.prodMk (ZoomRadial.aemeasurable_wedgePath hA₀)
    have hpm := IsBrownianReal.aemeasurable_pathOf hB'
    have hsb : IndepFun (hYc.mk _) (hpm.mk _) P' :=
      (hYB.comp measurable_coordsFull measurable_id).congr hYc.ae_eq_mk hpm.ae_eq_mk
    have hV := (indepFun_pair_fst (Q := (volume : Measure unitInterval)) hYc.measurable_mk
      hpm.measurable_mk hsb).comp (hw₀.measurable_mk.comp hf) measurable_id
    have hae1 : (fun ω : Ω' × unitInterval => hpm.mk _ ω.1) =ᵐ[P'.prod volume]
        pathOf (WedgeUnzip.liftPath B') :=
      measurePreserving_fst.quasiMeasurePreserving.ae_eq_comp hpm.ae_eq_mk.symm
    have hae2 : (fun ω : Ω' × unitInterval => hw₀.mk _ (f (hYc.mk _ ω.1) ω.2)) =ᵐ[P'.prod volume]
        (fun ω => (X₀ (f (hYc.mk _ ω.1) ω.2), fun t => A₀ t (f (hYc.mk _ ω.1) ω.2))) :=
      hGmp.quasiMeasurePreserving.ae_eq_comp hw₀.ae_eq_mk.symm
    exact hV.congr hae2 hae1
  · -- the `avgReg` identity
    have h1 := hGmp.quasiMeasurePreserving.ae hξ₀e
    have h2 : ∀ᵐ ω ∂(P'.prod (volume : Measure unitInterval)),
        hYc.mk _ ω.1 = coordsFull (Y ω.1) :=
      measurePreserving_fst.quasiMeasurePreserving.ae hYc.ae_eq_mk.symm
    filter_upwards [hGae, h1, h2] with ω e1 e2 e3
    exact avgReg_eq_of_coordsFull (e3.symm.trans (e1.symm.trans e2))

/-- **Core P holds.** -/
theorem pStarRealizeStmt_holds : PStarRealizeStmt :=
  pStarRealizeStmt_of_witnessStmt pStarWitnessRealizeStmt_holds

end WedgeUnzip
end QuantumZipper
