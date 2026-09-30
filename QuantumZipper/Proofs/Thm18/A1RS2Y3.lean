import QuantumZipper.Proofs.Thm18.A1RS2R3
import QuantumZipper.Proofs.Thm18.A1RS2Prof
import QuantumZipper.Proofs.Thm18.G1SSR2UC

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS2 (8): (R3) for the Theorem 1.8 field: continuity of the member at `ρ = 0`

* `measurable_g1zSideMap`, `smearFam_zero_eq`: for a good driver, the member of the smeared
  family at `ρ = 0` is `ψ_* fc(d, s)` (`ψ = g1zSideMap left W`; `f_t⁻¹ ∘ f_t = id` off the hull,
  `RS.fwdMapInv_fwdMap`, and `A1RF.map_prod_zero`);
* **`ae_continuousOn_smearFam_zero`**: a.s., for both sides, `p ↦ evalReg Y (ν_{p,0})` is
  continuous on `smearU` (the countable Cauchy condition `G1SSR2.UCond` at the selected side map,
  transferred from the representative exactly as in `g1SidePushContStmt_of_rep` (G1SSR2Meas.lean),
  then `continuousOn_evalReg_push` and the dilation relating `g1zSideMap` to the selection).

Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm Thm18Asm.G1SSR2

theorem measurable_g1zSideMap {W : ℝ → ℝ} (hG : G1zDrvGood W) (left : Bool) :
    Measurable (g1zSideMap left W) :=
  (G1.invFunOn_props (G1ZA1a.isOpen_sideDom hG.2.2.2.1 left)
    (G1ZA1a.isNormalizedUniformizer_sideDom hG.2.2.2.1 left)).2.2.1

/-- **The member at `ρ = 0` is the pushed side circle.** -/
theorem smearFam_zero_eq {W : ℝ → ℝ} (hG : G1zDrvGood W) (left : Bool) {p : Fin 4 → ℝ}
    (hp : p ∈ smearU) :
    smearFam W left p 0 = (foldedCircle (parD p) (p 3)).map (g1zSideMap left W) := by
  obtain ⟨ht, hs⟩ := hp
  obtain ⟨-, hmapsH, g, hgm, hEq⟩ := A1R.sidePush_props hG ht left
  have hfm : Measurable (fwdMapInv W (p 0)) := RTBeur.measurable_fwdMapInv_rt hG.1 hG.2.1 ht.le
  have hψm := measurable_g1zSideMap hG left
  have hmu : a1rMu W (p 0) left (parD p) (p 3) = (foldedCircle (parD p) (p 3)).map g := by
    unfold a1rMu
    refine Measure.map_congr ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H (parD p) hs] with u hu
    exact hEq hu
  have hH : ∀ᵐ z ∂a1rMu W (p 0) left (parD p) (p 3), z ∈ Hbar := by
    rw [hmu]
    refine (ae_map_iff hgm.aemeasurable isClosed_Hbar.measurableSet).2 ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H (parD p) hs] with u hu
    rw [← hEq hu]
    exact show 0 ≤ _ from le_of_lt (hmapsH hu)
  have e0 : smearFam W left p 0 = (a1rMu W (p 0) left (parD p) (p 3)).map (fwdMapInv W (p 0)) :=
    A1RF.map_prod_zero hH hfm
  rw [e0, hmu, Measure.map_map hfm hgm]
  refine Measure.map_congr ?_
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H (parD p) hs] with u hu
  simp only [Function.comp_apply]
  rw [← hEq hu]
  exact RS.fwdMapInv_fwdMap hG.1 hG.2.1 ht.le (sideMap_mem_compl_fwdHull hG ht.le left hu)

/-- **(R3) for the Theorem 1.8 field.** A.s., for both sides, the regularized pairings of `Y`
against the members `ν_{p,0} = ψ_* fc(d, s)` of the smeared family are continuous in
`p ∈ smearU`. -/
theorem ae_continuousOn_smearFam_zero (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample)
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) (left : Bool) :
    ∀ᵐ ω ∂P, ContinuousOn (fun p => evalReg (Y ω) (smearFam (drive (γ ^ 2) B ω) left p 0))
      smearU := by
  have hS0 := hS
  have hS' := hS
  obtain ⟨hγ, hγ2, hB, hY, hind⟩ := hS
  obtain ⟨hα, Ω', _, P', X, A, hP', hX, hA, hXA, hlaw⟩ := hY
  obtain ⟨Ψ, hΨ⟩ := g1PsiSelStmt γ hγ hγ2
  set E : Set G1PathData := {p | ∀ l : Bool, UCond (E1.fromC p.2.1) (Ψ l p.1)} with hEdef
  have hE : MeasurableSet E :=
    measurableSet_setOfPred.2 (Measurable.forall fun l => measurable_ucond hΨ l)
  have hfromC : ∀ y : FieldSample, avgReg (E1.fromC (WedgeMeas.dataFull H y).1) = avgReg y :=
    fun y => CoordsFull.avgReg_congr_full (E1.coordsFull_fromC y)
  have hae : ∀ᵐ a ∂(P.map (pathOf B)), ∀ᵐ ω' ∂P',
      (a, WedgeMeas.dataFull H (wedgeRep γ X A ω')) ∈ E := by
    filter_upwards [g1SidePushUCRepStmt_holds γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ] with a ha
    filter_upwards [ha true, ha false] with ω' ht hf
    intro l
    rw [ucond_congr (hfromC _)]
    cases l
    · exact hf
    · exact ht
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  have hrep : IsQuantumWedge γ (γ - 2 / γ) (wedgeRep γ X A) P' :=
    ⟨hα, Ω', inferInstance, P', X, A, hP', hX, hA, hXA, rfl⟩
  have hm := WedgeMeasND.aemeasurable_dataFull_of_isQuantumWedge
    (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hαQ) (WedgeInf.wedgeInfiniteTotal hγ hγ2 hαQ)
    hγ hγ2 hrep
  have hae2 : ∀ᵐ a ∂(P.map (pathOf B)), ∀ᵐ c ∂(fieldLawFull H Y P), (a, c) ∈ E := by
    rw [hlaw]
    filter_upwards [hae] with a ha
    exact (ae_map_iff hm (measurable_prodMk_left hE)).2 ha
  have hgm : AEMeasurable (pathOf B) P := QuantumZipper.IsBrownianReal.aemeasurable_pathOf hB
  have hdm : AEMeasurable (fun ω => WedgeMeas.dataFull H (Y ω)) P := hIn.2.1
  have hind' : IndepFun (hgm.mk _) (hdm.mk _) P :=
    (hind.comp measurable_id measurable_dataFull_H).congr hgm.ae_eq_mk hdm.ae_eq_mk
  have h1 : ∀ᵐ ω ∂P, ∀ᵐ ω' ∂P, (hgm.mk _ ω, hdm.mk _ ω') ∈ E := by
    filter_upwards [ae_of_ae_map hgm hae2, hgm.ae_eq_mk] with ω hω hω'
    filter_upwards [ae_of_ae_map hdm hω, hdm.ae_eq_mk] with ω' h2' h3'
    rw [← hω', ← h3']; exact h2'
  have h2'' := CharFunRhs.ae_indep_ae hgm.measurable_mk hdm.measurable_mk hind' hE h1
  have hext := ae_of_ae_map hgm (G1RC.g1PsiExtStmt_holds γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ)
  filter_upwards [h2'', hgm.ae_eq_mk, hdm.ae_eq_mk, hIn.2.2, hB.cont, hext, hIn.1,
    ae_g1zDrvGood hS0 hIn]
    with ω hω e1 e2 hin hc hpe hYω hGω
  rw [← e1, ← e2] at hω
  set a := pathOf B ω with ha
  have hU : UCond (Y ω) (Ψ left a) := (ucond_congr (hfromC _) _).1 (hω left)
  obtain ⟨ψe, -, hψec, hψeH, heq, -⟩ := hpe left
  obtain ⟨F, hF⟩ := hYω.1.1
  have hΨm : Measurable (Ψ left a) := (hΨ.1 left).comp (measurable_const.prodMk measurable_id)
  have hcont := contData_of_ucond hF hΨm hψec hψeH heq hU
  -- the side map is a dilation of the selected map
  obtain ⟨φ, hφ, hΨa⟩ := hΨ.2.2 a hc hin.1 left
  have hUn : IsNormalizedUniformizer (sideDom (sleTrace (γ ^ 2) B ω) left)
      (uniformizer (sideDom (sleTrace (γ ^ 2) B ω) left)) := by
    cases left
    · exact hin.2.2.2
    · exact hin.2.2.1
  obtain ⟨b, hb, hdil⟩ := g1z2_invFunOn_eq_dilate hin.1 left hφ hUn

  have hcont := continuousOn_evalReg_push hF hΨm hψec hψeH heq hU
  have hmapeq : ∀ (d : ℂ) (r : ℝ), 0 < r →
      (foldedCircle d r).map (g1zSideMap left (drive (γ ^ 2) B ω)) =
      (foldedCircle ((b : ℂ) * d) (b * r)).map (Ψ left a) := by
    intro d r hr
    rw [← WedgeTK.fc_map_mul d r hb, Measure.map_map hΨm (measurable_const_mul _)]
    refine Measure.map_congr ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun w hw => ?_)
    have := hdil hw
    simp only [Function.comp_apply]
    rw [hΨa]
    exact this
  have hside : ContinuousOn (fun q : ℂ × ℝ =>
      evalReg (Y ω) ((foldedCircle q.1 q.2).map (g1zSideMap left (drive (γ ^ 2) B ω))))
      (univ ×ˢ Ioi 0) := by
    refine (hcont.comp (f := fun q : ℂ × ℝ => (((b : ℂ) * q.1, b * q.2) : ℂ × ℝ))
      (by fun_prop) fun q hq => ⟨mem_univ _, mul_pos hb hq.2⟩).congr fun q hq => ?_
    simp only [Function.comp_apply]
    rw [hmapeq q.1 q.2 hq.2]
  refine (hside.comp (f := fun p : Fin 4 → ℝ => ((parD p, p 3) : ℂ × ℝ))
    (continuous_parD.prodMk (continuous_apply 3)).continuousOn
    fun p hp => ⟨mem_univ _, hp.2⟩).congr fun p hp => ?_
  simp only [Function.comp_apply]
  rw [smearFam_zero_eq hGω left hp]

end A1RS
end R18
end QuantumZipper
