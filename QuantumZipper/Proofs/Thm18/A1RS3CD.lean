import QuantumZipper.Proofs.Thm18.A1RS3Path

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS3 (6): continuum limits of the Theorem 1.8 field along the pushed side circles

**`ae_contData_sidePush`**: a.s., for both sides and all `d`, `s > 0`, the continuous-radius
pairings of `Y` against `ψ_* fc(d, s)` (`ψ = g1zSideMap left W`) converge (`F1.ContData`). Same
transfer as `ae_continuousOn_smearFam_zero` (A1RS2Y3.lean): the countable Cauchy condition
`G1SSR2.UCond` at the selected side map (`g1SidePushUCRepStmt_holds`, through the law of the
wedge and the independence of the driver), then `contData_of_ucond` and the dilation relating
`g1zSideMap` to the selection. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm Thm18Asm.G1SSR2

/-- **Continuum limits along the pushed side circles.** -/
theorem ae_contData_sidePush (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample)
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) (left : Bool) :
    ∀ᵐ ω ∂P, ∀ (d : ℂ) (s : ℝ), 0 < s →
      F1.ContData (Y ω) ((foldedCircle d s).map (g1zSideMap left (drive (γ ^ 2) B ω))) := by
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
  -- the side map is a dilation of the selected map
  obtain ⟨φ, hφ, hΨa⟩ := hΨ.2.2 a hc hin.1 left
  have hUn : IsNormalizedUniformizer (sideDom (sleTrace (γ ^ 2) B ω) left)
      (uniformizer (sideDom (sleTrace (γ ^ 2) B ω) left)) := by
    cases left
    · exact hin.2.2.2
    · exact hin.2.2.1
  obtain ⟨b, hb, hdil⟩ := g1z2_invFunOn_eq_dilate hin.1 left hφ hUn

  intro d r hr
  have hmapeq : (foldedCircle d r).map (g1zSideMap left (drive (γ ^ 2) B ω)) =
      (foldedCircle ((b : ℂ) * d) (b * r)).map (Ψ left a) := by
    rw [← WedgeTK.fc_map_mul d r hb, Measure.map_map hΨm (measurable_const_mul _)]
    refine Measure.map_congr ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun w hw => ?_)
    have := hdil hw
    simp only [Function.comp_apply]
    rw [hΨa]
    exact this
  rw [hmapeq]
  exact contData_of_ucond hF hΨm hψec hψeH heq hU _ (mul_pos hb hr)

end A1RS
end R18
end QuantumZipper
