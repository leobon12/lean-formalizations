import QuantumZipper.Proofs.Thm18.G1SSR2Det
import QuantumZipper.Proofs.Thm18.Thm18HeadlineV3
import QuantumZipper.Proofs.Thm18.G1PkgLeft
import QuantumZipper.Proofs.Thm18.G1SideWireA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1SSR2 (2): `G1SidePushContStmt` from the countable condition at the explicit representative

Theorem 1.8, G1 zoom. The node `G1SidePushContStmt` (G1SSRMain.lean) is reduced to the analytic
statement `G1SidePushUCRepStmt`: for a.e. Brownian path `a` and the selected side map `Ψ left a`
(a map independent of the field), the explicit wedge representative satisfies the countable
Cauchy condition `G1SSR2.UCond` a.s. (Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1
at a fixed map; Sheffield arXiv:1012.4797 (1.3)).

* `measurable_ucond`: the condition is a measurable property of (path, wedge data)
  (`IndepParams.measurable_evalReg_fc₂`, the joint measurability of the selection, countable
  quantifiers);
* the representative → `(Y, B)` transfer by the law of the data and independence, verbatim the
  pattern of `g1SideTransportId_of_path_sel` (G1SideWireA.lean);
* per sample: `contData_of_ucond` (G1SSR2Det.lean) with the continuous extension of the selected
  map (`G1RC.g1PsiExtStmt_holds`), and the side map `g1zSideMap` is a dilation of the selected
  map (`g1z2_invFunOn_eq_dilate`), which maps folded circles to folded circles.
Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open G1SSR2

/-- **Node: the countable Cauchy condition at the explicit representative**, for a.e. path. -/
def G1SidePushUCRepStmt : Prop :=
  G1RepSetting fun γ _ _ P B _ _ P' X A => ∀ Ψ, G1PsiSel γ Ψ →
    ∀ᵐ a ∂(P.map (pathOf B)), ∀ left : Bool, ∀ᵐ ω' ∂P',
      UCond (wedgeRep γ X A ω') (Ψ left a)

namespace G1SSR2

theorem ucond_congr {x x' : FieldSample} (h : avgReg x = avgReg x') (ψ : ℂ → ℂ) :
    UCond x ψ ↔ UCond x' ψ := by
  unfold UCond gPush
  rw [Factorization.evalReg_congr h]

theorem measurable_gPush {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ)
    (left : Bool) (d : ℂ) (r σ : ℝ) :
    Measurable fun p : G1PathData => gPush (E1.fromC p.2.1) (Ψ left p.1) d r σ := by
  unfold gPush
  have hA : Measurable fun q : G1PathData × ℂ => E1.fromC q.1.2.1 :=
    G1Meas.measurable_fromC'.comp (measurable_fst.snd.fst)
  have hB : Measurable fun q : G1PathData × ℂ => Ψ left q.1.1 q.2 :=
    (hΨ.1 left).comp (f := fun q : G1PathData × ℂ => ((q.1.1, q.2) : (ℝ≥0 → ℝ) × ℂ))
      (measurable_fst.fst.prodMk measurable_snd)
  have h1 : Measurable fun q : G1PathData × ℂ =>
      ((E1.fromC q.1.2.1, (Ψ left q.1.1 q.2, σ)) : FieldSample × (ℂ × ℝ)) :=
    hA.prodMk (hB.prodMk measurable_const)
  have hf : Measurable fun q : G1PathData × ℂ =>
      evalReg (E1.fromC q.1.2.1) (foldedCircle (Ψ left q.1.1 q.2) σ) :=
    Measurable.comp (g := fun q : FieldSample × (ℂ × ℝ) => evalReg q.1 (foldedCircle q.2.1 q.2.2))
      (f := fun q : G1PathData × ℂ =>
        ((E1.fromC q.1.2.1, (Ψ left q.1.1 q.2, σ)) : FieldSample × (ℂ × ℝ)))
      IndepParams.measurable_evalReg_fc₂ h1
  exact (hf.stronglyMeasurable.integral_prod_right' (ν := foldedCircle d r)).measurable

theorem measurable_ucond {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ)
    (left : Bool) : Measurable fun p : G1PathData => UCond (E1.fromC p.2.1) (Ψ left p.1) := by
  unfold UCond
  refine Measurable.forall fun N => Measurable.forall fun ε => measurable_const.imp ?_
  refine Measurable.exists fun δ => measurable_const.and ?_
  refine Measurable.forall fun a => Measurable.forall fun b => Measurable.forall fun r =>
    Measurable.forall fun σ => Measurable.forall fun σ' => ?_
  refine measurable_const.imp (measurable_const.imp (measurable_const.imp (measurable_const.imp
    (measurable_const.imp (measurable_const.imp (measurable_const.imp
    (measurable_const.imp ?_)))))))
  have hg : Measurable fun p : G1PathData =>
      |gPush (E1.fromC p.2.1) (Ψ left p.1) ⟨(a : ℝ), (b : ℝ)⟩ r σ -
        gPush (E1.fromC p.2.1) (Ψ left p.1) ⟨(a : ℝ), (b : ℝ)⟩ r σ'| :=
    continuous_abs.measurable.comp
      ((measurable_gPush hΨ left _ _ _).sub (measurable_gPush hΨ left _ _ _))
  exact measurableSet_setOfPred.1 (measurableSet_le hg measurable_const)

end G1SSR2

/-- **`G1SidePushContStmt` from the countable condition at the representative.** -/
theorem g1SidePushContStmt_of_rep (hRep : G1SidePushUCRepStmt) : G1SidePushContStmt := by
  intro γ Ω _ P _ B Y hS hIn left
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
    filter_upwards [hRep γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ] with a ha
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
  filter_upwards [h2'', hgm.ae_eq_mk, hdm.ae_eq_mk, hIn.2.2, hB.cont, hext, hIn.1]
    with ω hω e1 e2 hin hc hpe hYω
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
  exact hcont _ (mul_pos hb hr)

end Thm18Asm
end QuantumZipper
