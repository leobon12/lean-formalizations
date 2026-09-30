import QuantumZipper.Proofs.Thm18.G1Side3Red

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE3 (2): `G1Z2SideAreaStmt` from the selected-map node `G1Z2SideAreaSelStmt`

Measurable good set, law transfer and dilation, as in `Thm18Asm.bdryAll_rep` and
`ae_sideBdryLim_all` (G1Side2Bdry.lean). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus Factorization

/-- The good pairs for the area clause. -/
def G1AreaAll (γ : ℝ) (p : G1PathData) : Prop :=
  Continuous p.1 → IsSimpleChord (pathTrace (γ ^ 2) p.1) →
    ∀ y : FieldSample, WedgeMeas.dataFull H y = p.2 → ∀ left : Bool, ∀ φ : ℂ → ℂ,
      IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2) p.1) left) φ →
      AreaGood γ (coordChange y (invFunOn φ (sideDom (pathTrace (γ ^ 2) p.1) left)) (Qc γ))

theorem areaAll_rep (hN : G1Z2SideAreaSelStmt) :
    G1RepSetting fun γ _ _ P B _ _ P' X A =>
      ∃ E : Set G1PathData, MeasurableSet E ∧ (∀ p ∈ E, G1AreaAll γ p) ∧
        ∀ᵐ a ∂(P.map (pathOf B)), ∀ᵐ ω' ∂P',
          (a, WedgeMeas.dataFull H (wedgeRep γ X A ω')) ∈ E := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hXf hA hXA
  obtain ⟨Ψ, hΨ⟩ := g1PsiSelStmt γ hγ hγ2
  obtain ⟨E', hE'm, hE'g, hE'ae⟩ :=
    g1RegRepRestStmt_holds γ hγ hγ2 P B hB P' X A hXf hA hXA Ψ hΨ
  set R : Bool → Set G1PathData := fun left =>
    {p | IsRegularSample (G1ZA2.xc γ Ψ left p)} ∩
      {p | GoodMeas.AreaCert γ (G1ZA2.xc γ Ψ left p)} ∩ G1ZA2.SetST γ Ψ left with hR
  have hRm : ∀ left, MeasurableSet (R left) := fun left =>
    ((G1Meas.measurableSet_rc2 hΨ left).inter (G1ZA2.measurableSet_areaCert hΨ left)).inter
      (G1ZA2.measurableSet_SetST hΨ left)
  refine ⟨E' ∩ (R true ∩ R false), hE'm.inter ((hRm true).inter (hRm false)), ?_, ?_⟩
  · rintro p ⟨hp', hpt, hpf⟩ hc hs y hy left φ hφ
    have hRl : p ∈ R left := by
      cases left
      · exact hpf
      · exact hpt
    obtain ⟨⟨⟨F, hF⟩, hAC⟩, hST⟩ := hRl
    obtain ⟨μ, hμ⟩ := GoodMeas.hasAreaLimit_of_cert hF hAC
    obtain ⟨hsm, htop⟩ := (G1ZA2.mem_SetST_iff hF hμ).1 hST
    have hgood : AreaGood γ (G1ZA2.xc γ Ψ left p) := ⟨μ, hμ, hsm, htop⟩
    obtain ⟨φ₀, hφ₀, hΨa⟩ := hΨ.2.2 p.1 hc hs left
    have hexact := (hE'g p hp' left).1
    unfold G1ZA2.xc at hgood hF
    rw [hΨa] at hgood hF hexact
    have hD : IsOpen (sideDom (pathTrace (γ ^ 2) p.1) left) := G1.isOpen_component hs left
    obtain ⟨hψd, hψ0, hψm, -⟩ := G1.invFunOn_props hD hφ₀
    have hint := G1.choiceRegular_logDeriv hD hφ₀
    obtain ⟨b, hb, hbeq⟩ := g1z2_invFunOn_eq_dilate hs left hφ₀ hφ
    have hRE := g1z2_regEq_dilate (E1.fromC p.2.1) (Qc γ) hψd hψ0 hψm hb hbeq hint hexact
    have havg : avgReg (rescale (coordChange (E1.fromC p.2.1)
        (invFunOn φ₀ (sideDom (pathTrace (γ ^ 2) p.1) left)) (Qc γ)) (Qc γ) b) =
        avgReg (coordChange (E1.fromC p.2.1)
          (invFunOn φ (sideDom (pathTrace (γ ^ 2) p.1) left)) (Qc γ)) :=
      funext fun k => funext fun z => (hRE k z).symm
    have h1 : p.2.1 = CoordsFull.coordsFull y := by rw [← hy]; rfl
    have hcf : CoordsFull.coordsFull (E1.fromC p.2.1) = CoordsFull.coordsFull y := by
      rw [h1]; exact E1.coordsFull_fromC y
    have havg2 := CoordsFull.avgReg_congr_full hcf
    rw [← G1Z4.coordChange_congr_avg havg2]
    exact areaGood_congr_avg havg (areaGood_rescale hγ ⟨F, hF⟩ hgood hb)
  · filter_upwards [hE'ae, hN γ hγ hγ2 P B hB P' X A hXf hA hXA Ψ hΨ,
      G1RC.g1RegRepRC2Stmt_holds γ hγ hγ2 P B hB P' X A hXf hA hXA Ψ hΨ] with a ha1 hag ha2
    have hmem : ∀ left, ∀ᵐ ω' ∂P', (a, WedgeMeas.dataFull H (wedgeRep γ X A ω')) ∈ R left := by
      intro left
      filter_upwards [hag left, ha2 left] with ω' hg hr
      have e : G1ZA2.xc γ Ψ left (a, WedgeMeas.dataFull H (wedgeRep γ X A ω')) =
          coordChange (wedgeRep γ X A ω') (Ψ left a) (Qc γ) :=
        Factorization.coordChange_congr (CoordsFull.avgReg_congr_full
          (E1.coordsFull_fromC (wedgeRep γ X A ω'))) _ _
      obtain ⟨μ, hμ, hsm, htop⟩ := hg
      obtain ⟨F, hF⟩ := hr
      have hF' : IsRegularWith (G1ZA2.xc γ Ψ left
          (a, WedgeMeas.dataFull H (wedgeRep γ X A ω'))) F := by rw [e]; exact hF
      have hμ' : HasAreaLimit γ (G1ZA2.xc γ Ψ left
          (a, WedgeMeas.dataFull H (wedgeRep γ X A ω'))) μ := by rw [e]; exact hμ
      exact ⟨⟨⟨F, hF'⟩, GoodMeas.areaCert_of_hasAreaLimit hμ'⟩,
        (G1ZA2.mem_SetST_iff hF' hμ').2 ⟨hsm, htop⟩⟩
    filter_upwards [ha1, hmem true, hmem false] with ω' h1 ht hf
    exact ⟨h1, ht, hf⟩

/-- **`G1Z2SideAreaStmt` from the selected-map node.** -/
theorem g1Z2SideAreaStmt_of_sel (hN : G1Z2SideAreaSelStmt) : G1Z2SideAreaStmt := by
  intro γ Ω _ P _ B Y hS hIn left
  obtain ⟨hγ, hγ2, hB, hY, hind⟩ := hS
  obtain ⟨hα, Ω', _, P', X, A, hP', hX, hA, hXA, hlaw⟩ := hY
  obtain ⟨E, hE, hgood, hae⟩ := areaAll_rep hN γ hγ hγ2 P B hB P' X A hX hA hXA
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
  filter_upwards [h2'', hgm.ae_eq_mk, hdm.ae_eq_mk, hIn.2.2, hB.cont] with ω hω e1 e2 hin hc
  rw [← e1, ← e2] at hω
  intro φ hφ
  exact hgood _ hω hc hin.1 (Y ω) rfl left φ hφ

end Thm18Asm
end QuantumZipper
