import QuantumZipper.Proofs.Thm18.G1Z5Id
import QuantumZipper.Proofs.Thm18.G1ZA1cMain
import QuantumZipper.Proofs.Thm18.G1SideSelDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE wiring (D83), part A: the B0 transport chain from `G1Z4SideLimSelStmt`

Copies (suffix `_sel`) of `g1z5_ae_mem_repGood` (G1Z5Main.lean), `g1Z4SideLimStmt'_of_path`,
`g1z5_bdryRepId`, `g1SideTransportId_of_path` (G1Z5Id.lean) and `G1ZA1c.g1zA1c_ae_mem`
(G1ZA1cMain.lean), with the side-limit node at the selected side maps (`G1Z4SideLimSelStmt`,
decision D83) in place of `G1Z4SideLimPathStmt`. The only changed proof is
`g1z5_ae_mem_repGood_sel`: the reflection data of the selected maps are read a.e. path from
`G1Z2.sideReflChordStmt_holds` and fed to the node. Wiring only.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

open GoodSample GoodMeas

/-- Almost sure membership in the good set, from the side-limit node at the selected maps
(copy of `g1z5_ae_mem_repGood` with `G1Z4SideLimSelStmt`; D83). -/
theorem g1z5_ae_mem_repGood_sel (hN : G1Z4SideLimSelStmt) (h2 : G1RegRepRC2Stmt) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {Ω' : Type}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : Ω' → FieldSample}
    {A : ℝ → Ω' → ℝ} (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hXA : IndepFun X (fun ω t => A t ω) P') {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}
    (hΨ : G1PsiSel γ Ψ) :
    ∀ᵐ a ∂(P.map (pathOf B)), ∀ᵐ ω' ∂P', (a, WedgeMeas.dataFull H (wedgeRep γ X A ω')) ∈
      {p : G1PathData | G1Z5.RepGood γ true (Ψ true p.1) p.2.1} ∩
        {p | G1Z5.RepGood γ false (Ψ false p.1) p.2.1} := by
  have hrep : IsQuantumWedge γ (γ - 2 / γ) (wedgeRep γ X A) P' :=
    ⟨alpha_lt_Qc hγ hγ2, Ω', inferInstance, P', X, A, inferInstance, hX, hA, hXA, rfl⟩
  have hcert := ae_certF_of_isQuantumWedge hγ hγ2 hrep
  -- reflection data of the selected maps, a.e. path
  have hRefl := G1RC.ae_map_pathOf_of_chord G1RC.g1RegPathChordStmt hγ hγ2 hB hΨ
    (fun ms => ∀ left : Bool, ∃ Φ : ℝ ≃o ℝ, SideReflGood left (ms left) Φ) (by
      intro a hc hs left
      obtain ⟨φ₀, hφ₀, hΨa⟩ := hΨ.2.2 a hc hs left
      obtain ⟨Φ, hR⟩ := G1Z2.sideReflChordStmt_holds _ hs left φ₀ hφ₀
      refine ⟨Φ, ?_⟩
      simp only
      rw [hΨa]
      exact hR)
  have hQ : ∀ᵐ a ∂(P.map (pathOf B)), ∀ left : Bool, ∀ᵐ ω' ∂P',
      G1Z5.SideCert γ left (coordChange (E1.fromC (CoordsFull.coordsFull (wedgeRep γ X A ω')))
        (Ψ left a) (Qc γ)) ∧
      (∀ N n : ℕ, G1Z5.IdT γ left (Ψ left a) (CoordsFull.coordsFull (wedgeRep γ X A ω'))
        (G1Z5.glue left (BdryVague.testFam N n))) ∧
      ∀ N : ℕ, G1Z5.IdT γ left (Ψ left a) (CoordsFull.coordsFull (wedgeRep γ X A ω'))
        (G1Z5.glue left (BdryVague.bump N)) := by
    filter_upwards [hN γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ, hRefl] with a hSa hRa left
    obtain ⟨Φ, hR⟩ := hRa left
    filter_upwards [hSa left Φ hR, hcert] with ω' hν hce
    have havg := CoordsFull.avgReg_congr_full (E1.coordsFull_fromC (wedgeRep γ X A ω'))
    have hzeq := G1Z4.coordChange_congr_avg havg (Ψ left a) (Qc γ)
    have hqeq : qBoundaryMeasure γ (E1.fromC (CoordsFull.coordsFull (wedgeRep γ X A ω'))) =
        qBoundaryMeasure γ (wedgeRep γ X A ω') := G1Z4.qBoundaryMeasure_congr_avg havg
    have hb : E1.M4.BCert γ (E1.fromC (CoordsFull.coordsFull (wedgeRep γ X A ω'))) :=
      (G1Z5.bCert_congr havg).2 hce.1
    have hy := E1.M4.isVagueLimitR_qBoundaryMeasure (E1.M4.exists_isVagueLimitR_of_bCert hb)
    have key : ∀ G : ℝ → ℝ, Continuous G → HasCompactSupport G →
        G1Z5.IdT γ left (Ψ left a) (CoordsFull.coordsFull (wedgeRep γ X A ω'))
          (G1Z5.glue left G) := by
      intro G hG hGc
      unfold G1Z5.IdT
      rw [hzeq, (hy.2 _ (G1Z5.continuous_glue left hG hGc)
        (G1Z5.hasCompactSupport_glue left hG hGc)).limUnder_eq, hqeq]
      simp_rw [← G1Z5.glue_bm hR]
      have ht := G1Z5.tendsto_glue_comp hν hR.1 hG hGc
      rwa [G1Z5.integral_glue_pullback _ Φ hG hGc] at ht
    refine ⟨?_, fun N n => key _ (BdryVague.continuous_testFam N n)
      (BdryVague.hasCompactSupport_testFam N n), fun N => key _ (BdryVague.continuous_bump N)
      (BdryVague.hasCompactSupport_bump N)⟩
    rw [hzeq]
    exact G1Z5.sideCert_of_lim hν
  filter_upwards [hQ, h2 γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ] with a hQa hRa
  filter_upwards [hQa true, hQa false, hRa true, hRa false, hcert] with ω' hqt hqf hrt hrf hce
  have havg := CoordsFull.avgReg_congr_full (E1.coordsFull_fromC (wedgeRep γ X A ω'))
  have hb : E1.M4.BCert γ (E1.fromC (CoordsFull.coordsFull (wedgeRep γ X A ω'))) :=
    (G1Z5.bCert_congr havg).2 hce.1
  have hreg : ∀ left, IsRegularSample (coordChange (wedgeRep γ X A ω') (Ψ left a) (Qc γ)) →
      IsRegularSample (coordChange (E1.fromC (CoordsFull.coordsFull (wedgeRep γ X A ω')))
        (Ψ left a) (Qc γ)) := fun left h => by
    rwa [G1Z4.coordChange_congr_avg havg]
  exact ⟨⟨hreg true hrt, hqt.1, hb, hqt.2.1, hqt.2.2⟩,
    ⟨hreg false hrf, hqf.1, hb, hqf.2.1, hqf.2.2⟩⟩

theorem g1Z4SideLimStmt'_of_path_sel (hN : G1Z4SideLimSelStmt) (h2 : G1RegRepRC2Stmt) :
    G1Z4SideLimStmt' := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hX hA hXA Ψ hΨ
  refine ⟨{p | G1Z5.RepGood γ true (Ψ true p.1) p.2.1} ∩
      {p | G1Z5.RepGood γ false (Ψ false p.1) p.2.1},
    (G1Z5.measurableSet_repGood hΨ true).inter (G1Z5.measurableSet_repGood hΨ false), ?_, ?_⟩
  · rintro p ⟨ht, hf⟩ hc hs left
    cases left
    · exact G1Z5.sideLim_of_repGood' hΨ hc hs hf
    · exact G1Z5.sideLim_of_repGood' hΨ hc hs ht
  · exact g1z5_ae_mem_repGood_sel hN h2 hγ hγ2 hB hX hA hXA hΨ

/-- **Representative form with identified transport map.** -/
theorem g1z5_bdryRepId_sel (hN : G1Z4SideLimSelStmt) (h2 : G1RegRepRC2Stmt)
    (h3 : G1RegRepRestStmt) :
    G1RepSetting fun γ _ _ P B _ _ P' X A =>
      ∃ E : Set G1PathData, MeasurableSet E ∧ (∀ p ∈ E, G1BdryGood' γ p) ∧
        ∀ᵐ a ∂(P.map (pathOf B)), ∀ᵐ ω' ∂P',
          (a, WedgeMeas.dataFull H (wedgeRep γ X A ω')) ∈ E := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hXf hA hXA
  obtain ⟨Ψ, hΨ⟩ := g1PsiSelStmt γ hγ hγ2
  obtain ⟨E', hE'm, hE'g, hE'ae⟩ := h3 γ hγ hγ2 P B hB P' X A hXf hA hXA Ψ hΨ
  obtain ⟨E₁, hE₁m, hE₁g, hE₁ae⟩ :=
    g1Z4SideLimStmt'_of_path_sel hN h2 γ hγ hγ2 P B hB P' X A hXf hA hXA Ψ hΨ
  set R : Bool → Set G1PathData := fun left =>
    {p | IsRegularSample (coordChange (E1.fromC p.2.1) (Ψ left p.1) (Qc γ))} with hR
  refine ⟨E' ∩ E₁ ∩ (R true ∩ R false), (hE'm.inter hE₁m).inter
    ((G1Meas.measurableSet_rc2 hΨ true).inter (G1Meas.measurableSet_rc2 hΨ false)), ?_, ?_⟩
  · rintro p ⟨⟨hp', hp₁⟩, hpt, hpf⟩ hc hs y hy left
    have hreg : IsRegularSample (coordChange (E1.fromC p.2.1) (Ψ left p.1) (Qc γ)) := by
      cases left
      · exact hpf
      · exact hpt
    obtain ⟨F, hF⟩ := hreg
    obtain ⟨φ₀, hφ₀, hΨa⟩ := hΨ.2.2 p.1 hc hs left
    obtain ⟨Φ₀, hR₀, hν⟩ := hE₁g p hp₁ hc hs left
    have hexact := (hE'g p hp' left).1
    rw [hΨa] at hF hν hexact hR₀
    have h1 : p.2.1 = CoordsFull.coordsFull y := by rw [← hy]; rfl
    have hcf : CoordsFull.coordsFull (E1.fromC p.2.1) = CoordsFull.coordsFull y := by
      rw [h1]; exact E1.coordsFull_fromC y
    have havg := CoordsFull.avgReg_congr_full hcf
    obtain ⟨Φ, hRΦ, hΦ⟩ := G1Z5.good_of_selected' hγ hs hφ₀ hF hexact hR₀ hν
    refine ⟨Φ, hRΦ, ?_⟩
    rw [← G1Z4.qBoundaryMeasure_congr_avg havg]
    show g1SideNu γ left (coordChange y _ (Qc γ)) = _
    rw [← G1Z4.coordChange_congr_avg havg]
    exact hΦ
  · filter_upwards [hE'ae, hE₁ae, h2 γ hγ hγ2 P B hB P' X A hXf hA hXA Ψ hΨ]
      with a ha1 ha1' ha2
    filter_upwards [ha1, ha1', ha2 true, ha2 false] with ω' h1 h1' ht hf
    have hc : ∀ left, IsRegularSample (coordChange (wedgeRep γ X A ω') (Ψ left a) (Qc γ)) →
        (a, WedgeMeas.dataFull H (wedgeRep γ X A ω')) ∈ R left := fun left h => by
      show IsRegularSample (coordChange (E1.fromC (CoordsFull.coordsFull (wedgeRep γ X A ω')))
        (Ψ left a) (Qc γ))
      rwa [Factorization.coordChange_congr (CoordsFull.avgReg_congr_full
        (E1.coordsFull_fromC (wedgeRep γ X A ω')))]
    exact ⟨⟨h1, h1'⟩, hc true ht, hc false hf⟩

theorem g1SideTransportId_of_path_sel (hN : G1Z4SideLimSelStmt) (h2 : G1RegRepRC2Stmt)
    (h3 : G1RegRepRestStmt) :
    ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
      Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool,
      ∀ᵐ ω ∂P, ∃ Φ : ℝ ≃o ℝ, SideReflGood left (g1zSideMap left (drive (γ ^ 2) B ω)) Φ ∧
        g1SideNu γ left (g1SideField γ B Y left ω) =
          ((qBoundaryMeasure γ (Y ω)).restrict (g1SideHalf left)).map Φ.symm := by
  intro γ Ω _ P _ B Y hS hIn left
  obtain ⟨hγ, hγ2, hB, hY, hind⟩ := hS
  obtain ⟨hα, Ω', _, P', X, A, hP', hX, hA, hXA, hlaw⟩ := hY
  obtain ⟨E, hE, hgood, hae⟩ := g1z5_bdryRepId_sel hN h2 h3 γ hγ hγ2 P B hB P' X A hX hA hXA
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
  exact hgood _ hω hc hin.1 (Y ω) rfl left

namespace G1ZA1c

theorem g1zA1c_ae_mem_sel (hN : G1Z4SideLimSelStmt) (h2 : G1RegRepRC2Stmt) (h3 : G1RegRepRestStmt)
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample} (hS : Thm18Setting γ P B Y)
    (hIn : Thm18Inputs γ P B Y) :
    ∃ E : Set G1PathData, MeasurableSet E ∧ (∀ p ∈ E, G1BdryGood' γ p) ∧
      ∀ᵐ ω ∂P, (pathOf B ω, WedgeMeas.dataFull H (Y ω)) ∈ E := by
  obtain ⟨hγ, hγ2, hB, hY, hind⟩ := hS
  obtain ⟨hα, Ω', _, P', X, A, hP', hX, hA, hXA, hlaw⟩ := hY
  obtain ⟨E, hE, hgood, hae⟩ := g1z5_bdryRepId_sel hN h2 h3 γ hγ hγ2 P B hB P' X A hX hA hXA
  refine ⟨E, hE, hgood, ?_⟩
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
  filter_upwards [h2'', hgm.ae_eq_mk, hdm.ae_eq_mk] with ω hω e1 e2
  rw [← e1, ← e2] at hω
  exact hω

end G1ZA1c

end Thm18Asm
end QuantumZipper
