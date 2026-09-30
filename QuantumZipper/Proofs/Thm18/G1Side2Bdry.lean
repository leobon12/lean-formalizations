import QuantumZipper.Proofs.Thm18.G1SideMain
import QuantumZipper.Proofs.Thm18.G1SideWireA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE2 (1): the boundary clause of `G1Z2SideGoodStmt`, for every normalized uniformizer

`ae_sideBdryLim_all`: in the Theorem 1.8 setting, almost surely, for EVERY normalized
uniformizer `φ` of the side domain, the pulled-back wedge field `coordChange (Y ω) (φ⁻¹) Q` has a
side boundary limit along all radii (`G1Z2SideBdryLim`).

Route: the proved side-limit node at the selected maps (`g1Z4SideLimSelStmt_holds`, D83) in its
measurable-good-set form (`g1Z4SideLimStmt'_of_path_sel`), the law transfer from the
representative to `Y` and the independence of the path (as in `g1SideTransportId_of_path`,
G1Z5Id.lean), and, per sample, the passage from the selected map to any normalized uniformizer,
which is a dilation of it (U6, `g1z2_invFunOn_eq_dilate`): the pulled-back fields differ by a
rescaling (`g1z2_regEq_dilate`, using RC3 of `G1RegRepRestStmt`), and a side limit along all
radii survives rescaling (`sideBdryLim_rescale`; offsets become continuous radii through
`GoodTransforms.tendsto_idx`). Coordinate-change rule (1.3) of Sheffield, arXiv:1012.4797, for
dilations. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus Factorization

/-- The side limit along all radii only reads the regularized averages. -/
theorem sideBdryLim_congr_avg {γ : ℝ} {left : Bool} {x x' : FieldSample}
    (h : avgReg x = avgReg x') {ν : Measure ℝ} (hν : G1Z2SideBdryLim γ left x ν) :
    G1Z2SideBdryLim γ left x' ν := by
  have hb : ∀ r, bdryR γ x r = bdryR γ x' r := fun r => by
    unfold bdryR bdryDens
    simp_rw [Factorization.evalReg_congr h]
  refine ⟨hν.1, hν.2.1, fun f hf hfc hfS => ?_⟩
  simp_rw [← hb]
  exact hν.2.2 f hf hfc hfS

/-- **A side limit along all radii survives rescaling.** -/
theorem sideBdryLim_rescale {γ : ℝ} (hγ : 0 < γ) {left : Bool} {x : FieldSample}
    {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) {ν : Measure ℝ} (hν : G1Z2SideBdryLim γ left x ν)
    {b : ℝ} (hb : 0 < b) :
    G1Z2SideBdryLim γ left (rescale x (Qc γ) b) (ν.map fun u => u / b) := by
  have hv := g1z2_isVagueLimitOnR_rescale hγ hF hν hb
  refine ⟨hv.1, hv.2.1, fun f hf hfc hfS => ?_⟩
  have hmeas : Measurable fun u : ℝ => u / b := measurable_id.div_const b
  set S := g1SideHalf left
  have hg : Continuous fun u : ℝ => f (u / b) := hf.comp (continuous_id.div_const b)
  set h : ℝ ≃ₜ ℝ := Homeomorph.mulRight₀ b⁻¹ (inv_ne_zero hb.ne') with hh
  have hfun : (fun u : ℝ => u / b) = h := funext fun u => by simp [hh, div_eq_mul_inv]
  have hgc : HasCompactSupport fun u : ℝ => f (u / b) := by
    have := hfc.comp_homeomorph h
    rwa [← hfun] at this
  have hgS : tsupport (fun u : ℝ => f (u / b)) ⊆ S := fun u hu =>
    (g1z2_mem_sideHalf_div hb left u).1
      (hfS (g1z2_tsupport_comp (f := f) (continuous_id.div_const b) hu))
  -- the limit along continuous radii
  have hlim : Tendsto (fun r => ∫ t, f (t / b) ∂bdryR γ x r) (𝓝[>] 0)
      (𝓝 (∫ t, f (t / b) ∂ν)) := by
    refine ((hν.2.2 _ hg hgc hgS).comp GoodTransforms.tendsto_idx).congr' ?_
    filter_upwards [(Ioo_mem_nhdsGT one_pos : Ioo (0 : ℝ) 1 ∈ 𝓝[>] 0)] with r hr
    simp only [Function.comp, (GoodTransforms.idx_spec ⟨hr.1, hr.2.le⟩).1]
  have hrad : Tendsto (fun i => b * goodRad i) goodFilter (𝓝[>] 0) := by
    have hg0 : Tendsto goodRad goodFilter (𝓝 0) := by
      unfold goodFilter goodRad
      have h1 : Tendsto (fun i : ℕ × ℝ => radius i.1) (atTop ×ˢ 𝓟 (Icc 1 2)) (𝓝 0) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp tendsto_fst
      have h2 : ∀ i ∈ (univ : Set ℕ) ×ˢ Icc (1 : ℝ) 2, |i.2 * radius i.1| ≤ 2 * radius i.1 :=
        fun i hi => by
          rw [abs_of_nonneg (mul_nonneg (by linarith [hi.2.1]) (radius_pos _).le)]
          exact mul_le_mul_of_nonneg_right hi.2.2 (radius_pos _).le
      refine squeeze_zero_norm' ?_ (by simpa using h1.const_mul 2)
      filter_upwards [prod_mem_prod univ_mem (mem_principal_self _)] with i hi
      rw [Real.norm_eq_abs]; exact h2 i hi
    refine tendsto_nhdsWithin_iff.2 ⟨by simpa using hg0.const_mul b, ?_⟩
    filter_upwards [prod_mem_prod univ_mem (mem_principal_self _)] with i hi
    exact mul_pos hb (mul_pos (by linarith [hi.2.1]) (radius_pos _))
  rw [integral_map hmeas.aemeasurable hf.aestronglyMeasurable]
  refine (hlim.comp hrad).congr' ?_
  filter_upwards [prod_mem_prod univ_mem (mem_principal_self _)] with i hi
  simp only [Function.comp]
  exact (GoodTransforms.integral_bdryR_rescale hF hγ hb
    (mul_pos (by linarith [(show i.2 ∈ Icc (1 : ℝ) 2 from hi.2).1]) (radius_pos _)) f).symm

/-- The good pairs: every normalized uniformizer has a side limit along all radii. -/
def G1BdryAll (γ : ℝ) (p : G1PathData) : Prop :=
  Continuous p.1 → IsSimpleChord (pathTrace (γ ^ 2) p.1) →
    ∀ y : FieldSample, WedgeMeas.dataFull H y = p.2 → ∀ left : Bool, ∀ φ : ℂ → ℂ,
      IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2) p.1) left) φ →
      ∃ ν, G1Z2SideBdryLim γ left
        (coordChange y (invFunOn φ (sideDom (pathTrace (γ ^ 2) p.1) left)) (Qc γ)) ν

/-- **Representative form** (measurable good set of full product measure). -/
theorem bdryAll_rep :
    G1RepSetting fun γ _ _ P B _ _ P' X A =>
      ∃ E : Set G1PathData, MeasurableSet E ∧ (∀ p ∈ E, G1BdryAll γ p) ∧
        ∀ᵐ a ∂(P.map (pathOf B)), ∀ᵐ ω' ∂P',
          (a, WedgeMeas.dataFull H (wedgeRep γ X A ω')) ∈ E := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hXf hA hXA
  obtain ⟨Ψ, hΨ⟩ := g1PsiSelStmt γ hγ hγ2
  obtain ⟨E', hE'm, hE'g, hE'ae⟩ :=
    g1RegRepRestStmt_holds γ hγ hγ2 P B hB P' X A hXf hA hXA Ψ hΨ
  obtain ⟨E₁, hE₁m, hE₁g, hE₁ae⟩ :=
    g1Z4SideLimStmt'_of_path_sel g1Z4SideLimSelStmt_holds G1RC.g1RegRepRC2Stmt_holds
      γ hγ hγ2 P B hB P' X A hXf hA hXA Ψ hΨ
  set R : Bool → Set G1PathData := fun left =>
    {p | IsRegularSample (coordChange (E1.fromC p.2.1) (Ψ left p.1) (Qc γ))} with hR
  refine ⟨E' ∩ E₁ ∩ (R true ∩ R false), (hE'm.inter hE₁m).inter
    ((G1Meas.measurableSet_rc2 hΨ true).inter (G1Meas.measurableSet_rc2 hΨ false)), ?_, ?_⟩
  · rintro p ⟨⟨hp', hp₁⟩, hpt, hpf⟩ hc hs y hy left φ hφ
    have hreg : IsRegularSample (coordChange (E1.fromC p.2.1) (Ψ left p.1) (Qc γ)) := by
      cases left
      · exact hpf
      · exact hpt
    obtain ⟨F, hF⟩ := hreg
    obtain ⟨φ₀, hφ₀, hΨa⟩ := hΨ.2.2 p.1 hc hs left
    obtain ⟨Φ₀, -, hν⟩ := hE₁g p hp₁ hc hs left
    have hexact := (hE'g p hp' left).1
    rw [hΨa] at hF hν hexact
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
    refine ⟨((((qBoundaryMeasure γ (E1.fromC p.2.1)).restrict (g1SideHalf left)).map
      Φ₀.symm).map fun u => u / b), ?_⟩
    rw [← G1Z4.coordChange_congr_avg havg2]
    exact sideBdryLim_congr_avg havg (sideBdryLim_rescale hγ hF hν hb)
  · filter_upwards [hE'ae, hE₁ae, G1RC.g1RegRepRC2Stmt_holds γ hγ hγ2 P B hB P' X A hXf hA hXA
      Ψ hΨ] with a ha1 ha1' ha2
    filter_upwards [ha1, ha1', ha2 true, ha2 false] with ω' h1 h1' ht hf
    have hc : ∀ left, IsRegularSample (coordChange (wedgeRep γ X A ω') (Ψ left a) (Qc γ)) →
        (a, WedgeMeas.dataFull H (wedgeRep γ X A ω')) ∈ R left := fun left h => by
      show IsRegularSample (coordChange (E1.fromC (CoordsFull.coordsFull (wedgeRep γ X A ω')))
        (Ψ left a) (Qc γ))
      rwa [Factorization.coordChange_congr (CoordsFull.avgReg_congr_full
        (E1.coordsFull_fromC (wedgeRep γ X A ω')))]
    exact ⟨⟨h1, h1'⟩, hc true ht, hc false hf⟩

/-- **The boundary clause of `G1Z2SideGoodStmt`.** -/
theorem ae_sideBdryLim_all :
    ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
      Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool,
      ∀ᵐ ω ∂P, ∀ φ : ℂ → ℂ, IsNormalizedUniformizer (sideDom (sleTrace (γ ^ 2) B ω) left) φ →
        ∃ ν, G1Z2SideBdryLim γ left
          (coordChange (Y ω) (invFunOn φ (sideDom (sleTrace (γ ^ 2) B ω) left)) (Qc γ)) ν := by
  intro γ Ω _ P _ B Y hS hIn left
  obtain ⟨hγ, hγ2, hB, hY, hind⟩ := hS
  obtain ⟨hα, Ω', _, P', X, A, hP', hX, hA, hXA, hlaw⟩ := hY
  obtain ⟨E, hE, hgood, hae⟩ := bdryAll_rep γ hγ hγ2 P B hB P' X A hX hA hXA
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
