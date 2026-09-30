import QuantumZipper.Proofs.Thm18.G3ZqSTop
import QuantumZipper.Proofs.Thm18.G3ZqL11Reg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3ZqS2: the one-point unscaled-wedge regularity `G3ZqL.G3ZqL1RegUStmt`

One-point analog of `G3ZqS.g3ZqSRegUStmt_of_choice` / `g3ZqSChoiceUStmt_holds` (G3ZqSReg3,
G3ZqSTop): the shift clauses (`G3ZqS.ae_regShiftU`) and the area-only choice regularity
(`ae_choiceU_all`, the body of `g3ZqSChoiceUStmt_holds` at every point of both sides) of the
unscaled wedge along the unscaled path, hence `G3ZqRegU` at every side point. With the G3ZqL
reduction this gives `g1WedgePalmLimStmt_of_pathU'`.

Sheffield, arXiv:1012.4797, p. 70. Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqS

open G1Zm G3Zq G3Zr G3Z2b2 G1SSR2

/-- **The area-only choice regularity of the unscaled wedge along the unscaled path, at every
point of both sides, a.s.** -/
theorem ae_choiceU_all {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}
    (hsel : G1PsiSel γ Ψ) {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hXA : IndepFun X (fun ω t => A t ω) P') {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hsc : ∀ᵐ ω ∂P, IsSimpleChord (pathTrace (γ ^ 2) (pathOf B ω))) (L : ℝ) :
    ∀ᵐ ω' ∂P', ∀ᵐ ω ∂P, ∀ (left : Bool) (x : ℝ),
      G1.ChoiceRegularA γ (addConst (translate (wedgeU γ X A ω') (x : ℂ)) (L / γ))
        (g3mapB Ψ left (pathOf B ω) 1 x) := by
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  obtain ⟨c, hc, hc0, hce⟩ := exists_meas_scale hγ hγ2 hX hA hXA
  have hZ2 : G1Z2SideGoodStmt := g1Z2SideGoodStmt_of_area
    (g1Z2SideAreaStmt_of_sel (g1Z2SideAreaSelStmt_of_top G1Top.g1Z2SideTopSelStmt_holds))
  have hS := thm18Setting_rs (P := P) hγ hγ2 hX hA hXA hB hc hc0
  have hIn := thm18Inputs_of_setting hS
  have hW : IsProbabilityMeasure (P.map (pathOf B)) :=
    (Measure.isProbabilityMeasure_map_iff (IsBrownianReal.aemeasurable_pathOf hB)).2
      inferInstance
  have hprod : ∀ left : Bool, ∀ᵐ z ∂(P'.prod (P.map (pathOf B))),
      IsSimpleChord (pathTrace (γ ^ 2) (pathOf (rsBM c) z)) →
      ∀ φ, IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2) (pathOf (rsBM c) z)) left) φ →
        G1.ChoiceRegularCore γ (wedgeRep γ X A z.1)
            (invFunOn φ (sideDom (pathTrace (γ ^ 2) (pathOf (rsBM c) z)) left)) ∧
          G1Z2MeasGood γ left (coordChange (wedgeRep γ X A z.1)
            (invFunOn φ (sideDom (pathTrace (γ ^ 2) (pathOf (rsBM c) z)) left)) (Qc γ)) := by
    intro left
    have hR : G1RegExSide γ (P'.prod (P.map (pathOf B))) (rsBM c) (fun z : Ω' × (ℝ≥0 → ℝ) => wedgeRep γ X A z.1) left := by
      have := g1RegExStmt_of_rest g1RegRepRestStmt_holds γ _ _ _ hS hIn
      cases left
      · exact this.2
      · exact this.1
    filter_upwards [hR, hZ2 γ _ _ _ hS hIn left] with z hRz hZz hsz φ hφ
    obtain ⟨φ₀, hφ₀, hcore₀⟩ := hRz
    exact ⟨G1.choiceRegularCore_invFunOn_of_normalized hsz left hφ₀ hφ hcore₀, hZz φ hφ⟩
  have ht : ∀ left : Bool, ∀ᵐ ω' ∂P', ∀ᵐ ω ∂P,
      IsSimpleChord (pathTrace (γ ^ 2) (scalePath (c ω') (pathOf B ω))) →
      ∀ φ, IsNormalizedUniformizer
          (sideDom (pathTrace (γ ^ 2) (scalePath (c ω') (pathOf B ω))) left) φ →
        G1.ChoiceRegularCore γ (wedgeRep γ X A ω')
            (invFunOn φ (sideDom (pathTrace (γ ^ 2) (scalePath (c ω') (pathOf B ω))) left)) ∧
          G1Z2MeasGood γ left (coordChange (wedgeRep γ X A ω')
            (invFunOn φ (sideDom (pathTrace (γ ^ 2) (scalePath (c ω') (pathOf B ω))) left))
            (Qc γ)) :=
    fun left => ae_ae_scaled_of_prod hB (p := fun ω' a =>
      IsSimpleChord (pathTrace (γ ^ 2) a) →
      ∀ φ, IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2) a) left) φ →
        G1.ChoiceRegularCore γ (wedgeRep γ X A ω') (invFunOn φ (sideDom (pathTrace (γ ^ 2) a) left)) ∧
          G1Z2MeasGood γ left (coordChange (wedgeRep γ X A ω')
            (invFunOn φ (sideDom (pathTrace (γ ^ 2) a) left)) (Qc γ))) (hprod left)
  filter_upwards [ht true, ht false, hce,
    LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hαQ Ω' _ P' X A inferInstance hX hA hXA,
    ae_ucond_scaled hγ hγ2 hsel hX hA hXA hB hc0]
    with ω' h1 h2 he hg hu
  have hb : 0 < scaleParam γ (wedgeU γ X A ω') := he ▸ hc0 ω'
  filter_upwards [h1, h2, hu, ae_psiExt_scaled hγ hγ2 hsel hX hA hXA hB hb,
    ae_goodPathF hγ hγ2 hB hsc] with ω k1 k2 hu' hpe hgood
  intro left x
  obtain ⟨hac, hs', hWd, hW0, hex⟩ := hgood
  set b := scaleParam γ (wedgeU γ X A ω') with hbdef
  have hsb : IsSimpleChord (pathTrace (γ ^ 2) (scalePath b (pathOf B ω))) :=
    isSimpleChord_scalePath hb _ hWd hW0 hex hs'
  rw [he] at k1 k2
  have hu2 : UCond (canonical γ (wedgeU γ X A ω')) (Ψ left (scalePath b (pathOf B ω))) := by
    have := hu' left; rw [he] at this; exact this
  have hcont := contData_unscaled_pt hsel hg hb hac hs' hWd hW0 hex left (hpe left) hu2
  cases left
  · exact choiceRegularA_unscaled_pt hsel hg hb hac hs' hWd hW0 hex false (k2 hsb) hcont L x
  · exact choiceRegularA_unscaled_pt hsel hg hb hac hs' hWd hW0 hex true (k1 hsb) hcont L x

/-- **`G3ZqL1RegUStmt` holds.** -/
theorem g3ZqL1RegUStmt_holds : G3ZqL.G3ZqL1RegUStmt := by
  intro γ hγ hγ2 Ψ hsel Ω' _ P' _ X A hX hA hXA Ω _ P _ B hB hsc left U L
  filter_upwards [ae_regShiftU (Ψ := Ψ) hγ hγ2 hsel hX hA hXA hB hsc,
    ae_choiceU_all hγ hγ2 hsel hX hA hXA hB hsc L] with ω' h1 h2
  filter_upwards [h1, h2] with ω a1 a2
  exact ae_of_all _ fun x _ => ⟨(a1 left x).1, (a1 left x).2, a2 left x⟩

end G3ZqS
end Thm18Asm
end QuantumZipper
