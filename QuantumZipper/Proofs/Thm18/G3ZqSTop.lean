import QuantumZipper.Proofs.Thm18.G3ZqSReg4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3ZqS (7): `G3ZqResclRegStmt` holds

The choice-regularity node `G3ZqSChoiceUStmt` (G3ZqSReg3) is proved from the setting-level core
(`G1RegExSide`, via `g1RegExStmt_of_rest g1RegRepRestStmt_holds`, transported to every normalized
uniformizer by `choiceRegularCore_invFunOn_of_normalized`) and side area (`G1Z2SideGoodStmt`) of
the canonical wedge along the randomly scaled path (`thm18Setting_rs`, transferred to the coupled
scaled path by `ae_ae_scaled_of_prod`), the pointwise transfer `choiceRegularA_unscaled_pt`
(G3ZqSReg4), and the scaling of the length partner (`g3zPartner_rescale`).

Headlines: **`g3ZqSChoiceUStmt_holds`**, **`g3ZqResclRegStmt_holds : G3Zq.G3ZqResclRegStmt`**.
Sheffield, arXiv:1012.4797, p. 70 (independent curve, SLE scale invariance). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqS

open G1Zm G3Zq G3Zr G3Z2b2 G1SSR2

/-- **`G3ZqSChoiceUStmt` holds.** -/
theorem g3ZqSChoiceUStmt_holds : G3ZqSChoiceUStmt := by
  intro γ hγ hγ2 Ψ hsel Ω' _ P' _ X A hX hA hXA Ω _ P _ B hB hsc U L
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
    ae_ucond_scaled hγ hγ2 hsel hX hA hXA hB hc0, ae_partner_pos_rep hγ hγ2 hX hA hXA]
    with ω' h1 h2 he hg hu hpp
  have hb : 0 < scaleParam γ (wedgeU γ X A ω') := he ▸ hc0 ω'
  filter_upwards [h1, h2, hu, ae_psiExt_scaled hγ hγ2 hsel hX hA hXA hB hb,
    ae_goodPathF hγ hγ2 hB hsc] with ω k1 k2 hu' hpe hgood
  refine ae_of_all _ fun x hx => ?_
  obtain ⟨hac, hs', hWd, hW0, hex⟩ := hgood
  set b := scaleParam γ (wedgeU γ X A ω') with hbdef
  have hsb : IsSimpleChord (pathTrace (γ ^ 2) (scalePath b (pathOf B ω))) :=
    isSimpleChord_scalePath hb _ hWd hW0 hex hs'
  rw [he] at k1 k2
  have hu2 : ∀ left, UCond (canonical γ (wedgeU γ X A ω')) (Ψ left (scalePath b (pathOf B ω))) :=
    fun left => by have := hu' left; rw [he] at this; exact this
  have hcont := fun left => contData_unscaled_pt hsel hg hb hac hs' hWd hW0 hex left
    (hpe left) (hu2 left)
  have hxneg : x < 0 := by simpa [g1SideHalf] using hx.1
  have hp : 0 < R18.g3zPartner γ (wedgeU γ X A ω') x := by
    have e := g3zPartner_rescale hγ hg hb x
    have h0 : 0 < R18.g3zPartner γ (rescale (wedgeU γ X A ω') (Qc γ) b) (x / b) :=
      hpp (x / b) (div_neg_of_neg_of_pos hxneg hb)
    rw [e] at h0
    exact (div_pos_iff_of_pos_right hb).1 h0
  exact ⟨choiceRegularA_unscaled_pt hsel hg hb hac hs' hWd hW0 hex true (k1 hsb) (hcont true) L x,
    hp, choiceRegularA_unscaled_pt hsel hg hb hac hs' hWd hW0 hex false (k2 hsb) (hcont false) L _⟩

/-- **`G3ZqResclRegStmt` holds.** -/
theorem g3ZqResclRegStmt_holds : G3ZqResclRegStmt :=
  g3ZqResclRegStmt_of_choice g3ZqSChoiceUStmt_holds

end G3ZqS
end Thm18Asm
end QuantumZipper
