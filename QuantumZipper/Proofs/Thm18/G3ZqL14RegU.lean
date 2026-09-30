import QuantumZipper.Proofs.Thm18.G3ZqL10Cert
import QuantumZipper.Proofs.GFF.CircleContinuity
import QuantumZipper.Proofs.Thm18.G3ZqL11Reg
import QuantumZipper.Proofs.Thm18.G3ZqTop
import QuantumZipper.Proofs.Thm18.G3ZqPath
import QuantumZipper.Proofs.Thm18.G3ZqFLeaf
import QuantumZipper.Proofs.Thm18.G3ZqG3LRegG
import QuantumZipper.Proofs.Thm18.G3ZqG3Unif
import QuantumZipper.Proofs.Thm18.G3ZqSTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-LOC (14): the one-point unscaled-wedge regularity node holds

`G3ZqL1RegUStmt` (G3ZqL11Reg), one-point copy of the helper's proof of `G3ZqS.g3ZqSChoiceUStmt_holds`
(G3ZqSTop) with the partner dropped: the RegShift clauses are `G3ZqS.ae_regShiftU`, the
`ChoiceRegularA` clause is `G3ZqS.choiceRegularA_unscaled_pt` along the randomly scaled Brownian
motion on the product space (no quantifier swap). Hence `G3ZqL1ResclRegStmt` holds and
`G1WedgePalmLimStmt` follows from `G3ZqL1PathUStmt` alone (`g1WedgePalmLimStmt_of_pathU'`).
Sheffield, arXiv:1012.4797, p. 70. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqL

open G1Zm G3Zq G3Zr G3Z2b2 G1SSR2 G3ZqS

/-- **`G3ZqL1RegUStmt` holds.** -/
theorem g3ZqL1RegUStmt_holds : G3ZqL1RegUStmt := by
  intro γ hγ hγ2 Ψ hsel Ω' _ P' _ X A hX hA hXA Ω _ P _ B hB hsc left U L
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
  filter_upwards [ht left, hce,
    LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hαQ Ω' _ P' X A inferInstance hX hA hXA,
    ae_ucond_scaled hγ hγ2 hsel hX hA hXA hB hc0, ae_regShiftU hγ hγ2 hsel hX hA hXA hB hsc]
    with ω' h1 he hg hu hrs
  have hb : 0 < scaleParam γ (wedgeU γ X A ω') := he ▸ hc0 ω'
  filter_upwards [h1, hu, ae_psiExt_scaled hγ hγ2 hsel hX hA hXA hB hb,
    ae_goodPathF hγ hγ2 hB hsc, hrs] with ω k1 hu' hpe hgood hr
  refine ae_of_all _ fun x _ => ?_
  obtain ⟨hac, hs', hWd, hW0, hex⟩ := hgood
  set b := scaleParam γ (wedgeU γ X A ω') with hbdef
  have hsb : IsSimpleChord (pathTrace (γ ^ 2) (scalePath b (pathOf B ω))) :=
    isSimpleChord_scalePath hb _ hWd hW0 hex hs'
  rw [he] at k1
  have hu2 : UCond (canonical γ (wedgeU γ X A ω')) (Ψ left (scalePath b (pathOf B ω))) := by
    have := hu' left; rw [he] at this; exact this
  have hcont := contData_unscaled_pt hsel hg hb hac hs' hWd hW0 hex left (hpe left) hu2
  exact ⟨(hr left x).1, (hr left x).2,
    choiceRegularA_unscaled_pt hsel hg hb hac hs' hWd hW0 hex left (k1 hsb) hcont L x⟩

/-- **`G3ZqL1ResclRegStmt` holds.** -/
theorem g3ZqL1ResclRegStmt_holds : G3ZqL1ResclRegStmt :=
  g3ZqL1ResclRegStmt_of_regU g3ZqL1RegUStmt_holds

end G3ZqL
end Thm18Asm
end QuantumZipper
