import QuantumZipper.Proofs.Thm18.G1Z2MeasNu
import QuantumZipper.Proofs.Thm18.G1Z2MeasPair

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z2-MEAS, part 5: `G1SideRerootRepStmt` and node B1-MEAS

The measurable representative is the side field `g1z2Field` built with the measurable selection
`Ψ` of `g1PsiSelStmt`. Almost surely, the side field `g1SideField` (the `Classical.epsilon`
uniformizer) and the representative are, up to regularized averages, dilations `rescale x Q b`,
`rescale x Q c` of the pulled-back field `x` of the normalized uniformizer given by the
regularity half (U6 and `G1.regEq_coordChange_comp_mul`). With the regularity package
`G1Z2Good` of `x` (its measure part is the single new input `G1Z2SideGoodStmt`), the rerooted canonical data of both
agree with those of `x` (`g1z2_rerootData_rescale`), the representative has an area limit
(`GoodTransforms.hasAreaLimit_rescale`) and a side boundary limit, hence an a.e.-measurable side
boundary measure (`g1z2_aemeasurable_sideNu`).

`G1Z2SideGoodStmt` (a.s., for every normalized uniformizer of the side domain, the pulled-back
wedge field has an area limit on `ℍ` along all radii `a 2^{-k}`, finite near boundary points and
infinite in total, and a side boundary limit along all radii) is the conformal covariance of the
LQG measures of the `(γ − 2/γ)`-wedge under the side map: Sheffield–Wang, arXiv:1605.06171,
Thm 1.4 (area) and Thm 4.3 (boundary, all maps simultaneously); Duplantier–Sheffield,
arXiv:0808.1560, Prop. 2.1. Regularity (RC2), RC3 and the scale consistency of the test pairings
come from the regularity half (`G1RegExStmt`: PAIR-LIM gives scale consistency,
`g1z2_scaleConsistent_translate`). Own bookkeeping otherwise.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus Factorization

/-- The LQG-measure part of the regularity package: an area limit on `ℍ` along all radii
`a 2^{-k}`, finite near boundary points and infinite in total, and a side boundary limit along
all radii. -/
def G1Z2MeasGood (γ : ℝ) (left : Bool) (x : FieldSample) : Prop :=
  (∃ μ : Measure ℂ, HasAreaLimit γ x μ ∧
    (∀ p : ℝ, ∃ a : ℝ, 0 < a ∧ μ (Metric.ball (p : ℂ) a ∩ H) < 1) ∧ μ H = ⊤) ∧
  (∃ ν : Measure ℝ, G1Z2SideBdryLim γ left x ν)

/-- **Node (LQG measures of the pulled-back side fields).** -/
def G1Z2SideGoodStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool,
    ∀ᵐ ω ∂P, ∀ φ : ℂ → ℂ, IsNormalizedUniformizer (sideDom (sleTrace (γ ^ 2) B ω) left) φ →
      G1Z2MeasGood γ left
        (coordChange (Y ω) (invFunOn φ (sideDom (sleTrace (γ ^ 2) B ω) left)) (Qc γ))

/-- The full package from the measure part, RC2 and PAIR-LIM (`G1.ChoiceRegularCore`). -/
theorem g1z2Good_of_core {γ : ℝ} {left : Bool} {y : FieldSample} {ψ : ℂ → ℂ}
    (hcore : G1.ChoiceRegularCore γ y ψ) (hm : G1Z2MeasGood γ left (coordChange y ψ (Qc γ))) :
    G1Z2Good γ left (coordChange y ψ (Qc γ)) := by
  obtain ⟨⟨F, hF⟩, -, hpair⟩ := hcore
  exact ⟨⟨F, hF⟩, hm.1, hm.2, fun p b hb c hc ρ σ hσ =>
    g1z2_scaleConsistent_translate hF hpair p hb hc ρ σ hσ⟩

/-- Changing the chart off `ℍ` does not change the regularized averages. -/
theorem g1z2_regEq_of_eqOn (y : FieldSample) {F F' : ℂ → ℂ} (h : EqOn F F' H) (Q : ℝ) :
    RegEq (coordChange y F Q) (coordChange y F' Q) := fun k z => by
  unfold avgReg
  simp_rw [g1zMeas_coordChange_fc_congr y h Q _ (radius_pos k)]

/-- The pulled-back field of a dilated chart is the rescaled pulled-back field (`RegEq`). -/
theorem g1z2_regEq_dilate (y : FieldSample) (Q : ℝ) {ψ ψ' : ℂ → ℂ}
    (hψd : DifferentiableOn ℂ ψ H) (hψ0 : ∀ w ∈ H, deriv ψ w ≠ 0) (hψm : Measurable ψ)
    {b : ℝ} (hb : 0 < b) (heq : EqOn ψ' (fun w => ψ ((b : ℂ) * w)) H)
    (hint : ∀ d ∈ Hbar, ∀ r > 0,
      Integrable (fun z => Real.log ‖deriv ψ z‖) (foldedCircle d r))
    (hexact : ∀ d ∈ Hbar, ∀ r > 0,
      evalReg (coordChange y ψ Q) (foldedCircle d r) = coordChange y ψ Q (foldedCircle d r)) :
    RegEq (coordChange y ψ' Q) (rescale (coordChange y ψ Q) Q b) := fun k z =>
  (g1z2_regEq_of_eqOn y heq Q k z).trans
    (G1.regEq_coordChange_comp_mul y Q hψd hψ0 hψm hb hint hexact k z)

/-- The dyadic area approximations converge when the area limit along all radii exists. -/
theorem g1z2_isVagueLimitOn_of_hasAreaLimit {γ : ℝ} {y : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith y F) {μ : Measure ℂ} (h : HasAreaLimit γ y μ) :
    IsVagueLimitOn H (areaApprox γ y) μ :=
  ⟨h.1, h.2.1, fun f hf hfc hfU =>
    ((h.2.2 f hf hfc hfU).comp GoodSample.tendsto_one_goodFilter).congr fun k => by
      simp only [Function.comp, goodRad, GoodSample.areaR_radius γ hF]⟩

/-- **`G1SideRerootRepStmt` from the regularity half and the goodness node.** -/
theorem g1SideRerootRepStmt_of (hR : G1RegExStmt) (hG : G1Z2SideGoodStmt) :
    G1SideRerootRepStmt := by
  intro γ Ω _ P _ B Y hS hIn left
  obtain ⟨Ψ, hΨ⟩ := g1PsiSelStmt γ hS.1 hS.2.1
  have hγ : 0 < γ := hS.1
  have hside : G1RegExSide γ P B Y left := by
    cases left
    · exact (hR γ P B Y hS hIn).2
    · exact (hR γ P B Y hS hIn).1
  have hkey : ∀ᵐ ω ∂P, ∃ x : FieldSample, G1Z2Good γ left x ∧
      (∃ b : ℝ, 0 < b ∧ RegEq (g1SideField γ B Y left ω) (rescale x (Qc γ) b)) ∧
      ∃ c : ℝ, 0 < c ∧ RegEq (g1z2Field γ Ψ B Y left ω) (rescale x (Qc γ) c) := by
    filter_upwards [hside, hIn.2.2, hS.2.2.1.cont, hG γ P B Y hS hIn left]
      with ω ⟨φ, hφ, hcore⟩ hω hc hgood
    have hη : IsSimpleChord (pathTrace (γ ^ 2) (pathOf B ω)) := hω.1
    obtain ⟨φ₀, hφ₀, hΨe⟩ := hΨ.2.2 (pathOf B ω) hc hη left
    have hu : IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2) (pathOf B ω)) left)
        (uniformizer (sideDom (pathTrace (γ ^ 2) (pathOf B ω)) left)) := by
      cases left
      · exact hω.2.2.2
      · exact hω.2.2.1
    have hD : IsOpen (sideDom (pathTrace (γ ^ 2) (pathOf B ω)) left) :=
      G1.isOpen_component hω.1 left
    obtain ⟨hψd, hψ0, hψm, -⟩ := G1.invFunOn_props hD hφ
    have hint := G1.choiceRegular_logDeriv hD hφ
    have hexact := hcore.2.1
    obtain ⟨b, hb, hbeq⟩ := g1z2_invFunOn_eq_dilate hη left hφ hu
    obtain ⟨c, hc', hceq⟩ := g1z2_invFunOn_eq_dilate hη left hφ hφ₀
    refine ⟨_, g1z2Good_of_core hcore (hgood φ hφ), ⟨b, hb, ?_⟩, ⟨c, hc', ?_⟩⟩
    · exact g1z2_regEq_dilate (Y ω) (Qc γ) hψd hψ0 hψm hb hbeq hint hexact
    · unfold g1z2Field
      rw [hΨe]
      exact g1z2_regEq_dilate (Y ω) (Qc γ) hψd hψ0 hψm hc' hceq hint hexact
  have hcoords := g1z2_aemeasurable_coords γ hΨ (QuantumZipper.IsBrownianReal.aemeasurable_pathOf hS.2.2.1) hIn.2.1.fst left
  refine ⟨g1z2Field γ Ψ B Y left, hcoords, ?_, ?_, fun R => ?_⟩
  · refine g1z2_aemeasurable_sideNu hcoords ?_
    filter_upwards [hkey] with ω ⟨x, hx, _, c, hc, hZ₀⟩
    obtain ⟨⟨F, hF⟩, -, ⟨ν, hν⟩, -⟩ := hx
    have havg : avgReg (g1z2Field γ Ψ B Y left ω) = avgReg (rescale x (Qc γ) c) :=
      funext fun k => funext fun z => hZ₀ k z
    have hbd : bdryApprox γ (g1z2Field γ Ψ B Y left ω) = bdryApprox γ (rescale x (Qc γ) c) := by
      funext k; unfold bdryApprox; rw [havg]
    exact ⟨_, hbd ▸ g1z2_isVagueLimitOnR_rescale hγ hF hν hc⟩
  · filter_upwards [hkey, g1z2_ae_isRegularSample hR γ hS hIn hΨ left]
      with ω ⟨x, hx, _, c, hc, hZ₀⟩ hreg
    refine ⟨hreg, ?_⟩
    obtain ⟨⟨F, hF⟩, ⟨μ, hμ, -, -⟩, -, -⟩ := hx
    have havg : avgReg (g1z2Field γ Ψ B Y left ω) = avgReg (rescale x (Qc γ) c) :=
      funext fun k => funext fun z => hZ₀ k z
    have har : areaApprox γ (g1z2Field γ Ψ B Y left ω) = areaApprox γ (rescale x (Qc γ) c) := by
      funext k; unfold areaApprox; rw [havg]
    show ∃ μ', IsVagueLimitOn H (areaApprox γ (g1z2Field γ Ψ B Y left ω)) μ'
    rw [har]
    exact ⟨_, g1z2_isVagueLimitOn_of_hasAreaLimit (hF.rescale' (Qc γ) hc)
      (GoodTransforms.hasAreaLimit_rescale ⟨F, hF⟩ hγ hμ hc)⟩
  · filter_upwards [hkey] with ω ⟨x, hx, ⟨b, hb, hZ⟩, c, hc, hZ₀⟩ ℓ
    simp only [g1zRerootData]
    rw [g1z2_rerootData_rescale hγ hx hb hZ R ℓ, g1z2_rerootData_rescale hγ hx hc hZ₀ R ℓ]

/-- **Node B1-MEAS from the regularity half and the goodness node.** -/
theorem g1SideTranslMeasStmt_of_good (hR : G1RegExStmt) (hG : G1Z2SideGoodStmt) :
    G1SideTranslMeasStmt :=
  g1SideTranslMeasStmt_of_regEx hR (g1SideRerootRepStmt_of hR hG)

/-- **Node B1-MEAS from the rest node of the regularity half and the goodness node.** -/
theorem g1SideTranslMeasStmt_of_rest_good (h3 : G1RegRepRestStmt) (hG : G1Z2SideGoodStmt) :
    G1SideTranslMeasStmt :=
  g1SideTranslMeasStmt_of_good (g1RegExStmt_of_rest h3) hG

end Thm18Asm
end QuantumZipper
