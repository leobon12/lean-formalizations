import QuantumZipper.Proofs.Thm18.G1ZMeasNode
import QuantumZipper.Proofs.Thm18.G1Rescale
import QuantumZipper.Proofs.Thm18.G1RegCore
import QuantumZipper.Proofs.Thm18.G1CoreSplit
import QuantumZipper.Proofs.Thm18.G1RegRepMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-MEAS, part 3: RC2 for the chosen uniformizer from the G1 regularity half

`G1SideRegSampleStmt` (G1ZMeasNode.lean: a.s. the side field `g1SideField`, built with the
`Classical.epsilon`-chosen `uniformizer`, is a regular sample) follows from the existential
regularity half `G1RegExStmt` (G1CoreSplit.lean: RC2/RC3 for *some* normalized uniformizer):
by U6 the two inverse uniformizers differ by a dilation on `ℍ`
(`G1.exists_invFunOn_uniformizer_eq`), and the pulled-back field of `ψ ∘ (b ·)` has the same raw
folded-circle values as the rescaling by `b` of the pulled-back field of `ψ` (RC3; the
computation `G1.coordChange_comp_mul_fc`, `G1.rescale_fc_apply` of G1Rescale.lean), which is
regular (`IsRegularSample.rescale'`); regularity only reads the raw folded-circle values.

Own argument (bookkeeping on top of G1Rescale.lean).
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus

/-- Changing the conformal map off `ℍ` does not change the raw values at folded circles. -/
theorem g1zMeas_coordChange_fc_congr (y : FieldSample) {F F' : ℂ → ℂ} (hFF : EqOn F F' H)
    (Q : ℝ) (d : ℂ) {r : ℝ} (hr : 0 < r) :
    coordChange y F Q (foldedCircle d r) = coordChange y F' Q (foldedCircle d r) := by
  have hμ := TwoPoint.foldedCircle_ae_mem_H d hr
  unfold coordChange
  have h1 : (foldedCircle d r).map F = (foldedCircle d r).map F' :=
    Measure.map_congr (hμ.mono fun z hz => hFF hz)
  have h2 : ∫ z, Real.log ‖deriv F z‖ ∂(foldedCircle d r) =
      ∫ z, Real.log ‖deriv F' z‖ ∂(foldedCircle d r) :=
    integral_congr_ae (hμ.mono fun z hz => by
      show Real.log ‖deriv F z‖ = Real.log ‖deriv F' z‖
      rw [Filter.EventuallyEq.deriv_eq (eventuallyEq_of_mem (isOpen_H.mem_nhds hz) hFF)])
  rw [h1, h2]

/-- **RC2 transfers along a dilation of the chart.** If `ψ' = ψ ∘ (b ·)` on `ℍ`, `log|ψ'|` is
integrable on folded circles, the pulled-back field `coordChange y ψ Q` is regular and its
folded-circle values are its regularized ones (RC3), then `coordChange y ψ' Q` is regular. -/
theorem g1zMeas_isRegularSample_comp_mul (y : FieldSample) (Q : ℝ) {ψ ψ' : ℂ → ℂ}
    (hψd : DifferentiableOn ℂ ψ H) (hψ0 : ∀ w ∈ H, deriv ψ w ≠ 0) (hψm : Measurable ψ)
    {b : ℝ} (hb : 0 < b) (heq : EqOn ψ' (fun w => ψ ((b : ℂ) * w)) H)
    (hint : ∀ d ∈ Hbar, ∀ r > 0,
      Integrable (fun z => Real.log ‖deriv ψ z‖) (foldedCircle d r))
    (hexact : ∀ d ∈ Hbar, ∀ r > 0,
      evalReg (coordChange y ψ Q) (foldedCircle d r) = coordChange y ψ Q (foldedCircle d r))
    (hreg : IsRegularSample (coordChange y ψ Q)) :
    IsRegularSample (coordChange y ψ' Q) := by
  have key : ∀ d : ℂ, ∀ r > 0, coordChange y ψ' Q (foldedCircle d r) =
      rescale (coordChange y ψ Q) Q b (foldedCircle d r) := by
    intro d r hr
    have hbr : 0 < b * r := mul_pos hb hr
    have hH := CircleFubini.foldH_mem_Hbar' ((b : ℂ) * d)
    have hint' := hint _ hH _ hbr
    rw [WedgeTK.fc_foldH_eq] at hint'
    rw [g1zMeas_coordChange_fc_congr y heq Q d hr,
      G1.coordChange_comp_mul_fc y Q hψd hψ0 hψm hb d hr hint', G1.rescale_fc_apply _ Q hb,
      hexact _ hH _ hbr, WedgeTK.fc_foldH_eq]
  have hc : CoordsFull.coordsFull (coordChange y ψ' Q) =
      CoordsFull.coordsFull (rescale (coordChange y ψ Q) Q b) := by
    funext i
    have hr : 0 < (CoordsFull.fullIndex i).2 := by
      unfold CoordsFull.fullIndex; positivity
    exact key _ _ hr
  obtain ⟨F, hF⟩ := hreg.rescale' Q hb
  exact ⟨F, (G1Meas.isRegularWith_congr_coordsFull hc F).2 hF⟩

/-- **`G1SideRegSampleStmt` from the existential regularity half.** -/
theorem g1SideRegSampleStmt_of_regEx (h : G1RegExStmt) : G1SideRegSampleStmt := by
  intro γ Ω _ P _ B Y hS hIn left
  have hside : G1RegExSide γ P B Y left := by
    cases left
    · exact (h γ P B Y hS hIn).2
    · exact (h γ P B Y hS hIn).1
  filter_upwards [hside, hIn.2.2] with ω ⟨φ, hφ, hcore⟩ hω
  set η := sleTrace (γ ^ 2) B ω with hη
  have hu : IsNormalizedUniformizer (if left then leftComponent η else rightComponent η)
      (uniformizer (if left then leftComponent η else rightComponent η)) := by
    cases left
    · exact hω.2.2.2
    · exact hω.2.2.1
  have hD := G1.isOpen_component hω.1 left
  obtain ⟨b, hb, heq⟩ := G1.exists_invFunOn_uniformizer_eq hω.1 left hφ hu
  obtain ⟨hψd, hψ0, hψm, -⟩ := G1.invFunOn_props hD hφ
  obtain ⟨hreg, hexact, -⟩ := hcore
  exact g1zMeas_isRegularSample_comp_mul (Y ω) (Qc γ) hψd hψ0 hψm hb heq
    (G1.choiceRegular_logDeriv hD hφ) hexact hreg

/-- **Node B1-MEAS from the regularity half and the measurable representative.** -/
theorem g1SideTranslMeasStmt_of_regEx (hR : G1RegExStmt) (hRep : G1SideRerootRepStmt) :
    G1SideTranslMeasStmt :=
  g1SideTranslMeasStmt_of (g1SideRegSampleStmt_of_regEx hR) hRep

end Thm18Asm
end QuantumZipper
