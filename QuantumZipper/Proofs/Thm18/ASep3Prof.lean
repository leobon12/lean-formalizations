import QuantumZipper.Proofs.Thm18.ASep3Resc
import QuantumZipper.Proofs.Thm18.ASep2Conj2
import QuantumZipper.Proofs.Thm18.ASepWedgeCongr

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP3 (step 13): a continuous profile commutes with the rescaling

For a regular sample `x` and a continuous profile `g`, the rescaled field
`rescale (ofFun g + x) Q s` has the same dyadic averages as `ofFun (g(s ·)) + rescale x Q s`
(`avgReg_rescale_ofFun_add`): at every folded circle both raw values equal
`evalReg x (fc(s c, s ρ)) + ∫ g dfc(s c, s ρ) + Q log s` (`evalReg_ofFun_add_of_tendsto_cont`,
`F2.rescale_apply_eq_evalReg_add`, `Thm18Asm.foldedCircle_map_mul`). Hence
`g4SepConcl0_rescale_ofFun_add_iff`: for continuous profiles, the conclusion of
`G4SepScale0Stmt` is the conclusion for the field `ofFun (g(s ·)) + rescale X Q s`, i.e. the
form of `ae_conj1_add_good`/`ae_conj2_add_good` with the free field replaced by its rescaling
(whose scale-uniform inputs are ASep3PsiRun/ASep3Box/ASep3Inner). Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace QuantumZipper
namespace ASep

/-- Raw value of `rescale (ofFun g + x) Q s` at a folded circle. -/
theorem rescale_ofFun_add_fc {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    {g : ℂ → ℝ} (hg : Continuous g) (Q : ℝ) {s : ℝ} (hs : 0 < s) (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    rescale (ofFun g + x) Q s (foldedCircle c ρ) =
      (ofFun (fun z => g ((s : ℂ) * z)) + rescale x Q s) (foldedCircle c ρ) := by
  have hm : Measurable fun z : ℂ => (s : ℂ) * z := measurable_const_mul _
  set c' : ℂ := foldH ((s : ℂ) * c) with hc'
  have hc'H : c' ∈ Hbar := CircleFubini.foldH_mem_Hbar' _
  have hsρ : 0 < s * ρ := mul_pos hs hρ
  have efc : (foldedCircle c ρ).map (fun z => (s : ℂ) * z) = foldedCircle c' (s * ρ) := by
    rw [Thm18Asm.foldedCircle_map_mul hs, hc', WedgeTK.fc_foldH_eq]
  have hK : IsCompact (closedBall (0 : ℂ) (‖c'‖ + s * ρ) ∩ Hbar) :=
    (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have hν : ∀ᵐ w ∂foldedCircle c' (s * ρ), w ∈ closedBall (0 : ℂ) (‖c'‖ + s * ρ) ∩ Hbar := by
    filter_upwards [TwoPoint.foldedCircle_ae_norm_le c' hsρ.le, RegClosure.fc_ae_mem_Hbar c' _]
      with w h1 h2
    exact ⟨mem_closedBall_zero_iff.2 h1, h2⟩
  have hL : Tendsto (fun j => ∫ w, avgReg x j w ∂foldedCircle c' (s * ρ)) atTop
      (𝓝 (evalReg x (foldedCircle c' (s * ρ)))) := by
    rw [hF.evalReg_fc_of_mem hc'H hsρ]
    exact tendsto_integral_avgReg_fc_of_reg hF hc'H hsρ
  have hE := evalReg_ofFun_add_of_tendsto_cont hF hg hK inter_subset_right hν hL
  show rescale (ofFun g + x) Q s (foldedCircle c ρ) =
    ofFun (fun z => g ((s : ℂ) * z)) (foldedCircle c ρ) + rescale x Q s (foldedCircle c ρ)
  rw [F2.rescale_apply_eq_evalReg_add, F2.rescale_apply_eq_evalReg_add, efc, hE]
  have hint : ∫ z, g ((s : ℂ) * z) ∂foldedCircle c ρ = ∫ w, g w ∂foldedCircle c' (s * ρ) := by
    rw [← efc, integral_map hm.aemeasurable hg.aestronglyMeasurable]
  show _ = ∫ z, g ((s : ℂ) * z) ∂foldedCircle c ρ + _
  rw [hint]
  ring

/-- **A continuous profile commutes with the rescaling** (dyadic averages). -/
theorem avgReg_rescale_ofFun_add {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    {g : ℂ → ℝ} (hg : Continuous g) (Q : ℝ) {s : ℝ} (hs : 0 < s) :
    avgReg (rescale (ofFun g + x) Q s) =
      avgReg (ofFun (fun z => g ((s : ℂ) * z)) + rescale x Q s) := by
  funext k z
  unfold avgReg
  congr 1
  funext n
  exact rescale_ofFun_add_fc hF hg Q hs _ (radius_pos k)

/-- **The conclusion for a rescaled field with a continuous profile.** -/
theorem g4SepConcl0_rescale_ofFun_add_iff {γ : ℝ} {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith x F) {g : ℂ → ℝ} (hg : Continuous g) {s : ℝ} (hs : 0 < s)
    (W : ℝ → ℝ) :
    G4SepConcl0 γ (rescale (ofFun g + x) (Qc γ) s, W) ↔
      G4SepConcl0 γ (ofFun (fun z => g ((s : ℂ) * z)) + rescale x (Qc γ) s, W) :=
  g4SepConcl0_congr_avgReg (avgReg_rescale_ofFun_add hF hg (Qc γ) hs) W

end ASep
end QuantumZipper
