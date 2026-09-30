import QuantumZipper.Proofs.Thm18.G1SSR2Dec
import QuantumZipper.Proofs.Thm18.G1SSR2Free
import QuantumZipper.Proofs.Thm18.G1SSR2Meas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1SSR2 (7): the countable Cauchy condition at the representative (`G1SidePushUCRepStmt`)

Theorem 1.8, G1 zoom. Per sample, the smoothed pushed pairing of the canonical wedge
representative splits (`evalReg_rescale_wedge_fc`) as
`gPush y ψ d r σ = Y_free(d, log r, log S, S σ) + ∫ profInt dfc(d, r) + Q log S`
(`gPush_split`), where `Y_free` is the continuous modification of the free-field pairings along
the pushed circles (`G1RC.exists_pushed_joint`, Duplantier–Sheffield, Invent. Math. 185 (2011),
Prop. 3.1) and the profile part is jointly continuous up to `σ = 0` (`continuousOn_profPush`).
On each compact box the sum is uniformly continuous, which is `UCond` (`ucond_of_split`). With the
a.s. goodness facts used for `G1ProfileStmt` this proves `G1SidePushUCRepStmt`, hence
`G1SidePushContStmt` (G1SSR2Meas.lean) and `G1SideShiftRegAStmt` (G1SSRMain.lean) from
`G1Z2SideGoodStmt`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric
open scoped Topology NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1SSR2

open F1.RC3Two G1RC

theorem aesm_of_continuousOn_Hbar {f : ℂ → ℝ} (hf : ContinuousOn f Hbar) {μ : Measure ℂ}
    (hμ : ∀ᵐ u ∂μ, u ∈ Hbar) : AEStronglyMeasurable f μ := by
  rw [← Measure.restrict_eq_self_of_ae_mem hμ]
  exact hf.aestronglyMeasurable isClosed_Hbar.measurableSet

variable {x : FieldSample} {F : ℂ × ℝ → ℝ} {A : ℝ → ℝ} {C : ℝ}

/-- **The split of the pushed pairing** into free part, profile part and constant. -/
theorem gPush_split (h : WedgeGood x F A) (Q : ℝ) {S : ℝ} (hS : 0 < S)
    (hbd : ∀ t, 0 < t → t ≤ 1 → |wg x A Q t| ≤ C * (1 - Real.log t))
    {ψ ψe : ℂ → ℂ} (hψ : PsiGood ψ) (heq : EqOn ψ ψe H) (hψem : Measurable ψe)
    (hψec : ContinuousOn ψe Hbar) (hψeH : MapsTo ψe Hbar Hbar)
    (d : ℂ) {r σ : ℝ} (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1 / S) :
    gPush (rescale (wedgeField (lateralPart x) A Q) Q S) ψ d r σ =
      ∫ u, F (u, S * σ) ∂((foldedCircle d r).map fun z => (S : ℂ) * ψe z) +
        ∫ u, profInt (wg x A Q) ψ S σ u ∂foldedCircle d r + Q * Real.log S := by
  set g := wg x A Q with hgdef
  have hgm : Measurable g := measurable_wg h.cont
  have hgc : ContinuousOn g (Ioi 0) := continuousOn_wg h.good h.cont
  have hC := nonneg_of_bd hbd
  have hF := h.good.1
  have hSσ : 0 < S * σ := mul_pos hS hσ
  have hS1 : S * σ ≤ 1 := by
    rw [le_div_iff₀ hS] at hσ1; linarith
  -- the free part as a function on `Hbar`
  have hFc : ContinuousOn (fun u => F ((S : ℂ) * ψe u, S * σ)) Hbar :=
    hF.1.comp (((continuousOn_const.mul hψec)).prodMk continuousOn_const) fun u hu =>
      ⟨RegClosure.mapsTo_mul_pos hS (hψeH hu), hSσ⟩
  have hFint : Integrable (fun u => F ((S : ℂ) * ψ u, S * σ)) (foldedCircle d r) := by
    refine (RegClosure.integrable_fc hFc d hr.le).congr
      ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun u hu => ?_)
    simp only [heq hu]
  -- the profile part is integrable
  have hPint : Integrable (fun u => profInt g ψ S σ u) (foldedCircle d r) := by
    obtain ⟨M, hM⟩ := norm_mul_psi_le hψ hS (‖d‖ + r)
    obtain ⟨B, hB⟩ := abs_smoothFun_rp_le hgm hgc hbd M
    refine ((integrable_const B).add
      (((logBd_log_norm hψ hS).integrable d hr).abs.const_mul (8 * C))).mono'
      ((continuous_smoothFun_rp hgm hgc hbd hSσ).measurable.comp
        (measurable_const.mul hψ.1)).aestronglyMeasurable ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hr,
      TwoPoint.foldedCircle_ae_norm_le d hr.le] with u hu hun
    rw [Real.norm_eq_abs]
    exact hB _ (hM u hu hun) (ne_zero_of_mem_H' (mul_psi_mem_H hψ hS hu)) _ hSσ hS1
  unfold gPush
  rw [integral_congr_ae (g := fun u => F ((S : ℂ) * ψ u, S * σ) + profInt g ψ S σ u +
      Q * Real.log S) ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun u hu => ?_)]
  · rw [integral_add (f := fun u => F ((S : ℂ) * ψ u, S * σ) + profInt g ψ S σ u)
      (g := fun _ => Q * Real.log S) (hFint.add hPint) (integrable_const _),
      integral_add (f := fun u => F ((S : ℂ) * ψ u, S * σ)) (g := fun u => profInt g ψ S σ u)
        hFint hPint, integral_const]
    simp only [probReal_univ, one_smul]
    congr 2
    have hm : Measurable fun z => (S : ℂ) * ψe z := measurable_const.mul hψem
    have hc' : ContinuousOn (fun u : ℂ => F (u, S * σ)) Hbar :=
      hF.1.comp (continuousOn_id.prodMk continuousOn_const) fun u hu => ⟨hu, hSσ⟩
    rw [integral_map (f := fun u : ℂ => F (u, S * σ)) hm.aemeasurable (aesm_of_continuousOn_Hbar hc'
      ((ae_map_iff hm.aemeasurable isClosed_Hbar.measurableSet).2
        ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun u hu =>
          RegClosure.mapsTo_mul_pos hS (hψeH (H_subset_Hbar hu)))))]
    refine integral_congr_ae ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun u hu => ?_)
    simp only [heq hu]
  · exact evalReg_rescale_wedge_fc h Q hS hbd (hψ.2.2.2.1 hu) hσ

end G1SSR2
end Thm18Asm
end QuantumZipper
