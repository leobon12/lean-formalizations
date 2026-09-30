import QuantumZipper.Proofs.Section5.Prop16LitDilDet2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: the dilation event from local regularity (D98)

`dilGood_of_localAreaRegular`: a locally regular field satisfies the dilation event at every
scale `s > 0` (the local dilation rule `isVagueLimitOn_rescale_local`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace Prop16Lit

open ExA GoodSample

theorem test_div {r s : ℝ} (hs : 0 < s) {F : ℂ → ℝ} (hFc : Continuous F) (hFs : HasCompactSupport F)
    (hFU : tsupport F ⊆ ball 0 (r / s) ∩ H) :
    Continuous (fun z => F (z / s)) ∧ HasCompactSupport (fun z => F (z / s)) ∧
      tsupport (fun z => F (z / s)) ⊆ ball 0 r ∩ H := by
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  set h' : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ (s : ℂ) hsc
  have hsymm : ∀ z, h'.symm z = z / s := fun z => by simp [h', div_eq_inv_mul]
  have hGe : (fun z => F (z / s)) = F ∘ h'.symm := funext fun z => by simp [hsymm]
  refine ⟨hFc.comp (continuous_id.div_const _), hGe ▸ hFs.comp_homeomorph h'.symm, ?_⟩
  intro w hw
  rw [hGe, tsupport_comp_eq_preimage] at hw
  have hw' := hFU hw
  rw [hsymm, ← preimage_mul_ball_inter_H hs] at hw'
  simpa [mul_div_cancel₀ _ hsc] using hw'

/-- Eventual continuity of the circle averages of the rescaled field on compacts. -/
theorem eventually_continuousOn_avgReg_rescale {Z : FieldSample} {r : ℝ} {μ : Measure ℂ} {γ : ℝ}
    (hR : LocalAreaRegular γ Z (ball 0 r ∩ H) μ) {s : ℝ} (hs : 0 < s) (Q : ℝ) {K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ ball 0 (r / s) ∩ H) :
    ∀ᶠ k in atTop, ContinuousOn (avgReg (rescale Z Q s) k) K := by
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hUo : IsOpen (ball (0 : ℂ) r ∩ H) := isOpen_ball.inter isOpen_H
  set Ks := (fun z => (s : ℂ) * z) '' K with hKsdef
  have hKs : IsCompact Ks := hK.image (continuous_const.mul continuous_id)
  have hKsU : Ks ⊆ ball 0 r ∩ H := by
    rintro _ ⟨z, hz, rfl⟩
    have := hKU hz
    rw [← preimage_mul_ball_inter_H hs] at this
    exact this
  obtain ⟨ε₀, hε₀, hε₀U⟩ := hKs.exists_cthickening_subset_open hUo hKsU
  have hK₂ : IsCompact (cthickening ε₀ Ks) := hKs.cthickening
  obtain ⟨ρ₀, hρ₀, hc⟩ := hR.2.2.1 _ hK₂ hε₀U
  have hK₂H : cthickening ε₀ Ks ⊆ Hbar := fun w hw => H_subset_Hbar (hε₀U hw).2
  have hrad : ∀ᶠ k in atTop, s * radius k < ρ₀ := by
    have ht : Tendsto (fun k => s * radius k) atTop (𝓝 0) := by
      simpa using (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).const_mul s
    exact ht.eventually (gt_mem_nhds hρ₀)
  filter_upwards [hrad] with k hk
  have hck := hc _ (mul_pos hs (radius_pos k)) hk
  have hcomp : ContinuousOn (fun z => evalReg Z (foldedCircle ((s : ℂ) * z) (s * radius k)) +
      Q * Real.log s) K :=
    (hck.comp (continuous_const.mul continuous_id).continuousOn fun z hz =>
      self_subset_cthickening Ks (mem_image_of_mem _ hz)).add continuousOn_const
  refine hcomp.congr fun z hz => ?_
  have hszK : (s : ℂ) * z ∈ Ks := mem_image_of_mem _ hz
  have hzH : z ∈ Hbar := H_subset_Hbar (hKU hz).2
  refine avgReg_rescale_local hs hK₂H hck Q rfl hzH ?_ (self_subset_cthickening Ks hszK)
  have hn := (RegClosure.tendsto_dyadicRoundC z).eventually
    (Metric.ball_mem_nhds z (by positivity : (0 : ℝ) < ε₀ / s))
  filter_upwards [hn] with n hn
  refine mem_cthickening_of_dist_le _ _ ε₀ Ks hszK ?_
  rw [dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
  have := mem_ball.1 hn
  rw [dist_eq_norm] at this
  have h2 : s * ‖dyadicRoundC n z - z‖ < s * (ε₀ / s) := mul_lt_mul_of_pos_left this hs
  rw [mul_div_cancel₀ _ hs.ne'] at h2
  exact h2.le

/-- **Local regularity gives the dilation event at every positive scale.** -/
theorem dilGood_of_localAreaRegular {γ : ℝ} (hγ : 0 < γ) {Z : FieldSample} {r : ℝ}
    {μ : Measure ℂ} (hR : LocalAreaRegular γ Z (ball 0 r ∩ H) μ) {s : ℝ} (hs : 0 < s) :
    DilGood γ Z r s := by
  have hUo : IsOpen (ball (0 : ℂ) r ∩ H) := isOpen_ball.inter isOpen_H
  have hv := hR.isVagueLimitOn
  have hc := isVagueLimitOn_rescale_local hγ hUo inter_subset_right hR.2.2.1 hR.1 hR.2.1
    hR.2.2.2.2 hs
  rw [preimage_mul_ball_inter_H hs] at hc
  refine ⟨goodA_of_vague hc fun K hK hKU =>
    eventually_continuousOn_avgReg_rescale hR hs (Qc γ) hK hKU, fun n g hg => ?_⟩
  obtain ⟨hgc, hgs, -⟩ := famF_dense.1 g hg
  have hFc : Continuous fun z => hbCut (r / s) n z * g z := (continuous_hbCut _ n).mul hgc
  have hFs : HasCompactSupport fun z => hbCut (r / s) n z * g z := hgs.mul_left
  have hFU : tsupport (fun z => hbCut (r / s) n z * g z) ⊆ ball 0 (r / s) ∩ H :=
    (tsupport_mul_subset_left).trans (tsupport_hbCut _ n)
  obtain ⟨hGc, hGs, hGU⟩ := test_div hs hFc hFs hFU
  refine ⟨_, hc.2.2 _ hFc hFs hFU, ?_⟩
  have hmd : Measurable fun z : ℂ => z / (s : ℂ) := measurable_id.div_const _
  rw [integral_map hmd.aemeasurable hFc.aestronglyMeasurable]
  exact hv.2.2 _ hGc hGs hGU

end Prop16Lit
end QuantumZipper
