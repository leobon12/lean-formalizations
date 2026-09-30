import QuantumZipper.Proofs.Zipper.JointModFinal
import QuantumZipper.Proofs.Thm18.G1FMDPart

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CFG-FIRSTMODE (1): the deterministic part of the unzipped raw values is bounded

The raw values of the unzipped `Γ⁰` field split as `ZE + Ddet` (`RegUnif.ae_raw_eq`), with the
deterministic part `Ddet κ γ W (t, (v, s)) = (2/√κ) ∫ log ‖ψ_t‖ dfc(v, s) + Q ∫ log ‖ψ_t'‖ dfc(v, s)`,
`ψ_t = fwdMapInv W t`. Both integrands are jointly continuous on `[0,T] × ℍ`
(`RegUnif.continuousOn_fwdMapInv_joint`, `RegUnif.continuousOn_log_deriv_fwdMapInv_joint`), hence
bounded on `[0,T] × K'` for the compact thickening `K'` of a compact `K ⊆ ℍ`. So `Ddet` is bounded
uniformly for `t ∈ [0,T]`, centres within `τ₀` of `K` and radii `s ∈ (0, τ₀]`
(`CfgFM.abs_ddet_le`); its first circle mode is then `≤ 2π M`. Own elementary argument.
-/

noncomputable section

open MeasureTheory Filter Metric Set Function
open scoped Topology NNReal

namespace QuantumZipper.E6
namespace CfgFM

open RegUnif RegCont

variable {W : ℝ → ℝ}

/-- **Uniform bound of the deterministic part.** -/
theorem abs_ddet_le (hW : Continuous W) (hW0 : W 0 = 0) (κ γ T : ℝ) {K : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ H) :
    ∃ M τ₀ : ℝ, 0 ≤ M ∧ 0 < τ₀ ∧ (∀ w ∈ K, τ₀ < w.im) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ w ∈ K, ∀ v : ℂ, dist v w ≤ τ₀ → ∀ s : ℝ, 0 < s → s ≤ τ₀ →
        |Ddet κ γ W (t, (v, s))| ≤ M := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, 1, le_rfl, one_pos, fun w hw => absurd hw (notMem_empty w),
      fun t _ w hw => absurd hw (notMem_empty w)⟩
  obtain ⟨z0, hz0, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  have hm : 0 < z0.im := hKH hz0
  set K' := cthickening (z0.im / 2) K with hK'
  have hK'c : IsCompact K' := hK.cthickening
  have hK'H : ∀ u ∈ K', z0.im / 2 ≤ u.im := by
    intro u hu
    rw [hK', hK.cthickening_eq_biUnion_closedBall (by positivity)] at hu
    obtain ⟨w, hw, hu'⟩ := mem_iUnion₂.1 hu
    have h1 : dist u w ≤ z0.im / 2 := mem_closedBall.1 hu'
    have h2 : |(u - w).im| ≤ ‖u - w‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, ← dist_eq_norm] at h2
    have h3 : z0.im ≤ w.im := hmin hw
    linarith [neg_abs_le (u.im - w.im)]
  have hK'sub : K' ⊆ H := fun u hu => show 0 < u.im by linarith [hK'H u hu]
  have hprod : IsCompact (Icc (0 : ℝ) T ×ˢ K') := isCompact_Icc.prod hK'c
  have hsubH : Icc (0 : ℝ) T ×ˢ K' ⊆ Icc 0 T ×ˢ H := prod_mono le_rfl hK'sub
  have hc1 : ContinuousOn (fun p : ℝ × ℂ => Real.log ‖fwdMapInv W p.1 p.2‖) (Icc 0 T ×ˢ H) := by
    refine ContinuousOn.log (continuousOn_fwdMapInv_joint hW hW0 T).norm fun p hp => ?_
    exact norm_ne_zero_iff.2 (Thm18Asm.G1RC.ne_zero_of_mem_H' (RS.fwdMapInv_mem_H hW hW0 hp.1.1 hp.2))
  obtain ⟨M₁, hM₁⟩ := hprod.exists_bound_of_continuousOn (hc1.mono hsubH)
  obtain ⟨M₂, hM₂⟩ := hprod.exists_bound_of_continuousOn
    ((continuousOn_log_deriv_fwdMapInv_joint hW hW0 T).mono hsubH)
  refine ⟨|2 / Real.sqrt κ| * |M₁| + |Qc γ| * |M₂|, z0.im / 4, by positivity, by positivity,
    fun w hw => by have := hmin hw; simp only [mem_setOf_eq] at this; linarith, fun t ht w hw v hv s hs hsτ => ?_⟩
  have hnear : ∀ u : ℂ, dist u w ≤ 2 * (z0.im / 4) → (t, u) ∈ Icc (0 : ℝ) T ×ˢ K' := by
    intro u hu
    refine ⟨ht, mem_cthickening_of_dist_le u w _ K hw (by linarith)⟩
  have hvH : v ∈ Hbar := by
    have h2 : |(v - w).im| ≤ ‖v - w‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, ← dist_eq_norm] at h2
    have h3 : z0.im ≤ w.im := hmin hw
    show (0 : ℝ) ≤ v.im
    linarith [neg_abs_le (v.im - w.im)]
  have e1 := Thm18Asm.G1FM.abs_integral_fc_le (G := fun u => Real.log ‖fwdMapInv W t u‖) (M := |M₁|)
    (τ₀ := z0.im / 4) (w := w) (fun u hu => by
      have := hM₁ _ (hnear u hu)
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_abs_self _)) hvH hv hs.le hsτ
  have e2 := Thm18Asm.G1FM.abs_integral_fc_le (G := fun u => Real.log ‖deriv (fwdMapInv W t) u‖)
    (M := |M₂|) (τ₀ := z0.im / 4) (w := w) (fun u hu => by
      have := hM₂ _ (hnear u hu)
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_abs_self _)) hvH hv hs.le hsτ
  have emap : ∫ z, Real.log ‖z‖ ∂νT W v s t = ∫ u, Real.log ‖fwdMapInv W t u‖ ∂foldedCircle v s :=
    integral_map (aemeasurable_fwdMapInv hW hW0 ht.1 v hs)
      (Real.measurable_log.comp measurable_norm).aestronglyMeasurable
  show |2 / Real.sqrt κ * (∫ z, Real.log ‖z‖ ∂νT W v s t) +
    Qc γ * ∫ u, Real.log ‖deriv (fwdMapInv W t) u‖ ∂foldedCircle v s| ≤ _
  rw [emap]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left e1 (abs_nonneg _))
    (mul_le_mul_of_nonneg_left e2 (abs_nonneg _))

end CfgFM
end QuantumZipper.E6
