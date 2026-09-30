import QuantumZipper.Proofs.Zipper.SWCoreDefs
import QuantumZipper.Proofs.Zipper.AreaCoordCont
import QuantumZipper.Proofs.Loewner.ReverseHolo
import QuantumZipper.Proofs.RS.GenerationBasic
import QuantumZipper.Proofs.RS.KoebeLoewnerTime
import QuantumZipper.Proofs.RS.TraceShift

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A6-FLOW: Loewner flow maps on a rational rectangle lie in one rational area class

For a continuous driver `W` with `W 0 = 0`, `T ≥ 0` and a rectangle `K = [a,b] × [c,d]` with
`c > 0`, all maps `fwdMapInv W t`, `t ∈ [0,T]`, belong to one `AreaClass a b c d ρ M m` with
rational `ρ, M, m`, `ρ, m > 0`. Own elementary compactness argument: the flow image of the compact
rectangle `C ⊇ thickening (c/2) K` inside `ℍ` is compact in `ℍ` (`E6.isCompact_flowImage`), and
`log ‖ψ_t'‖` is jointly continuous (`RegUnif.continuousOn_log_deriv_fwdMapInv_joint`) with
`ψ_t' ≠ 0` (`QuantumZipper.deriv_revMap_ne_zero`).
-/

open MeasureTheory Filter Set Metric

namespace QuantumZipper
namespace SWCore

theorem swA6_isCompact_rectC (a b c d : ℝ) : IsCompact (rectC a b c d) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_Icc.preimage Complex.continuous_re).inter
      (isClosed_Icc.preimage Complex.continuous_im)
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := |a| + |b| + (|c| + |d|))).subset
      fun z hz => ?_
    rw [mem_closedBall, dist_zero_right]
    refine (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add ?_ ?_)
    · exact abs_le_max_abs_abs hz.1.1 hz.1.2 |>.trans (max_le (by linarith [abs_nonneg b])
        (by linarith [abs_nonneg a]))
    · exact abs_le_max_abs_abs hz.2.1 hz.2.2 |>.trans (max_le (by linarith [abs_nonneg d])
        (by linarith [abs_nonneg c]))

/-- **Loewner flow maps on a rational rectangle lie in one rational `AreaClass`.** -/
theorem flow_mem_areaClass {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    {a b c d : ℚ} (hc : (0 : ℝ) < c) :
    ∃ ρ M m : ℚ, (0 : ℝ) < ρ ∧ (0 : ℝ) < m ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, fwdMapInv W t ∈ AreaClass a b c d ρ M m := by
  set K := rectC (a : ℝ) b c d with hKdef
  set C := rectC ((a : ℝ) - c / 2) (b + c / 2) (c / 2) (d + c / 2) with hCdef
  have hc2 : (0 : ℝ) < c / 2 := by linarith
  have hCH : C ⊆ H := fun z hz => show 0 < z.im from lt_of_lt_of_le hc2 hz.2.1
  have hthick : thickening ((c : ℝ) / 2) K ⊆ C := by
    intro w hw
    obtain ⟨z, hz, hd⟩ := mem_thickening_iff.1 hw
    have h1 : |w.re - z.re| ≤ dist w z := by
      rw [dist_eq_norm]; simpa using Complex.abs_re_le_norm (w - z)
    have h2 : |w.im - z.im| ≤ dist w z := by
      rw [dist_eq_norm]; simpa using Complex.abs_im_le_norm (w - z)
    obtain ⟨⟨hz1, hz2⟩, ⟨hz3, hz4⟩⟩ := hz
    rw [abs_le] at h1 h2
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hFc := E6.isCompact_flowImage hW hW0 T (swA6_isCompact_rectC _ _ _ _) hCH
  have hFH := E6.flowImage_subset_H hW hW0 T hCH
  obtain ⟨M₀, hM₀⟩ := hFc.isBounded.exists_norm_le
  obtain ⟨δ, hδ, hδF⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ E6.flowImage W T C, δ ≤ w.im := by
    rcases (E6.flowImage W T C).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨w₀, hw₀, hmin⟩ := hFc.exists_isMinOn hne Complex.continuous_im.continuousOn
      exact ⟨w₀.im, hFH hw₀, fun w hw => hmin hw⟩
  have hKH : K ⊆ H := fun z hz => show 0 < z.im from lt_of_lt_of_le (by exact_mod_cast hc) hz.2.1
  have hg := (RegUnif.continuousOn_log_deriv_fwdMapInv_joint hW hW0 T).mono
    (prod_mono (subset_refl (Icc (0 : ℝ) T)) hKH)
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod (swA6_isCompact_rectC _ _ _ _)).exists_bound_of_continuousOn
    hg
  obtain ⟨ρ, hρ0, hρlt⟩ := exists_rat_btwn (lt_min hc2 hδ)
  obtain ⟨M, hM⟩ := exists_rat_gt M₀
  obtain ⟨m, hm0, hmlt⟩ := exists_rat_btwn (Real.exp_pos (-B))
  refine ⟨ρ, M, m, hρ0, hm0, ?_⟩
  intro t ht
  have hthρ : thickening (ρ : ℝ) K ⊆ C :=
    (thickening_mono (hρlt.le.trans (min_le_left _ _)) K).trans hthick
  have hTH : thickening (ρ : ℝ) K ⊆ H := hthρ.trans hCH
  refine ⟨(RS.differentiableOn_fwdMapInv hW hW0 ht.1).mono hTH,
    (RS.injOn_fwdMapInv_H hW hW0 ht.1).mono hTH, fun z hz => ?_, fun z hz => ?_⟩
  · have hmem : fwdMapInv W t z ∈ E6.flowImage W T C := ⟨(t, z), ⟨ht, hthρ hz⟩, rfl⟩
    exact ⟨(hM₀ _ hmem).trans hM.le, (hρlt.le.trans (min_le_right _ _)).trans (hδF _ hmem)⟩
  · have hzH := hKH hz
    have hne : deriv (fwdMapInv W t) z ≠ 0 := by
      rw [RegCont.deriv_fwdMapInv_eq hW hW0 ht.1 hzH]
      exact QuantumZipper.deriv_revMap_ne_zero _ (RegCont.continuous_vRev hW t) ht.1 hzH
    have hb := hB (t, z) ⟨ht, hz⟩
    rw [Real.norm_eq_abs, abs_le] at hb
    have hpos : 0 < ‖deriv (fwdMapInv W t) z‖ := norm_pos_iff.2 hne
    calc (m : ℝ) ≤ Real.exp (-B) := hmlt.le
      _ ≤ Real.exp (Real.log ‖deriv (fwdMapInv W t) z‖) := Real.exp_le_exp.2 hb.1
      _ = ‖deriv (fwdMapInv W t) z‖ := Real.exp_log hpos

end SWCore
end QuantumZipper
