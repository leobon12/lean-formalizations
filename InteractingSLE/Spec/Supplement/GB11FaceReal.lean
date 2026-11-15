/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11FaceDomain
import InteractingSLE.Foundations.Loewner.ConformalImageFullRate

/-!
# GB11: the forward chart at an unvisited real contact

The full Schwarz-reflection package already in the library gives a simple local
chart at every original-real point outside the old hull closure. This adapter also
proves that its values on the real diameter invert the continuous ambient inverse.
Thus a wall touching the original real line needs no interior-half-plane premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Theorem14.GB11Chart

/-- A continuous, injective forward chart across an unvisited original-real contact,
with inverse identity on the entire closed upper half of its neighborhood. -/
theorem exists_local_chart_at_real {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) {y : ℝ} (hy : (y : ℂ) ∉ closure (fwdHull W t)) :
    ∃ ρ > 0, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball (y : ℂ) ρ) ∧
      InjOn G (ball (y : ℂ) ρ) ∧ EqOn G (fwdMap W t) (ball (y : ℂ) ρ ∩ H) ∧
      MapsTo G (ball (y : ℂ) ρ ∩ Hbar) Hbar ∧
      (∀ z ∈ ball (y : ℂ) ρ, z.im = 0 → (G z).im = 0) ∧
      ∀ z ∈ ball (y : ℂ) ρ ∩ Hbar, trMap W 0 t (G z) = z := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hy
  have hd : Disjoint (ball (y : ℂ) r) (fwdHull W t) :=
    disjoint_left.2 (fun z hz hK => hball hz (subset_closure hK))
  have hK := isHPHull_fwdHull hW ht
  have hg := isMapOut_fwdMap hW hW0 ht
  obtain ⟨G, hGd, hGeq, -, -, -, hGi, hGup, -, hGreal⟩ :=
    ConformalImageFull.IsMapOut.exists_reflection_full hK hg hr hd
  set F : ℂ → ℂ := fun z => G z - W t
  have hFd : DifferentiableOn ℂ F (ball (y : ℂ) (r / 2)) :=
    hGd.sub_const _
  have hFeq : EqOn F (fwdMap W t) (ball (y : ℂ) (r / 2) ∩ H) := by
    intro z hz
    change G z - (W t : ℂ) = fwdMap W t z
    rw [hGeq hz]
    exact add_sub_cancel_right _ _
  have hFr : ∀ z ∈ ball (y : ℂ) (r / 2), z.im = 0 → (F z).im = 0 := by
    intro z hz him
    change (G z - (W t : ℂ)).im = 0
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero, hGreal z hz him]
  have hFH : MapsTo F (ball (y : ℂ) (r / 2) ∩ Hbar) Hbar := by
    intro z hz
    change 0 ≤ (G z - (W t : ℂ)).im
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero]
    rcases lt_or_eq_of_le (show (0 : ℝ) ≤ z.im from hz.2) with him | him
    · exact (hGup z hz.1 him).le
    · exact (hGreal z hz.1 him.symm).ge
  refine ⟨r / 2, half_pos hr, F, hFd, ?_, hFeq, hFH, hFr, ?_⟩
  · intro z hz w hw he
    exact hGi hz hw (sub_left_inj.1 he)
  · intro z hz
    set S := ball (y : ℂ) (r / 2) ∩ H
    have hzcl : z ∈ closure S := subset_closure_ball_inter_H _ _ hz
    have : (𝓝[S] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hzcl
    have htc := YuanSimpleApprox.trMap_continuousOn hη hW hW0 (a := 0) le_rfl ht
    have hfc : ContinuousWithinAt F S z := (hFd.continuousOn z hz.1).mono inter_subset_left
    have hc : ContinuousWithinAt (fun w => trMap W 0 t (F w)) S z :=
      (htc _ (hFH hz)).comp hfc (fun w hw => hFH ⟨hw.1, H_subset_Hbar hw.2⟩)
    have he : ∀ w ∈ S, trMap W 0 t (F w) = w := by
      intro w hw
      rw [hFeq hw]
      exact Sec6.trMap_zero_fwdMap hW hW0 ht ⟨hw.2,
        fun hwK => hd.le_bot ⟨by
          exact ball_subset_ball (show r / 2 ≤ r by linarith) hw.1, hwK⟩⟩
    exact tendsto_nhds_unique (hc.tendsto.congr'
      (eventually_nhdsWithin_of_forall he)) (tendsto_id.mono_left nhdsWithin_le_nhds)

end InteractingSLE.Theorem14.GB11Chart
