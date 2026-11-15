/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.FanTipFiber
import InteractingSLE.Spec.Sec7.R6FcTrace
import InteractingSLE.WangWu.ReverseContactBdry

/-!
# The singleton current tip supplies physical local agreement

PROVE-R6-TWO, following Astra's R.6 note, §§4.1–4.2 (ruling R98).
Only the current tip has a singleton fibre. No injectivity is asserted
at an exposed landing or at a seed corner. Bounded displacement replaces
the compactification at infinity in the compactness argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Sec7.R6Tr

/-- Compactness localizes the entire inverse image of a singleton fibre.
The displacement bound controls coordinates at infinity. -/
theorem exists_ball_preimage_of_singleton {F : ℂ → ℂ}
    (hF : ContinuousOn F Hbar) {B : ℝ}
    (hB : ∀ z ∈ Hbar, ‖F z - z‖ ≤ B) {p : ℂ}
    (hfibre : ∀ z ∈ Hbar, F z = p → z = 0) {r : ℝ} (hr : 0 < r) :
    ∃ ε > 0, ∀ z ∈ Hbar, F z ∈ ball p ε → z ∈ ball (0 : ℂ) r := by
  let R := ‖p‖ + 1 + B
  let K := (Hbar ∩ closedBall (0 : ℂ) R) ∩ (ball (0 : ℂ) r)ᶜ
  have hHc : IsClosed Hbar := by rw [← closure_H]; exact isClosed_closure
  have hK : IsCompact K :=
    ((isCompact_closedBall (0 : ℂ) R).inter_left hHc).inter_right isOpen_ball.isClosed_compl
  have hFK : IsClosed (F '' K) := (hK.image_of_continuousOn (hF.mono fun _ hz => hz.1.1)).isClosed
  have hp : p ∉ F '' K := by
    rintro ⟨z, hz, hzp⟩
    have hz0 := hfibre z hz.1.1 hzp
    exact hz.2 (hz0 ▸ mem_ball_self hr)
  obtain ⟨ε, hε, hεK⟩ := Metric.isOpen_iff.1 hFK.isOpen_compl p hp
  refine ⟨min ε 1, lt_min hε zero_lt_one, fun z hz hzp => ?_⟩
  by_contra hzr
  have hdist : dist (F z) p < 1 := (mem_ball.1 hzp).trans_le (min_le_right _ _)
  have hnorm : ‖z‖ ≤ R := by
    have h1 := norm_le_norm_add_norm_sub' z (F z)
    have h2 := norm_le_norm_add_norm_sub' (F z) p
    rw [norm_sub_rev z (F z)] at h1
    rw [dist_eq_norm] at hdist
    have hb := hB z hz
    dsimp [R]
    linarith
  have hzK : z ∈ K := ⟨⟨hz, by simpa only [mem_closedBall, dist_zero_right] using hnorm⟩, hzr⟩
  exact hεK (ball_subset_ball (min_le_left _ _) hzp) ⟨z, hzK, rfl⟩

/-- Aux. 136's real-boundary statement is the full closed-half-plane
singleton statement: interior points map to the active domain, whereas
the current tip does not. -/
theorem singletonTipFiber_full {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) (hs : IsSingletonTipFiber W t) :
    ∀ z ∈ Hbar, extendFrom H (fwdMapInv W t) z = η t → z = 0 := by
  intro z hz hzp
  rcases (show (0 : ℝ) ≤ z.im from hz).eq_or_lt with hzi | hzH
  · have hzreal : (z.re : ℂ) = z := Complex.ext (by simp) (by simp [← hzi])
    have hzero : z.re = 0 := hs z.re (by
      rw [hzreal, hzp, hη.loewnerTip_eq hW hW0 ht])
    rw [← hzreal, hzero, Complex.ofReal_zero]
  · have hzactive := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ht hzH
    have htip := hη.extendFrom_not_mem hW hW0 ht (x := 0) (by simp)
    have htipEq : extendFrom H (fwdMapInv W t) (0 : ℂ) = η t := by
      simpa only [loewnerTip, Complex.ofReal_zero] using hη.loewnerTip_eq hW hW0 ht
    rw [htipEq] at htip
    rw [extendFrom_H_eq (continuousOn_fwdMapInv hW hW0 ht) hzH] at hzp
    exact False.elim (htip (hzp ▸ hzactive))

/-- Every physical approach to the current tip has centered ambient
coordinate tending to zero, on the singleton-tip event of Aux. 136. -/
theorem exists_tip_ball_preimage {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) (hs : IsSingletonTipFiber W t) {r : ℝ} (hr : 0 < r) :
    ∃ ε > 0, ∀ z ∈ Hbar,
      extendFrom H (fwdMapInv W t) z ∈ ball (η t) ε → z ∈ ball (0 : ℂ) r := by
  obtain ⟨M, -, hM⟩ := exists_abs_le_of_continuous hW t
  exact exists_ball_preimage_of_singleton (hη.hasBdryLimits hW hW0 ht).continuousOn
    (fun z hz => WangWu.norm_extendFrom_sub_le hη hW hW0 ht hM hz)
    (singletonTipFiber_full hη hW hW0 ht hs) hr

/-- Astra Lemma 4.1 in the ambient Loewner chart. A driver collar in
the selected inner face gives a physical ball, for every active access
to the current tip. -/
theorem local_inclusion_of_tip_collar {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) (hs : IsSingletonTipFiber W t) {D : Set ℂ}
    {r : ℝ} (hr : 0 < r) (hcollar : H ∩ ball (0 : ℂ) r ⊆ (fwdMapInv W t) ⁻¹' D) :
    ∃ ε > 0, (H \ fwdHull W t) ∩ ball (η t) ε ⊆ D := by
  obtain ⟨ε, hε, hpre⟩ := exists_tip_ball_preimage hη hW hW0 ht hs hr
  refine ⟨ε, hε, fun w hw => ?_⟩
  let z := fwdMap W t w
  have hz : z ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht hw.1
  have hzw : fwdMapInv W t z = w := QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 ht hw.1
  have hzball : z ∈ ball (0 : ℂ) r := hpre z (QuantumZipper.H_subset_Hbar hz) (by
    rw [extendFrom_H_eq (continuousOn_fwdMapInv hW hW0 ht) hz, hzw]
    exact hw.2)
  simpa only [mem_preimage, hzw] using hcollar ⟨hz, hzball⟩

end InteractingSLE.Sec7.R6Tr
