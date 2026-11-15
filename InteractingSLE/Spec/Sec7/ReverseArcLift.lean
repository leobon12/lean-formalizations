/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux57
import InteractingSLE.Spec.Sec2.MartingaleLaurent
import InteractingSLE.Foundations.Loewner.ConformalImageFull

/-!
# The derivative-argument lift of a Loewner chart, and Aux. lemma 57 along a filter

Packet PROVE-LEMMA76B (specification §7.2, proof of Aux. lemma 70, p. 275: "Aux. lemma 57 gives argument lift zero for
the derivative of each such transition map, with normalization inherited from infinity").

* `isCanonicalDerivLog_logDerivFwd`: the canonical branch `logDerivFwd W t = −∫₀ᵗ 2/f_s²` of the frozen coupling mean is
  the canonical logarithm (`Restart.IsCanonicalDerivLog`) of `g_t′` for `g_t = f_t + W_t` (high up both are small:
  `norm_logDerivFwd_add_le`);
* `isCanonicalDerivLog_translate`, `isMapOut_translate`: the same for the chart of a trace from a real seed `x`,
  `z ↦ f_t(z − x) + W_t + x`, whose hull is `x + K_t`;
* `tendsto_im_sub_of_le`: Aux. lemma 57 for chart transitions (`tendsto_im_sub_canonDerivLog`) along any filter
  `F ≤ 𝓟 (ℍ \ B)` on which the smaller chart tends to an untouched real point.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped Real

open QuantumZipper (H)

namespace InteractingSLE

namespace Sec7

open Restart

namespace ReverseArc

/-- **The canonical branch of a Loewner chart** is the canonical logarithm of the derivative of `g_t = f_t + W_t`. -/
theorem isCanonicalDerivLog_logDerivFwd {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    IsCanonicalDerivLog (QuantumZipper.fwdHull W t) (fun z => QuantumZipper.fwdMap W t z + W t)
      (QuantumZipper.logDerivFwd W t) := by
  have hO : IsOpen (H \ QuantumZipper.fwdHull W t) := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW ht
  have hderiv : ∀ z ∈ H \ QuantumZipper.fwdHull W t,
      deriv (fun z => QuantumZipper.fwdMap W t z + W t) z = deriv (QuantumZipper.fwdMap W t) z := fun z _ =>
    deriv_add_const _
  obtain ⟨hdiff, hexp⟩ := isDerivLog_fwdMap hW ht
  refine ⟨⟨hdiff, fun z hz => by rw [hexp z hz, hderiv z hz]⟩, ?_⟩
  -- a bound on the driver
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn hW.continuousOn
  have hK' : ∀ r ∈ Icc (0 : ℝ) t, |W r| ≤ |K| := fun r hr => by
    have := hK r hr; rw [Real.norm_eq_abs] at this; exact this.trans (le_abs_self K)
  set D := 24 * |K| + 8 * Real.sqrt t with hD
  have hD0 : 0 ≤ D := by positivity
  obtain ⟨R, hR, hKR⟩ := (isHPHull_fwdHull hW ht).2.1.subset_ball_lt 0 0
  set Y := R + 2 * D + 4 * t + 96 * D * t + 2 with hY
  refine ⟨Y, fun w hw => ?_⟩
  have hwim : 0 < w.im := by
    have : 0 ≤ R + 2 * D + 4 * t + 96 * D * t := by positivity
    linarith
  have hnw : w.im ≤ ‖w‖ := (le_abs_self _).trans (abs_im_le_norm w)
  have hwK : w ∈ H \ QuantumZipper.fwdHull W t := by
    refine ⟨hwim, fun h => ?_⟩
    have := mem_ball_zero_iff.1 (hKR h)
    have : 0 ≤ 2 * D + 4 * t + 96 * D * t := by positivity
    linarith
  have hbig : 2 * D ≤ ‖w‖ := by
    have : 0 ≤ R + 4 * t + 96 * D * t := by positivity
    linarith
  have hb := MartChar.norm_logDerivFwd_add_le hW hW0 ht hK' hwK hbig
  have hw1 : 1 ≤ ‖w‖ := by
    have : 0 ≤ R + 2 * D + 4 * t + 96 * D * t := by positivity
    linarith
  have hnpos : 0 < ‖w‖ := by linarith
  -- `|log f_t′(w)| < 1`
  have h2 : ‖2 * (t : ℂ) / w ^ 2‖ ≤ 1 / 2 := by
    have h2t : ‖(2 * (t : ℂ))‖ = 2 * t := by
      rw [show (2 * (t : ℂ)) = ((2 * t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
    rw [norm_div, norm_pow, h2t]
    rw [div_le_iff₀ (by positivity)]
    have h1 : ‖w‖ ≤ ‖w‖ ^ 2 := by nlinarith
    have : 4 * t + 2 ≤ ‖w‖ := by
      have : 0 ≤ R + 2 * D + 96 * D * t := by positivity
      linarith
    nlinarith
  have h3 : 24 * D * t / ‖w‖ ^ 3 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : ‖w‖ ≤ ‖w‖ ^ 3 := by
      have : 1 ≤ ‖w‖ ^ 2 := by nlinarith
      nlinarith
    have : 96 * D * t + 2 ≤ ‖w‖ := by
      have : 0 ≤ R + 2 * D + 4 * t := by positivity
      linarith
    nlinarith
  have hL : ‖QuantumZipper.logDerivFwd W t w‖ < 1 := by
    have := norm_sub_le (QuantumZipper.logDerivFwd W t w + 2 * t / w ^ 2) (2 * t / w ^ 2)
    rw [add_sub_cancel_right] at this
    have h4 : 24 * D * t / ‖w‖ ^ 3 = 24 * (24 * |K| + 8 * Real.sqrt t) * t / ‖w‖ ^ 3 := by rw [hD]
    linarith
  have hLim : |(QuantumZipper.logDerivFwd W t w).im| < 1 := (abs_im_le_norm _).trans_lt hL
  rw [hderiv w hwK, ← hexp w hwK, log_exp]
  · have := neg_abs_le (QuantumZipper.logDerivFwd W t w).im
    linarith [Real.pi_gt_three]
  · have := le_abs_self (QuantumZipper.logDerivFwd W t w).im
    linarith [Real.pi_gt_three]

/-! ### Translation to a real seed -/

theorem mem_image_add_iff (x : ℝ) (K : Set ℂ) (w : ℂ) :
    w ∈ (fun z => z + (x : ℂ)) '' K ↔ w - x ∈ K := by
  constructor
  · rintro ⟨z, hz, rfl⟩; simpa using hz
  · intro h; exact ⟨w - x, h, by ring⟩

theorem mem_H_diff_image_add_iff (x : ℝ) (K : Set ℂ) (w : ℂ) :
    w ∈ H \ (fun z => z + (x : ℂ)) '' K ↔ w - x ∈ H \ K := by
  rw [Set.mem_sdiff, Set.mem_sdiff, mem_image_add_iff]
  have : w - x ∈ H ↔ w ∈ H := by
    show 0 < (w - (x : ℂ)).im ↔ 0 < w.im
    simp
  rw [this]

/-- A mapping-out function, translated by a real `x`. -/
theorem isMapOut_translate {K : Set ℂ} {g : ℂ → ℂ} (hg : IsMapOut K g) (x : ℝ) :
    IsMapOut ((fun z => z + (x : ℂ)) '' K) (fun w => g (w - x) + x) := by
  have h := hg.comp_affHomeo (r := 1) (x := x) one_pos
  have himg : affHomeo 1 one_pos x '' K = (fun z => z + (x : ℂ)) '' K := by
    congr 1; funext z; exact ConformalImageFull.affHomeo_one_apply x z
  have hfun : (fun w => affHomeo 1 one_pos x (g ((affHomeo 1 one_pos x).symm w))) =
      fun w => g (w - x) + x := by
    funext w
    rw [ConformalImageFull.affHomeo_one_apply, ConformalImageFull.affHomeo_one_symm_apply]
  rwa [himg, hfun] at h

/-- A canonical logarithm, translated by a real `x`. -/
theorem isCanonicalDerivLog_translate {K : Set ℂ} {g L : ℂ → ℂ} (hL : IsCanonicalDerivLog K g L) (x : ℝ) :
    IsCanonicalDerivLog ((fun z => z + (x : ℂ)) '' K) (fun w => g (w - x) + x) (fun w => L (w - x)) := by
  obtain ⟨⟨hd, he⟩, Y, hY⟩ := hL
  have hderiv : ∀ w, deriv (fun w => g (w - x) + x) w = deriv g (w - x) := fun w => by
    rw [deriv_add_const, deriv_comp_sub_const]
  refine ⟨⟨?_, fun w hw => ?_⟩, Y, fun w hw => ?_⟩
  · intro w hw
    have hw' := (mem_H_diff_image_add_iff x K w).1 hw
    exact (hd _ hw').comp w (differentiableWithinAt_id.sub_const _)
      (fun v hv => (mem_H_diff_image_add_iff x K v).1 hv)
  · rw [hderiv, he _ ((mem_H_diff_image_add_iff x K w).1 hw)]
  · show L (w - x) = _
    rw [hderiv, hY _ (by simpa using hw)]

/-! ### Aux. lemma 57 along a filter -/

/-- **Aux. lemma 57 for chart transitions, along a filter** (the filter form of `tendsto_im_sub_canonDerivLog`): if
`F ≤ 𝓟 (ℍ \ B)` and the chart `g` of `A ⊆ B` tends along `F` to a real point `u` whose ball avoids the transition hull
`g(B \ A)`, the two canonical lifts agree in the limit along `F`. -/
theorem tendsto_im_sub_of_le {A B : Set ℂ} {g : ℂ → ℂ} (hA : IsHPHull A) (hB : IsHPHull B) (hAB : A ⊆ B)
    (hg : IsMapOut A g) {gB LA LB : ℂ → ℂ} (hgB : IsMapOut B gB) (hLA : IsCanonicalDerivLog A g LA)
    (hLB : IsCanonicalDerivLog B gB LB) {F : Filter ℂ} (hF : F ≤ 𝓟 (H \ B)) {u ρ : ℝ} (hρ : 0 < ρ)
    (hd : Disjoint (ball (u : ℂ) ρ) (g '' (B \ A))) (hq : Tendsto g F (𝓝[H] (u : ℂ))) :
    Tendsto (fun z => (LB z).im - (LA z).im) F (𝓝 0) := by
  set C := g '' (B \ A) with hCdef
  have hC : IsHPHull C := hg.isHPHull_image hA hB hAB
  set gC := ConformalImage.mapOut C with hgCdef
  have hgC : IsMapOut C gC := ConformalImage.isMapOut_mapOut hC
  obtain ⟨LC, hLC⟩ := exists_isCanonicalDerivLog hC hgC
  have hcomp := IsCanonicalDerivLog.comp hA hB hAB hg hgC hLA hLC
  have hgB' : IsMapOut B (gC ∘ g) := hg.comp hA hB hAB hgC
  have heq : EqOn LB (fun z => LC (g z) + LA z) (H \ B) :=
    IsCanonicalDerivLog.eqOn (hLB.congr hB (hgB.eqOn hB hgB')) hcomp hB hgB'
  have hlim := (IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero hC hLC hgC hρ hd).comp hq
  refine hlim.congr' ?_
  filter_upwards [hF (mem_principal_self _)] with z hz
  simp only [Function.comp_apply, heq hz, add_im, add_sub_cancel_right]

end ReverseArc

end Sec7

end InteractingSLE
