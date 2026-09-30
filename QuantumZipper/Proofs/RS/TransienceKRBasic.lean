import QuantumZipper.Proofs.RS.BasePointPath
import QuantumZipper.Proofs.Loewner.RevMapExtension
import QuantumZipper.Proofs.Loewner.CaraR1
import QuantumZipper.Proofs.Loewner.ReverseHolo
import QuantumZipper.Proofs.Loewner.Algebra
import QuantumZipper.Proofs.Complex.KoebeCovering
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# EXT-RS node KR: the hull stays away from a real point (deterministic part)

Blueprint `blueprint/EXT_RS_BLUEPRINT.md` §4, node **KR**.

`kr_le_norm_sub`: if the real points `0 < y < x` are both alive at time `t` for the forward
flow driven by `W`, with forward solutions `u` (from `x`) and `v` (from `y`), then every point
`z` of the hull `K_t` satisfies `c₀ Υ ≤ ‖z - x‖`, where
`Υ = bpUpsPath u v t = (X - O) exp (∫₀ᵗ 2 / X_s²) = (g_t(x) - g_t(y)) / g_t'(x)` and
`c₀ = koebeCovConst = 1/48`.

## Source

Rohde–Schramm, *Basic properties of SLE*, Ann. of Math. 161 (2005), proof of Lemma 7.2, p. 32
of `literature/math_0106036.pdf` ("Koebe 1/4 applied to `g_t⁻¹`"). We follow that proof: with
`V s = W (t - s) - W t`, the map `g_t⁻¹` (centered) is the reverse map `revMap V t`; its Schwarz
reflection `revMapExt V t` is holomorphic and injective on the disk `ball X (X - O)`, maps
`X` to `x` with derivative `exp (∫₀ᵗ 2 / X_s²)`, and maps the upper half of the disk into
`ℍ \ K_t`. Koebe's covering theorem (with the non-sharp constant `1/48` of
`CA.Koebe.ball_subset_image_koebe`, recorded in DEVIATIONS for L-KOEBE) gives the claim.
-/

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ComplexConjugate

namespace QuantumZipper
namespace RS

/-- A forward solution started at a real point, read backwards in time, is a real solution of
the reverse flow driven by the time-reversed increment. -/
theorem kr_isRealRevSol_timeRev {W : ℝ → ℝ} (hW : Continuous W) {x t : ℝ} (ht : 0 ≤ t)
    {u : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) t u) :
    IsRealRevSol (fun s => W (t - s) - W t) (u t).re t (fun s => (u (t - s)).re) := by
  have hre : ∀ s ∈ Icc (0 : ℝ) t, u s = ((u s).re : ℂ) := fun s hs =>
    Complex.ext (by simp) (by simp [im_isForwardSol_real hW ht hu s hs])
  have hmaps : MapsTo (fun s => t - s) (Icc 0 t) (Icc 0 t) :=
    fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  refine ⟨Complex.continuous_re.comp_continuousOn
    (hu.1.comp (continuousOn_const.sub continuousOn_id) hmaps), fun s hs => ⟨?_, ?_⟩⟩
  · intro h0
    apply (hu.2 _ (hmaps hs)).1
    rw [hre _ (hmaps hs)]
    simp only at h0
    rw [h0, Complex.ofReal_zero]
  · have h := LoewnerAlgebra.timeRev_eq (A := W) (a := (x : ℂ)) (c := 1) hu.1
      (fun r hr => (hu.2 r hr).1) (fun r hr => by rw [one_mul]; exact (hu.2 r hr).2) hs
    have hint : (∫ r in (0 : ℝ)..s, (2 : ℂ) / u (t - r)) =
        ((∫ r in (0 : ℝ)..s, 2 / (u (t - r)).re : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hs.1] at hr
      have hr' : t - r ∈ Icc (0 : ℝ) t := hmaps ⟨hr.1, hr.2.trans hs.2⟩
      conv_lhs => rw [hre _ hr']
      push_cast; rfl
    rw [hint, one_mul] at h
    show (u (t - s)).re = (u t).re - (W (t - s) - W t) - ∫ r in (0 : ℝ)..s, 2 / (u (t - r)).re
    rw [h]
    simp

/-- **KR** (Rohde–Schramm, *Basic properties of SLE*, proof of Lemma 7.2, p. 32: Koebe 1/4
applied to `g_t⁻¹`). -/
theorem kr_le_norm_sub {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {x y t : ℝ}
    (hy : 0 < y) (hyx : y < x) (ht : 0 ≤ t) {u v : ℝ → ℂ}
    (hu : IsForwardSol W (x : ℂ) t u) (hv : IsForwardSol W (y : ℂ) t v)
    {z : ℂ} (hz : z ∈ fwdHull W t) :
    CA.Koebe.koebeCovConst * bpUpsPath u v t ≤ ‖z - x‖ := by
  classical
  set V : ℝ → ℝ := fun s => W (t - s) - W t with hVdef
  have hV : Continuous V := (hW.comp (continuous_const.sub continuous_id)).sub continuous_const
  have hV0 : V 0 = 0 := by simp [hVdef]
  have hVV : (fun s => V (t - s) - V t) = W := by
    funext s; simp only [hVdef, sub_sub_cancel, sub_self, hW0]; ring
  have hzH : 0 < z.im := hz.1
  rcases ht.eq_or_lt with rfl | htpos
  · exfalso
    obtain ⟨S, hS, w, hw⟩ := exists_isForwardSol_small hW hzH
    exact LoewnerAlgebra.not_mem_fwdHull_of_sol le_rfl hS ⟨w, hw⟩ hz
  have ha : IsRealRevSol V (u t).re t (fun s => (u (t - s)).re) :=
    kr_isRealRevSol_timeRev hW ht hu
  have hb : IsRealRevSol V (v t).re t (fun s => (v (t - s)).re) :=
    kr_isRealRevSol_timeRev hW ht hv
  set X := (u t).re with hX
  set O := (v t).re with hO
  set a : ℝ → ℝ := fun s => (u (t - s)).re with ha_def
  set b : ℝ → ℝ := fun s => (v (t - s)).re with hb_def
  have hat : a t = x := by
    simp only [ha_def, sub_self]
    rw [(hu.2 0 ⟨le_rfl, ht⟩).2]; simp [hW0]
  have hbt : b t = y := by
    simp only [hb_def, sub_self]
    rw [(hv.2 0 ⟨le_rfl, ht⟩).2]; simp [hW0]
  have hb0 : b 0 = O := by show (v (t - 0)).re = (v t).re; rw [sub_zero]
  have hOpos : 0 < O := by
    rw [← hb0]
    by_contra hneg
    push Not at hneg
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc ht hb.1
      (show (0 : ℝ) ∈ Icc (b 0) (b t) from ⟨hneg, by rw [hbt]; exact hy.le⟩)
    exact (hb.2 s hs).1 hs0
  have hOX : O < X := by
    rcases lt_trichotomy X O with h | h | h
    · have := RealLine.isRealRevSol_lt hV ht ha hb h
      rw [hat, hbt] at this; linarith
    · have hb' : IsRealRevSol V X t b := by rw [h]; exact hb
      have := RealLine.isRealRevSol_unique hV ht ha hb' ⟨ht, le_rfl⟩
      rw [hat, hbt] at this; linarith
    · exact h
  have hV0O : V 0 < O := by rw [hV0]; exact hOpos
  have hsol : ∀ p : ℝ, O < p → ∃ w, IsRealRevSol V p t w := fun p hp =>
    CaraR.not_mem_swallowedSet_iff.1 (CaraR.not_mem_swallowedSet_of_le hV ht hV0O hp.le
      (CaraR.not_mem_swallowedSet_iff.2 ⟨b, hb⟩))
  have hJ : ∀ p ∈ Ioi O, ENNReal.ofReal t < realHitTime V p := fun p hp =>
    CaraR.ofReal_lt_realHitTime_of_pos hV ht (hV0O.trans hp)
      (CaraR.not_mem_swallowedSet_iff.2 (hsol p hp))
  obtain ⟨U, hUo, hUJ, -, hUd, hUH, hconj, hUreal, hUderiv, -⟩ :=
    RevMapExtension.exists_revMapExt_extension hV ht (Ioi O) hJ
  set f := RevMapExtension.revMapExt V t with hf
  set r := X - O with hr
  -- real points of the disk lie to the right of `O`
  have hre_of : ∀ w ∈ ball (X : ℂ) r, O < w.re := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    have := Complex.abs_re_le_norm (w - X)
    rw [Complex.sub_re, Complex.ofReal_re] at this
    linarith [neg_abs_le (w.re - X)]
  have him_pos : ∀ w : ℂ, 0 < w.im → 0 < (f w).im := fun w hw => by
    rw [hUH w hw]; exact lt_of_lt_of_le hw (im_le_im_revMap V hV w hw ht)
  have him_neg : ∀ w : ℂ, w.im < 0 → (f w).im < 0 := fun w hw => by
    have := him_pos (conj w) (by rw [Complex.conj_im]; linarith)
    rw [hconj, Complex.conj_im] at this; linarith
  have him_zero : ∀ w ∈ ball (X : ℂ) r, w.im = 0 → f w = (realRevMap V t w.re : ℂ) := by
    intro w hw h0
    have hw' : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [h0])
    rw [hw', hUreal _ (hre_of w hw), Complex.ofReal_re]
  have hdiffH : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℂ f w := fun w hw =>
    (hasDerivAt_revMap V hV ht hw).differentiableAt.congr_of_eventuallyEq (by
      filter_upwards [(Complex.continuous_im.isOpen_preimage _ isOpen_Ioi).mem_nhds hw]
        with q hq using hUH q hq)
  have hd : DifferentiableOn ℂ f (ball (X : ℂ) r) := by
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    rcases lt_trichotomy w.im 0 with h | h | h
    · have e : f = conj ∘ f ∘ conj := funext fun q => by
        simp only [Function.comp, hconj, Complex.conj_conj]
      rw [e]
      exact differentiableAt_conj_conj_iff.2 (hdiffH _ (by rw [Complex.conj_im]; linarith))
    · have hw' : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [h])
      have hwU : w ∈ U := by rw [hw']; exact hUJ _ (hre_of w hw)
      exact (hUd w hwU).differentiableAt (hUo.mem_nhds hwU)
    · exact hdiffH w h
  have hinjH : ∀ w₁ w₂ : ℂ, 0 < w₁.im → 0 < w₂.im → f w₁ = f w₂ → w₁ = w₂ := by
    intro w₁ w₂ h1 h2 heq
    rw [hUH _ h1, hUH _ h2] at heq
    exact injOn_revMap V hV ht h1 h2 heq
  have hinj : InjOn f (ball (X : ℂ) r) := by
    intro w₁ hw₁ w₂ hw₂ heq
    have eim := congrArg Complex.im heq
    rcases lt_trichotomy w₁.im 0 with h1 | h1 | h1 <;>
      rcases lt_trichotomy w₂.im 0 with h2 | h2 | h2
    · have := hinjH (conj w₁) (conj w₂) (by rw [Complex.conj_im]; linarith)
        (by rw [Complex.conj_im]; linarith) (by rw [hconj, hconj, heq])
      simpa using congrArg conj this
    · rw [him_zero w₂ hw₂ h2, Complex.ofReal_im] at eim; linarith [him_neg w₁ h1]
    · linarith [him_neg w₁ h1, him_pos w₂ h2]
    · rw [him_zero w₁ hw₁ h1, Complex.ofReal_im] at eim; linarith [him_neg w₂ h2]
    · rw [him_zero w₁ hw₁ h1, him_zero w₂ hw₂ h2] at heq
      have hre := (RealLine.strictMonoOn_realRevMap hV ht).injOn (hsol _ (hre_of w₁ hw₁))
        (hsol _ (hre_of w₂ hw₂)) (Complex.ofReal_injective heq)
      exact Complex.ext hre (h1.trans h2.symm)
    · rw [him_zero w₁ hw₁ h1, Complex.ofReal_im] at eim; linarith [him_pos w₂ h2]
    · linarith [him_pos w₁ h1, him_neg w₂ h2]
    · rw [him_zero w₂ hw₂ h2, Complex.ofReal_im] at eim; linarith [him_pos w₁ h1]
    · exact hinjH w₁ w₂ h1 h2 heq
  have hXJ : X ∈ Ioi O := hOX
  have hfX : f X = x := by
    rw [hUreal X hXJ, RealLine.realRevMap_eq hV ha ht le_rfl]
    show ((a t : ℝ) : ℂ) = x
    rw [hat]
  have hint : (∫ s in (0 : ℝ)..t, 2 / (realRevMap V s X) ^ 2) =
      ∫ s in (0 : ℝ)..t, 2 / (u s).re ^ 2 := by
    have e1 : (∫ s in (0 : ℝ)..t, 2 / (realRevMap V s X) ^ 2) =
        ∫ s in (0 : ℝ)..t, (fun q => 2 / (u q).re ^ 2) (t - s) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le ht] at hs
      simp only [RealLine.realRevMap_eq hV ha hs.1 hs.2, ha_def]
    rw [e1, intervalIntegral.integral_comp_sub_left (fun q => 2 / (u q).re ^ 2) t, sub_self,
      sub_zero]
  have hderX : ‖deriv f X‖ = Real.exp (∫ s in (0 : ℝ)..t, 2 / (u s).re ^ 2) := by
    rw [hUderiv X hXJ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hint]
  have hK := CA.Koebe.ball_subset_image_koebe hd hinj
  rw [hfX, hderX] at hK
  have hUps : bpUpsPath u v t = r * Real.exp (∫ s in (0 : ℝ)..t, 2 / (u s).re ^ 2) := rfl
  by_contra hlt
  push Not at hlt
  have hzb : z ∈ ball (x : ℂ) (CA.Koebe.koebeCovConst * r *
      Real.exp (∫ s in (0 : ℝ)..t, 2 / (u s).re ^ 2)) := by
    rw [mem_ball, dist_eq_norm, mul_assoc, ← hUps]; exact hlt
  obtain ⟨w, hw, hwz⟩ := hK hzb
  have hwH : 0 < w.im := by
    rcases lt_trichotomy w.im 0 with h | h | h
    · have := him_neg w h; rw [hwz] at this; linarith
    · have := congrArg Complex.im (him_zero w hw h)
      rw [hwz, Complex.ofReal_im] at this; linarith
    · exact h
  have hnot := (LoewnerAlgebra.fwdMap_revMap_timeRev V hV hV0 htpos hwH).1
  rw [hVV, ← hUH w hwH, hwz] at hnot
  exact hnot hz

end RS
end QuantumZipper
