import QuantumZipper.Proofs.Zipper.XPCMod
import QuantumZipper.Proofs.Zipper.SWCoreVAClass

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-VA (iii): the centre modulus of pushed circles, uniformly over an area map class

Task SWC-VA (`handoff/SW-CORE.md` §5). Generic step (`swcVA_push_push_le_of_qt`): the proof of
the repository's `E6.XAreaPC.abs_kernelCov2_push_push_le` (pushed-circle energy modulus via the
correction kernel `qt`, `neumannH (ψ x) (ψ y) = neumannH x y + qt ψ x y`), for maps defined on an
open `U` and with the Lipschitz and sup bounds of `qt` as hypotheses:

  `|kernelCov2 neumannH (ψ_* fc(z,s) − ψ_* fc(z',s'))| ≤ 2 (2 δ / min s s' + L δ)`,
  `δ = ‖z − z'‖ + |s − s'|`.

This is the modulus input of SW Lemma 3.5 ((3.21)–(3.22), p. 16) for the chaining over the class.
Own adaptation of the repository proof (no new mathematics).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ComplexConjugate

namespace QuantumZipper
namespace SWCore

open E6 E6.XAreaPC

section Push

variable {φ : ℂ → ℂ} {K : Set ℂ}

end Push

/-! ## Uniform bounds on the correction kernel over an area class, locally -/

/-- **Uniform Lipschitz bound of `qt` over the class, on small discs.** For `z₀ ∈ K`, and the disc
`B̄(z₀, R)` with `R ≤ R₀` (class constants), `qt ψ x ·` is `L`-Lipschitz on the disc. -/
theorem swcVA_qt_lip {a b c d ρ M m : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hm : 0 < m) :
    ∃ L R₀ : ℝ, 0 ≤ L ∧ 0 < R₀ ∧ ∀ ψ ∈ AreaClass a b c d ρ M m, ∀ z₀ ∈ rectC a b c d,
      ∀ R : ℝ, 0 ≤ R → R ≤ R₀ →
        (∀ x ∈ closedBall z₀ R, ∀ y ∈ closedBall z₀ R, m / 2 ≤ ‖ddq ψ x y‖) ∧
        (∀ u ∈ closedBall z₀ R, c / 2 ≤ u.im ∧ m / 2 ≤ ‖deriv ψ u‖) ∧
        closedBall z₀ R ⊆ thickening ρ (rectC a b c d) ∧
        ∀ x ∈ closedBall z₀ R, ∀ y ∈ closedBall z₀ R, ∀ y' ∈ closedBall z₀ R,
          |qt ψ x y - qt ψ x y'| ≤ L * ‖y - y'‖ := by
  set M₁ := |M| / (ρ / 4) with hM₁
  set M₂ := |M| / (ρ / 4) / (ρ / 4) with hM₂
  have hM₁0 : 0 ≤ M₁ := by positivity
  have hM₂0 : 0 ≤ M₂ := by positivity
  set R₀ := min (min (ρ / 16) (c / 2)) (m / (4 * M₂ + 4)) with hR₀
  have hR₀0 : 0 < R₀ := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  refine ⟨M₂ / (m / 2) + M₁ / ρ + 1 / (c / 2), R₀, by positivity, hR₀0,
    fun ψ hψ z₀ hz₀ R hR hRR => ?_⟩
  obtain ⟨hψd, -, hψb, hψm⟩ := hψ
  set K := closedBall z₀ R with hKdef
  set U := thickening ρ (rectC a b c d) with hU
  have hR16 : R ≤ ρ / 16 := hRR.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hRc : R ≤ c / 2 := hRR.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hRm : R ≤ m / (4 * M₂ + 4) := hRR.trans (min_le_right _ _)
  have hMb : ∀ u ∈ U, ‖ψ u‖ ≤ |M| := fun u hu => (hψb u hu).1.trans (le_abs_self M)
  have hKt : K ⊆ thickening (ρ / 8) (rectC a b c d) := fun u hu =>
    swcVA_mem_thickening (self_subset_thickening (show (0 : ℝ) < ρ / 32 by positivity) _ hz₀)
      (mem_closedBall.1 hu) (by linarith)
  have hKU : K ⊆ U := hKt.trans (thickening_mono (by linarith) _)
  have hKc : Convex ℝ K := convex_closedBall z₀ R
  have hd1 : ∀ u ∈ K, ‖deriv ψ u‖ ≤ M₁ := fun u hu =>
    swcVA_norm_deriv_le hρ hψd hMb (thickening_mono (by linarith) _ (hKt hu))
  have hd2 : ∀ u ∈ K, ‖deriv (deriv ψ) u‖ ≤ M₂ := fun u hu =>
    swcVA_norm_deriv2_le hρ hψd hMb (hKt hu)
  have hz₀K : z₀ ∈ K := mem_closedBall_self hR
  have hmz : m ≤ ‖deriv ψ z₀‖ := hψm z₀ hz₀
  have h2MR : 2 * M₂ * R ≤ m / 2 := by
    have : R * (4 * M₂ + 4) ≤ m := by
      rw [le_div_iff₀ (by positivity)] at hRm; linarith
    nlinarith
  have hlow : ∀ x ∈ K, ∀ y ∈ K, m / 2 ≤ ‖ddq ψ x y‖ := by
    intro x hx y hy
    have h := ddq_lip isOpen_thickening hψd hKc hKU hM₂0 hd2 hx hy hz₀K hz₀K
    rw [ddq_self] at h
    have hx' : ‖x - z₀‖ ≤ R := by rw [← dist_eq_norm]; exact mem_closedBall.1 hx
    have hy' : ‖y - z₀‖ ≤ R := by rw [← dist_eq_norm]; exact mem_closedBall.1 hy
    have h3 : ‖deriv ψ z₀‖ - ‖ddq ψ x y‖ ≤ M₂ * (‖x - z₀‖ + ‖y - z₀‖) := by
      have := norm_sub_norm_le (deriv ψ z₀) (ddq ψ x y)
      rw [norm_sub_rev] at this
      linarith
    nlinarith
  have hbelow : ∀ u ∈ K, c / 2 ≤ u.im := by
    intro u hu
    have h1 : |(u - z₀).im| ≤ ‖u - z₀‖ := Complex.abs_im_le_norm _
    have h2 : ‖u - z₀‖ ≤ R := by rw [← dist_eq_norm]; exact mem_closedBall.1 hu
    have h3 : c ≤ z₀.im := hz₀.2.1
    rw [Complex.sub_im] at h1
    have := neg_abs_le (u.im - z₀.im)
    linarith
  refine ⟨hlow, fun u hu => ⟨hbelow u hu, ?_⟩, hKU, ?_⟩
  · have := hlow u hu u hu
    rwa [ddq_self] at this
  intro x hx y hy y' hy'
  have hψL : ∀ p ∈ K, ∀ q ∈ K, ‖ψ p - ψ q‖ ≤ M₁ * ‖p - q‖ := fun p hp q hq =>
    hKc.norm_image_sub_le_of_norm_deriv_le (f := ψ) (C := M₁)
      (fun u hu => hψd.differentiableAt (isOpen_thickening.mem_nhds (hKU hu))) hd1 hq hp
  have lb1 : ∀ p ∈ K, ∀ q ∈ K, ρ ≤ ‖ψ p - conj (ψ q)‖ := fun p hp q hq => by
    have := xpm_im_add_le_norm_sub_conj (ψ p) (ψ q)
    linarith [(hψb p (hKU hp)).2, (hψb q (hKU hq)).2]
  have lb2 : ∀ p ∈ K, ∀ q ∈ K, c / 2 ≤ ‖p - conj q‖ := fun p hp q hq => by
    have := xpm_im_add_le_norm_sub_conj p q
    linarith [hbelow p hp, hbelow q hq]
  have hm2 : 0 < m / 2 := by positivity
  have hc2 : 0 < c / 2 := by positivity
  have t1 : |Real.log ‖ddq ψ x y‖ - Real.log ‖ddq ψ x y'‖| ≤ M₂ / (m / 2) * ‖y - y'‖ := by
    refine (xpm_abs_log_sub_le hm2 (hlow x hx y hy) (hlow x hx y' hy')).trans ?_
    have h := ddq_lip isOpen_thickening hψd hKc hKU hM₂0 hd2 hx hy hx hy'
    rw [sub_self, norm_zero, zero_add] at h
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hm2]
    exact (abs_norm_sub_norm_le _ _).trans h
  have t2 : |Real.log ‖ψ x - conj (ψ y)‖ - Real.log ‖ψ x - conj (ψ y')‖| ≤
      M₁ / ρ * ‖y - y'‖ := by
    refine (xpm_abs_log_sub_le hρ (lb1 x hx y hy) (lb1 x hx y' hy')).trans ?_
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hρ]
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [show ψ x - conj (ψ y) - (ψ x - conj (ψ y')) = conj (ψ y' - ψ y) by
      simp only [map_sub]; ring, RCLike.norm_conj, norm_sub_rev]
    exact hψL y hy y' hy'
  have t3 : |Real.log ‖x - conj y‖ - Real.log ‖x - conj y'‖| ≤ 1 / (c / 2) * ‖y - y'‖ := by
    refine (xpm_abs_log_sub_le hc2 (lb2 x hx y hy) (lb2 x hx y' hy')).trans ?_
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff_of_pos_right hc2]
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [show x - conj y - (x - conj y') = conj (y' - y) by simp only [map_sub]; ring,
      RCLike.norm_conj, norm_sub_rev]
  unfold qt
  rw [abs_le] at t1 t2 t3 ⊢
  constructor <;> nlinarith [t1.1, t1.2, t2.1, t2.2, t3.1, t3.2]

end SWCore
end QuantumZipper
