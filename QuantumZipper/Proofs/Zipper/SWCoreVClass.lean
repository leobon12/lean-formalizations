import QuantumZipper.Proofs.Zipper.SWCoreDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-V-CLASS: deterministic rescaling estimates for the boundary map class

Task SWC-V-CLASS (helper of SWC-V, `handoff/SW-CORE.md` §5).

Source: S. Sheffield, M. Wang, *Field-measure correspondence in Liouville quantum gravity almost
surely commutes with all conformal maps simultaneously*, arXiv:1605.06171, Lemma 3.4, estimates
(3.17)–(3.19), p. 15: for maps of the normalized family the rescaled map
`T(u) = (ψ(t + r u) − ψ(t)) / (r ψ'(t))` is `O(r)`-close to the identity on the unit disc, and
bi-Lipschitz with constants close to `1`. SW obtain the derivative bounds from de Branges/Koebe;
here, for the rational class `BdryClass a b ρ M m` of `SWCoreDefs.lean`, they come from Cauchy's
estimates on discs of radius `ρ/4` (`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`), and
the closeness from the mean value inequality (`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`).
The upper half plane is preserved (`Im T u ≥ 0` for `Im u ≥ 0`) because `ψ` is real on the real
points of the thickening, by the identity theorem applied to `z ↦ conj (ψ (conj z))`
(`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`); positivity `ψ'(t) ≥ m` comes from strict
monotonicity on `[a,b]` and the second-order Taylor bound (own elementary argument for these
standard steps).

The hypothesis `a < b` is needed: for `a = b` the class contains `ψ(z) = -z` (strict monotonicity
on a point is vacuous), for which `ψ'(t) = -1 < 0`.
-/

noncomputable section

open Metric Set Filter
open scoped Topology ComplexConjugate

namespace QuantumZipper
namespace SWCore

lemma swcv_ball_sub {a b ρ t : ℝ} (ht : t ∈ Icc a b) :
    ball (t : ℂ) ρ ⊆ thickening ρ (segC a b) :=
  ball_subset_thickening (mem_image_of_mem (fun s : ℝ => (s : ℂ)) ht) ρ

/-- Cauchy estimate for `ψ'` on the `ρ/2`-ball around a point of `[a,b]`. -/
lemma swcv_deriv_bound {a b ρ M m : ℝ} {ψ : ℂ → ℂ} (hψ : ψ ∈ BdryClass a b ρ M m) (hρ : 0 < ρ)
    {t : ℝ} (ht : t ∈ Icc a b) {w : ℂ} (hw : w ∈ ball (t : ℂ) (ρ / 2)) :
    ‖deriv ψ w‖ ≤ (|M| + 1) / (ρ / 4) := by
  obtain ⟨hd, hM, -, -, -⟩ := hψ
  have hsub : closedBall w (ρ / 4) ⊆ thickening ρ (segC a b) := by
    intro z hz
    apply swcv_ball_sub ht
    rw [mem_ball] at hw ⊢
    rw [mem_closedBall] at hz
    calc dist z t ≤ dist z w + dist w t := dist_triangle _ _ _
      _ < ρ := by linarith
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
  · refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball w (by positivity)]
    exact hd.mono hsub
  · intro z hz
    exact (hM z (hsub (sphere_subset_closedBall hz))).trans (by linarith [le_abs_self M])

/-- Cauchy estimate for `ψ''` on the `ρ/4`-ball around a point of `[a,b]`. -/
lemma swcv_deriv2_bound {a b ρ M m : ℝ} {ψ : ℂ → ℂ} (hψ : ψ ∈ BdryClass a b ρ M m) (hρ : 0 < ρ)
    {t : ℝ} (ht : t ∈ Icc a b) {z : ℂ} (hz : z ∈ ball (t : ℂ) (ρ / 4)) :
    ‖deriv (deriv ψ) z‖ ≤ (|M| + 1) / (ρ / 4) / (ρ / 4) := by
  have hd := hψ.1
  have hsub : closedBall z (ρ / 4) ⊆ thickening ρ (segC a b) := by
    intro w hw
    apply swcv_ball_sub ht
    rw [mem_ball] at hz ⊢
    rw [mem_closedBall] at hw
    calc dist w t ≤ dist w z + dist z t := dist_triangle _ _ _
      _ < ρ := by linarith
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
  · refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball z (by positivity)]
    exact (hd.deriv isOpen_thickening).mono hsub
  · intro w hw
    apply swcv_deriv_bound hψ hρ ht
    rw [mem_sphere] at hw
    rw [mem_ball] at hz ⊢
    calc dist w t ≤ dist w z + dist z t := dist_triangle _ _ _
      _ < ρ / 2 := by linarith

/-- Lipschitz bound for `ψ − ψ'(t)·id` on `closedBall t s`, `s < ρ/4`. -/
lemma swcv_lip {a b ρ M m : ℝ} {ψ : ℂ → ℂ} (hψ : ψ ∈ BdryClass a b ρ M m) (hρ : 0 < ρ)
    {t : ℝ} (ht : t ∈ Icc a b) {s : ℝ} (hs : s < ρ / 4) {z w : ℂ}
    (hz : z ∈ closedBall (t : ℂ) s) (hw : w ∈ closedBall (t : ℂ) s) :
    ‖(ψ z - deriv ψ t * z) - (ψ w - deriv ψ t * w)‖ ≤
      (|M| + 1) / (ρ / 4) / (ρ / 4) * s * ‖z - w‖ := by
  set K := (|M| + 1) / (ρ / 4) / (ρ / 4) with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hs0 : 0 ≤ s := dist_nonneg.trans (mem_closedBall.1 hz)
  have hB : closedBall (t : ℂ) s ⊆ ball (t : ℂ) (ρ / 4) := closedBall_subset_ball hs
  have hS : ∀ x ∈ closedBall (t : ℂ) s, x ∈ thickening ρ (segC a b) := fun x hx =>
    swcv_ball_sub ht (ball_subset_ball (by linarith) (hB hx))
  have hdiff : ∀ x ∈ closedBall (t : ℂ) s, DifferentiableAt ℂ ψ x := fun x hx =>
    hψ.1.differentiableAt (isOpen_thickening.mem_nhds (hS x hx))
  have hdiff2 : ∀ x ∈ closedBall (t : ℂ) s, DifferentiableAt ℂ (deriv ψ) x := fun x hx =>
    (hψ.1.deriv isOpen_thickening).differentiableAt (isOpen_thickening.mem_nhds (hS x hx))
  have h1 : ∀ x ∈ closedBall (t : ℂ) s, ‖deriv ψ x - deriv ψ t‖ ≤ K * s := by
    intro x hx
    have := (convex_closedBall (t : ℂ) s).norm_image_sub_le_of_norm_deriv_le hdiff2
      (fun y hy => swcv_deriv2_bound hψ hρ ht (hB hy)) (mem_closedBall_self hs0) hx
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hK0)
    rw [← dist_eq_norm]
    exact mem_closedBall.1 hx
  have hφd : ∀ x ∈ closedBall (t : ℂ) s,
      HasDerivWithinAt (fun y => ψ y - deriv ψ t * y) (deriv ψ x - deriv ψ t)
        (closedBall (t : ℂ) s) x := by
    intro x hx
    exact (((hdiff x hx).hasDerivAt.sub ((hasDerivAt_id' x).const_mul (deriv ψ t))).congr_deriv
      (by rw [mul_one])).hasDerivWithinAt
  exact (convex_closedBall (t : ℂ) s).norm_image_sub_le_of_norm_hasDerivWithin_le hφd h1 hw hz

/-- `ψ` is real on the real points of the thickening (identity theorem for
`z ↦ conj (ψ (conj z))`). -/
lemma swcv_real {a b ρ M m : ℝ} {ψ : ℂ → ℂ} (hψ : ψ ∈ BdryClass a b ρ M m) (hρ : 0 < ρ)
    (hab : a < b) {x : ℝ} (hx : (x : ℂ) ∈ thickening ρ (segC a b)) : (ψ x).im = 0 := by
  obtain ⟨hd, -, hre, -, -⟩ := hψ
  set S := thickening ρ (segC a b) with hSdef
  have hconjS : ∀ z ∈ S, conj z ∈ S := by
    intro z hz
    rw [hSdef, mem_thickening_iff] at hz ⊢
    obtain ⟨y, hy, hzy⟩ := hz
    refine ⟨y, hy, ?_⟩
    obtain ⟨s, -, rfl⟩ := hy
    calc dist (conj z) (s : ℂ) = dist (conj z) (conj (s : ℂ)) := by rw [Complex.conj_ofReal]
      _ = dist z s := Complex.dist_conj_conj _ _
      _ < ρ := hzy
  have hg : DifferentiableOn ℂ (conj ∘ ψ ∘ conj) S := by
    intro z hz
    have h1 : DifferentiableAt ℂ ψ (conj z) :=
      hd.differentiableAt (isOpen_thickening.mem_nhds (hconjS z hz))
    have h2 := h1.conj_conj
    rw [Complex.conj_conj] at h2
    exact h2.differentiableWithinAt
  have hS : IsOpen S := isOpen_thickening
  have hconvseg : Convex ℝ (segC a b) := (convex_Icc a b).linear_image Complex.ofRealCLM.toLinearMap
  have hconv : Convex ℝ S := hconvseg.thickening ρ
  have hfreq : ∃ᶠ z in 𝓝[≠] (a : ℂ), ψ z = (conj ∘ ψ ∘ conj) z := by
    have hlim : Tendsto (fun n : ℕ => ((a + (b - a) * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) atTop
        (𝓝[≠] (a : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        have h1 : Tendsto (fun n : ℕ => a + (b - a) * (1 / ((n : ℝ) + 1))) atTop
            (𝓝 (a + (b - a) * 0)) := tendsto_const_nhds.add (tendsto_const_nhds.mul h0)
        rw [mul_zero, add_zero] at h1
        exact (Complex.continuous_ofReal.tendsto a).comp h1
      · refine Eventually.of_forall (fun n => ?_)
        simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_inj]
        intro h
        have hp : 0 < (b - a) * (1 / ((n : ℝ) + 1)) := by
          have : 0 < b - a := by linarith
          positivity
        linarith
    refine hlim.frequently (Frequently.of_forall (fun n => ?_))
    have hn1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hn0 : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
    have hs : a + (b - a) * (1 / ((n : ℝ) + 1)) ∈ Icc a b := by
      constructor <;> nlinarith
    have him := hre _ hs
    simp only [Function.comp_apply, Complex.conj_ofReal]
    exact (Complex.conj_eq_iff_im.2 him).symm
  have ha : (a : ℂ) ∈ S := self_subset_thickening hρ _ ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩
  have heq := (hd.analyticOnNhd hS).eqOn_of_preconnected_of_frequently_eq (hg.analyticOnNhd hS)
    hconv.isPreconnected ha hfreq hx
  simp only [Function.comp_apply, Complex.conj_ofReal] at heq
  exact Complex.conj_eq_iff_im.1 heq.symm

lemma swcv_le_zero_of_forall {c K h₀ : ℝ} (hK : 0 < K) (hh₀ : 0 < h₀)
    (H : ∀ h, 0 < h → h < h₀ → c ≤ K * h) : c ≤ 0 := by
  by_contra hc
  push Not at hc
  set h := min (h₀ / 2) (c / (2 * K))
  have hpos : 0 < h := lt_min (by linarith) (by positivity)
  have hlt : h < h₀ := (min_le_left _ _).trans_lt (by linarith)
  have h2 : K * h ≤ K * (c / (2 * K)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hK.le
  have h3 : K * (c / (2 * K)) = c / 2 := by field_simp
  linarith [H h hpos hlt]

/-- `ψ'(t)` is real and `≥ m` at every `t ∈ [a,b]`. -/
lemma swcv_deriv_real {a b ρ M m : ℝ} {ψ : ℂ → ℂ} (hψ : ψ ∈ BdryClass a b ρ M m) (hρ : 0 < ρ)
    (hab : a < b) {t : ℝ} (ht : t ∈ Icc a b) :
    deriv ψ t = ((deriv ψ t).re : ℂ) ∧ m ≤ (deriv ψ t).re := by
  set K := (|M| + 1) / (ρ / 4) / (ρ / 4) with hKdef
  have hK : 0 < K := by positivity
  set D' := deriv ψ t with hD'
  have hre := hψ.2.2.1
  have hmono := hψ.2.2.2.1
  -- a direction `σ = ±1` pointing into `[a,b]`
  obtain ⟨σ, h₀, hh₀, hσ, hdir⟩ : ∃ σ h₀ : ℝ, 0 < h₀ ∧ (σ = 1 ∨ σ = -1) ∧
      ∀ h, 0 < h → h < h₀ → t + σ * h ∈ Icc a b ∧
        0 < σ * ((ψ ((t + σ * h : ℝ) : ℂ)).re - (ψ (t : ℂ)).re) := by
    by_cases htb : t < b
    · refine ⟨1, b - t, by linarith, Or.inl rfl, fun h hh hh' => ?_⟩
      have hm : t + 1 * h ∈ Icc a b := ⟨by linarith [ht.1], by linarith⟩
      refine ⟨hm, ?_⟩
      have := hmono ht hm (by linarith)
      simp only at this
      linarith
    · have htb' : t = b := le_antisymm ht.2 (not_lt.1 htb)
      refine ⟨-1, b - a, by linarith, Or.inr rfl, fun h hh hh' => ?_⟩
      have hm : t + -1 * h ∈ Icc a b := ⟨by linarith, by linarith⟩
      refine ⟨hm, ?_⟩
      have := hmono hm ht (by linarith)
      simp only at this
      linarith
  have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  -- second-order bound in direction `σ`
  have hQ : ∀ h, 0 < h → h < min h₀ (ρ / 4) →
      ‖ψ ((t + σ * h : ℝ) : ℂ) - ψ (t : ℂ) - D' * ((σ * h : ℝ) : ℂ)‖ ≤ K * h * h := by
    intro h hh hlt
    have hnorm : ‖(((t + σ * h : ℝ) : ℂ) - (t : ℂ))‖ = h := by
      rw [show ((t + σ * h : ℝ) : ℂ) - (t : ℂ) = ((σ * h : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_mul, hσ1, one_mul, abs_of_pos hh]
    have hz : ((t + σ * h : ℝ) : ℂ) ∈ closedBall (t : ℂ) h := by
      rw [mem_closedBall, dist_eq_norm, hnorm]
    have := swcv_lip hψ hρ ht (lt_of_lt_of_le hlt (min_le_right _ _)) hz
      (mem_closedBall_self hh.le)
    rw [hnorm] at this
    convert this using 2
    push_cast
    ring
  have hIm : |D'.im| ≤ 0 := by
    refine swcv_le_zero_of_forall (h₀ := min h₀ (ρ / 4)) hK (lt_min hh₀ (by positivity))
      (fun h hh hlt => ?_)
    have hq := hQ h hh hlt
    have hy := hre _ (hdir h hh (lt_of_lt_of_le hlt (min_le_left _ _))).1
    have ht0 := hre t ht
    have him := (Complex.abs_im_le_norm _).trans hq
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hy, ht0,
      mul_zero, zero_add, zero_sub, neg_zero] at him
    rw [abs_neg, abs_mul, abs_mul, hσ1, one_mul, abs_of_pos hh] at him
    nlinarith
  have hRe : -D'.re ≤ 0 := by
    refine swcv_le_zero_of_forall (h₀ := min h₀ (ρ / 4)) hK (lt_min hh₀ (by positivity))
      (fun h hh hlt => ?_)
    have hq := hQ h hh hlt
    have hd := (hdir h hh (lt_of_lt_of_le hlt (min_le_left _ _))).2
    have hre' := abs_le.1 ((Complex.abs_re_le_norm _).trans hq)
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] at hre'
    rcases hσ with rfl | rfl <;> nlinarith
  have hIm0 : D'.im = 0 := abs_nonpos_iff.1 hIm
  have hD : D' = (D'.re : ℂ) := Complex.ext (by simp) (by simp [hIm0])
  refine ⟨hD, ?_⟩
  have hm := hψ.2.2.2.2 t ht
  rw [← hD', hD, Complex.norm_of_nonneg (by linarith)] at hm
  exact hm

end SWCore
end QuantumZipper
