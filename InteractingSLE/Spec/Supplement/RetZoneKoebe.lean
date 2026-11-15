/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.LocalSets.Prop38

/-!
# Conformal estimates for Proposition 3.8 in a chart

Packet PROVE-T15-RET6 (Aux. lemma 82, supplement pp. 296–297: "Under `g_A` this is the same statement for a
zero-boundary field in `ℍ` … The relative local-set boundary-decay argument in Proposition 3.8 consequently gives
continuous zero boundary values"). The landed Proposition 3.8 (`LocalSets.IsLocalSetMean.ae_tendsto_sub_of_union`)
uses Euclidean ball patches `B(c, 4R)` and the Koebe variance bound of `GFF.zeroGFFTestCov_sub_le_of_dist`. At a
point where the added set touches the old one, no Euclidean ball patch works; the source's patches are the preimages
`G⁻¹(B(c, 4R))` under a conformal chart `G : D → ℍ` of a component `D` of `ℍ ∖ A₂`. This file proves the
deterministic estimates for such patches:

* `mobH w z = (z − w)/(z − w̄)`, the Möbius chart of `ℍ` onto `𝔻` sending `w` to `0`
  (`isConformalBijection_mobH`), its Apollonius bound (`norm_sub_lt_of_norm_mobH_lt`) and the lower bound
  `1 − ‖mobH w w₀‖ ≥ 2 Im w Im w₀ / |w₀ − w̄|²` (`two_mul_im_div_le_one_sub_norm_mobH`);
* `norm_le_of_isConformalBijection_ball`, `dist_le_of_isConformalBijection_ball`: Schwarz and Koebe growth bounds
  for any conformal bijection `φ : D → 𝔻` with `φ x = 0` (the proof of `GFF.exists_riemannMap_bounds`, for a given
  map);
* **`im_le_of_ref`**: a Beurling-type bound in the chart: `Im G(y) ≤ (|G y₀ − conj G y|² / (2 Im G y₀))
  (2 d / (c d₀))^{1/C}` with `d = dist(y, ∂D)`, `d₀ = dist(y₀, ∂D)`, `2d ≤ d₀`;
* **`zeroGFFTestCov_sub_le_of_chart`**: the variance gap `σ²_{ℍ∖S}(ψ) − σ²_V(ψ) ≤ 4t (∫ψ)²` for `ψ ≥ 0` supported
  in `B(y, t·dist(y, ∂D))`, when `V` contains the chart patch `D ∩ G⁻¹(B(c, R))` and
  `dist(G y, c) + 2 Im G(y)/t ≤ R`.

Deterministic; no Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric MeasureTheory
open scoped ComplexConjugate

open QuantumZipper (H zeroGFFTestCov)
open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper.CA.Koebe (koebeCovConst koebeDistExp koebeCovConst_pos koebeDistExp_pos)

namespace InteractingSLE

namespace RLC

namespace RetZone

/-! ### The Möbius chart of `ℍ` at a point -/

/-- The Möbius chart of `ℍ` onto the unit disc sending `w` to `0`: `z ↦ (z − w)/(z − w̄)`. -/
def mobH (w z : ℂ) : ℂ := (z - w) / (z - conj w)

theorem mobH_self (w : ℂ) : mobH w w = 0 := by simp [mobH]

lemma conj_eq_re_sub (w : ℂ) : conj w = (w.re : ℂ) - (w.im : ℂ) * I := by
  apply Complex.ext <;> simp

lemma sub_conj_ne_zero {w z : ℂ} (hw : w ∈ H) (hz : 0 ≤ z.im) : z - conj w ≠ 0 := by
  intro h
  have h2 := congrArg Complex.im h
  simp only [sub_im, conj_im, zero_im] at h2
  have : (0 : ℝ) < w.im := hw
  linarith

/-- `mobH w` inverts the disc chart `diskChartH w`. -/
theorem mobH_diskChartH {w ζ : ℂ} (hw : w ∈ H) (hζ : ζ ∈ ball (0 : ℂ) 1) : mobH w (diskChartH w ζ) = ζ := by
  have hne : ζ ≠ 1 := fun h => by subst h; simp at hζ
  have h1 : (1 : ℂ) - ζ ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hden : diskChartH w ζ - conj w ≠ 0 :=
    sub_conj_ne_zero hw ((isConformalBijection_diskChartH hw).2.mapsTo hζ).le
  rw [mobH, div_eq_iff hden]
  set c := QuantumZipper.CA.cayleyInv ζ with hc
  have hc1 : c * (1 - ζ) = I * (1 + ζ) := by
    rw [hc, QuantumZipper.CA.cayleyInv, div_mul_cancel₀ _ h1]
  have hd : diskChartH w ζ = (w.im : ℂ) * c + (w.re : ℂ) := rfl
  have hwc : w = (w.re : ℂ) + (w.im : ℂ) * I := (re_add_im w).symm
  rw [hd, conj_eq_re_sub]
  linear_combination (w.im : ℂ) * hc1 - hwc

/-- **The Möbius chart is a conformal bijection of `ℍ` onto `𝔻`.** -/
theorem isConformalBijection_mobH {w : ℂ} (hw : w ∈ H) : IsConformalBijection (mobH w) H (ball 0 1) := by
  have hD := isConformalBijection_diskChartH hw
  have hdiff : DifferentiableOn ℂ (mobH w) H := by
    intro z hz
    exact ((differentiableAt_id.sub_const w).div (differentiableAt_id.sub_const _)
      (sub_conj_ne_zero hw (le_of_lt hz))).differentiableWithinAt
  refine ⟨hdiff, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨ζ, hζ, rfl⟩ := hD.2.surjOn hz
    rw [mobH_diskChartH hw hζ]; exact hζ
  · intro z₁ hz₁ z₂ hz₂ he
    obtain ⟨ζ₁, hζ₁, rfl⟩ := hD.2.surjOn hz₁
    obtain ⟨ζ₂, hζ₂, rfl⟩ := hD.2.surjOn hz₂
    rw [mobH_diskChartH hw hζ₁, mobH_diskChartH hw hζ₂] at he
    rw [he]
  · intro ζ hζ
    exact ⟨diskChartH w ζ, hD.2.mapsTo hζ, mobH_diskChartH hw hζ⟩

lemma norm_sub_conj (w : ℂ) : ‖w - conj w‖ = 2 * |w.im| := by
  have : w - conj w = ((2 * w.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp; ring
  rw [this, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_mul, abs_two]

/-- **The Apollonius bound**: `‖mobH w ζ‖ < 1 − t` forces `‖ζ − w‖ < 2 Im w / t`. -/
theorem norm_sub_lt_of_norm_mobH_lt {w ζ : ℂ} (hw : w ∈ H) (hζ : ζ ∈ H) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    (h : ‖mobH w ζ‖ < 1 - t) : ‖ζ - w‖ < 2 * w.im / t := by
  have hw0 : (0 : ℝ) < w.im := hw
  have hden : ζ - conj w ≠ 0 := sub_conj_ne_zero hw (le_of_lt hζ)
  have hb : 0 < ‖ζ - conj w‖ := norm_pos_iff.2 hden
  have he : ‖ζ - w‖ = ‖mobH w ζ‖ * ‖ζ - conj w‖ := by
    rw [mobH, norm_div, div_mul_cancel₀ _ hb.ne']
  have htri : ‖ζ - conj w‖ ≤ ‖ζ - w‖ + 2 * w.im := by
    have := norm_sub_le_norm_sub_add_norm_sub ζ w (conj w)
    rw [norm_sub_conj, abs_of_pos hw0] at this
    exact this
  have h1 : ‖ζ - w‖ < (1 - t) * ‖ζ - conj w‖ := by
    rw [he]; exact mul_lt_mul_of_pos_right h hb
  rw [lt_div_iff₀ ht0]
  nlinarith [norm_nonneg (ζ - w)]

/-- **The lower bound `1 − ‖mobH w w₀‖ ≥ 2 Im w Im w₀ / |w₀ − w̄|²`.** -/
theorem two_mul_im_div_le_one_sub_norm_mobH {w w₀ : ℂ} (hw : w ∈ H) (hw₀ : w₀ ∈ H) :
    2 * w.im * w₀.im / ‖w₀ - conj w‖ ^ 2 ≤ 1 - ‖mobH w w₀‖ := by
  have hw0 : (0 : ℝ) < w.im := hw
  have hw₀0 : (0 : ℝ) < w₀.im := hw₀
  have hden : w₀ - conj w ≠ 0 := sub_conj_ne_zero hw (le_of_lt hw₀)
  set a := ‖w₀ - w‖ with ha
  set b := ‖w₀ - conj w‖ with hb
  have hb0 : 0 < b := norm_pos_iff.2 hden
  have hsq : b ^ 2 - a ^ 2 = 4 * w.im * w₀.im := by
    rw [ha, hb, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [sub_re, sub_im, conj_re, conj_im]
    ring
  have hab : a ≤ b := by nlinarith [norm_nonneg (w₀ - w)]
  have hM : ‖mobH w w₀‖ = a / b := by rw [mobH, norm_div]
  rw [hM, div_le_iff₀ (by positivity)]
  have : (1 - a / b) * b ^ 2 = (b - a) * b := by field_simp
  rw [this]
  nlinarith [norm_nonneg (w₀ - w)]

/-! ### Schwarz and growth bounds for a given conformal bijection onto the disc -/

section Bounds

variable {D : Set ℂ} {φ : ℂ → ℂ} {x : ℂ}

lemma infDist_compl_pos (hDo : IsOpen D) (hDne : D ≠ univ) (hx : x ∈ D) : 0 < infDist x Dᶜ :=
  (IsClosed.notMem_iff_infDist_pos hDo.isClosed_compl (nonempty_compl.2 hDne)).1 (fun h => h hx)

/-- **Schwarz bound** for a conformal bijection `φ : D → 𝔻` with `φ x = 0`. -/
theorem norm_le_of_isConformalBijection_ball (hφ : IsConformalBijection φ D (ball 0 1)) (hφx : φ x = 0) {y : ℂ}
    (hy : dist y x < infDist x Dᶜ) : ‖φ y‖ ≤ dist y x / infDist x Dᶜ := by
  set d := infDist x Dᶜ with hd
  have hball : ball x d ⊆ D := ball_infDist_compl_subset
  have hmaps : MapsTo φ (ball x d) (closedBall (φ x) 1) := fun z hz => by
    rw [hφx]; exact ball_subset_closedBall (hφ.2.mapsTo (hball hz))
  have := Complex.dist_le_div_mul_dist_of_mapsTo_ball (hφ.1.mono hball) hmaps (mem_ball.2 hy)
  rw [hφx, dist_zero_right] at this
  calc ‖φ y‖ ≤ 1 / d * dist y x := this
    _ = dist y x / d := by ring

/-- **Koebe growth bound** for a conformal bijection `φ : D → 𝔻` with `φ x = 0`:
`|y − x| ≤ (d / c) (1 − ‖φ y‖)^{−C₂}`. -/
theorem dist_le_of_isConformalBijection_ball (hDo : IsOpen D) (hDne : D ≠ univ)
    (hφ : IsConformalBijection φ D (ball 0 1)) (hx : x ∈ D) (hφx : φ x = 0) {y : ℂ} (hy : y ∈ D) :
    dist y x ≤ infDist x Dᶜ / koebeCovConst * (1 - ‖φ y‖) ^ (-koebeDistExp) := by
  set d := infDist x Dᶜ with hd
  have hd0 : 0 < d := infDist_compl_pos hDo hDne hx
  set ψ := Function.invFunOn φ D with hψdef
  have hψφ : ∀ z ∈ D, ψ (φ z) = z := fun z hz => hφ.2.injOn.leftInvOn_invFunOn hz
  have himg : φ '' D = ball 0 1 := hφ.2.image_eq
  have hψd : DifferentiableOn ℂ ψ (ball 0 1) := by
    have := SmallGammaGeodesics.CC.differentiableOn_leftInv hDo hφ.1 hφ.2.injOn hψφ
    rwa [himg] at this
  have hψi : InjOn ψ (ball 0 1) := by
    have := SmallGammaGeodesics.CC.injOn_leftInv hψφ
    rwa [himg] at this
  have hψimg : ψ '' ball 0 1 = D := by
    rw [← himg]; exact SmallGammaGeodesics.CC.image_leftInv_image hψφ subset_rfl
  have hψ0 : ψ 0 = x := by rw [← hφx]; exact hψφ x hx
  have hζ : φ y ∈ ball (0 : ℂ) 1 := hφ.2.mapsTo hy
  have hcov := QuantumZipper.CA.Koebe.ball_subset_image_koebe hψd hψi
  rw [hψimg, hψ0, mul_one] at hcov
  have hK : koebeCovConst * ‖deriv ψ 0‖ ≤ d := GFF.le_infDist_of_ball_subset hDne hcov
  have hg := QuantumZipper.CA.Koebe.norm_sub_le_growth_global hψd hψi hζ
  rw [hψφ y hy, hψ0, div_one, dist_zero_right, ← dist_eq_norm] at hg
  have hn1 : ‖φ y‖ ≤ 1 := (mem_ball_zero_iff.1 hζ).le
  have hn1' : ‖φ y‖ < 1 := mem_ball_zero_iff.1 hζ
  have hderiv : ‖deriv ψ 0‖ ≤ d / koebeCovConst := by
    rw [le_div_iff₀ koebeCovConst_pos]; linarith
  have hP : 0 ≤ (1 - ‖φ y‖) ^ (-koebeDistExp) := Real.rpow_nonneg (by linarith) _
  calc dist y x ≤ ‖φ y‖ * (‖deriv ψ 0‖ * (1 - ‖φ y‖) ^ (-koebeDistExp)) := hg
    _ ≤ 1 * (d / koebeCovConst * (1 - ‖φ y‖) ^ (-koebeDistExp)) := by
        have : 0 ≤ d / koebeCovConst := div_nonneg hd0.le koebeCovConst_pos.le
        gcongr
    _ = d / koebeCovConst * (1 - ‖φ y‖) ^ (-koebeDistExp) := one_mul _

end Bounds

/-! ### The chart Riemann map at a point -/

section Chart

variable {D : Set ℂ} {G : ℂ → ℂ}

/-- The Riemann map of `D` at `y` read through a chart `G : D → ℍ`. -/
def chartDisc (G : ℂ → ℂ) (y : ℂ) : ℂ → ℂ := mobH (G y) ∘ G

theorem isConformalBijection_chartDisc (hG : IsConformalBijection G D H) {y : ℂ} (hy : y ∈ D) :
    IsConformalBijection (chartDisc G y) D (ball 0 1) :=
  isConformalBijection_comp (isConformalBijection_mobH (hG.2.mapsTo hy)) hG

theorem chartDisc_self (G : ℂ → ℂ) (y : ℂ) : chartDisc G y y = 0 := mobH_self _

lemma ne_univ_of_subset_H (hDH : D ⊆ H) : D ≠ univ := fun h => by
  have : (0 : ℂ) ∈ D := h ▸ mem_univ _
  have := hDH this
  simp [H] at this

/-- **A Beurling-type bound in the chart.** For a conformal bijection `G : D → ℍ`, points `y, y₀ ∈ D` with
`2 dist(y, ∂D) ≤ dist(y₀, ∂D)`:
`Im G(y) ≤ (|G y₀ − conj G y|² / (2 Im G y₀)) · (2 dist(y, ∂D) / (c · dist(y₀, ∂D)))^{1/C₂}`. -/
theorem im_le_of_ref (hDo : IsOpen D) (hDH : D ⊆ H) (hG : IsConformalBijection G D H) {y y₀ : ℂ} (hy : y ∈ D)
    (hy₀ : y₀ ∈ D) (hdd : 2 * infDist y Dᶜ ≤ infDist y₀ Dᶜ) :
    (G y).im ≤ ‖G y₀ - conj (G y)‖ ^ 2 / (2 * (G y₀).im) *
      (2 * infDist y Dᶜ / (koebeCovConst * infDist y₀ Dᶜ)) ^ koebeDistExp⁻¹ := by
  have hDne := ne_univ_of_subset_H hDH
  set d := infDist y Dᶜ with hd
  set d₀ := infDist y₀ Dᶜ with hd₀
  have hd0 : 0 < d := infDist_compl_pos hDo hDne hy
  have hd₀0 : 0 < d₀ := by linarith
  have hw : G y ∈ H := hG.2.mapsTo hy
  have hw₀ : G y₀ ∈ H := hG.2.mapsTo hy₀
  have hs₀ : (0 : ℝ) < (G y₀).im := hw₀
  have hφ := isConformalBijection_chartDisc hG hy
  set ρ := ‖chartDisc G y y₀‖ with hρ
  have hρ1 : ρ < 1 := mem_ball_zero_iff.1 (hφ.2.mapsTo hy₀)
  have hgrow := dist_le_of_isConformalBijection_ball hDo hDne hφ hy (chartDisc_self G y) hy₀
  -- `d₀ ≤ dist y₀ y + d`
  have htri : d₀ ≤ dist y₀ y + d := by
    have := infDist_le_infDist_add_dist (x := y₀) (y := y) (s := Dᶜ)
    linarith
  have hC := koebeDistExp_pos
  have hc := koebeCovConst_pos
  have h1ρ : 0 < 1 - ρ := by linarith
  -- `(1 − ρ)^{C₂} ≤ 2d / (c d₀)`
  have hpow : (1 - ρ) ^ koebeDistExp ≤ 2 * d / (koebeCovConst * d₀) := by
    have hneg : (1 - ρ) ^ (-koebeDistExp) = ((1 - ρ) ^ koebeDistExp)⁻¹ := Real.rpow_neg h1ρ.le _
    have hpos : 0 < (1 - ρ) ^ koebeDistExp := Real.rpow_pos_of_pos h1ρ _
    rw [hneg] at hgrow
    rw [le_div_iff₀ (by positivity)]
    have h2 : d₀ / 2 ≤ d / koebeCovConst * ((1 - ρ) ^ koebeDistExp)⁻¹ := by linarith
    have h3 : d₀ / 2 * (1 - ρ) ^ koebeDistExp ≤ d / koebeCovConst := by
      have := mul_le_mul_of_nonneg_right h2 hpos.le
      rwa [mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one] at this
    have h4 : (d₀ / 2 * (1 - ρ) ^ koebeDistExp) * (2 * koebeCovConst) ≤ d / koebeCovConst * (2 * koebeCovConst) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    have e1 : d / koebeCovConst * (2 * koebeCovConst) = 2 * d := by field_simp
    rw [e1] at h4
    nlinarith
  have hroot : 1 - ρ ≤ (2 * d / (koebeCovConst * d₀)) ^ koebeDistExp⁻¹ := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg h1ρ.le _) hpow (inv_nonneg.2 hC.le)
    rwa [← Real.rpow_mul h1ρ.le, mul_inv_cancel₀ hC.ne', Real.rpow_one] at this
  have hlow := two_mul_im_div_le_one_sub_norm_mobH hw hw₀
  have hb0 : 0 < ‖G y₀ - conj (G y)‖ := norm_pos_iff.2 (sub_conj_ne_zero hw hw₀.le)
  have hmob : ‖mobH (G y) (G y₀)‖ = ρ := rfl
  rw [hmob] at hlow
  have hkey : 2 * (G y).im * (G y₀).im / ‖G y₀ - conj (G y)‖ ^ 2 ≤
      (2 * d / (koebeCovConst * d₀)) ^ koebeDistExp⁻¹ := hlow.trans hroot
  rw [div_le_iff₀ (by positivity)] at hkey
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

end Chart

/-! ### The variance gap on a chart patch -/

section Variance

/-- **The variance gap on a chart patch.** Let `D` be open, a union of components of `ℍ ∖ S` containing `y`, with a
conformal chart `G : D → ℍ`, and let `V ⊆ ℍ` be open and contain the chart patch `D ∩ G⁻¹(B(c, R))`. If
`dist(G y, c) + 2 Im G(y)/t ≤ R` and `0 < t ≤ 1/4`, then for every `ψ ≥ 0` supported in `B(y, t · dist(y, ∂D))`:
`σ²_{ℍ∖S}(ψ) − σ²_V(ψ) ≤ 4t (∫ψ)²`. -/
theorem zeroGFFTestCov_sub_le_of_chart {S V D : Set ℂ} {G : ℂ → ℂ} (hS : IsOpen (H \ S)) (hDo : IsOpen D)
    (hDS : D ⊆ H \ S) (hDc : ∀ z ∈ D, connectedComponentIn (H \ S) z ⊆ D) (hG : IsConformalBijection G D H)
    (hVo : IsOpen V) (hVH : V ⊆ H) {c : ℂ} {R : ℝ} (hV : ∀ z ∈ D, G z ∈ ball c R → z ∈ V) {y : ℂ} (hy : y ∈ D)
    {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 4) (hyc : dist (G y) c + 2 * (G y).im / t ≤ R)
    (ψ : LQGMetric.TestOn upperHalfPlaneOpens) (hψ0 : ∀ z, 0 ≤ ψ z)
    (hψs : ∀ z, ψ z ≠ 0 → dist z y < t * infDist y Dᶜ) :
    zeroGFFTestCov (H \ S) ψ ψ - zeroGFFTestCov V ψ ψ ≤ 4 * t * (∫ z, ψ z) ^ 2 := by
  have hDH : D ⊆ H := hDS.trans sdiff_subset
  have hDne := ne_univ_of_subset_H hDH
  set d := infDist y Dᶜ with hd
  have hd0 : 0 < d := infDist_compl_pos hDo hDne hy
  have hw : G y ∈ H := hG.2.mapsTo hy
  have hφ := isConformalBijection_chartDisc hG hy
  set φ := chartDisc G y with hφdef
  have htd : t * d < d := by nlinarith
  -- the support of `ψ`
  have hsupp : tsupport ψ ⊆ closedBall y (t * d) :=
    closure_minimal (fun z hz => mem_closedBall.2 (hψs z hz).le) isClosed_closedBall
  have hsD : tsupport ψ ⊆ D := hsupp.trans fun z hz =>
    ball_infDist_compl_subset (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hz) htd))
  -- the conformal disc `W = {‖φ‖ < 1 − t}`
  have hWo : IsOpen {z | z ∈ D ∧ ‖φ z‖ < 1 - t} :=
    hφ.1.continuousOn.isOpen_inter_preimage hDo
      (isOpen_lt continuous_norm (continuous_const (y := 1 - t)) : IsOpen {w : ℂ | ‖w‖ < 1 - t})
  let W : TopologicalSpace.Opens ℂ := ⟨_, hWo⟩
  let D' : TopologicalSpace.Opens ℂ := ⟨D, hDo⟩
  have hWV : (W : Set ℂ) ⊆ V := by
    rintro z ⟨hzD, hz⟩
    refine hV z hzD ?_
    have hz' := norm_sub_lt_of_norm_mobH_lt hw (hG.2.mapsTo hzD) ht0 (by linarith) hz
    rw [mem_ball]
    calc dist (G z) c ≤ dist (G z) (G y) + dist (G y) c := dist_triangle _ _ _
      _ < 2 * (G y).im / t + dist (G y) c := by rw [dist_eq_norm]; linarith
      _ ≤ R := by linarith
  have hsW : tsupport ψ ⊆ (W : Set ℂ) := by
    intro z hz
    have hzb := mem_closedBall.1 (hsupp hz)
    have hzd : dist z y < d := lt_of_le_of_lt hzb htd
    refine ⟨hsD hz, ?_⟩
    have h1 := norm_le_of_isConformalBijection_ball hφ (chartDisc_self G y) hzd
    have h2 : dist z y / d ≤ t := by rw [div_le_iff₀ hd0]; exact hzb
    linarith
  let ρ : LQGMetric.TestOn D' := ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, hsD⟩
  let ρW : LQGMetric.TestOn W := ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, hsW⟩
  have hmain := GFF.zeroGFFTestCov_sub_le_of_isConformalBijection_ball (D := D') (W := W) hφ ht0.le
    (by linarith) (by linarith) rfl ρ ρW rfl hψ0 (fun z hz => by
      have hzd : dist z y < d := lt_of_lt_of_le (hψs z hz) htd.le
      have h1 := norm_le_of_isConformalBijection_ball hφ (chartDisc_self G y) hzd
      have h2 : dist z y / d < t := by rw [div_lt_iff₀ hd0]; exact hψs z hz
      linarith)
  change zeroGFFTestCov D ψ ψ - zeroGFFTestCov (W : Set ℂ) ψ ψ ≤ _ at hmain
  have hΔ := GFF.logDelta_le ht0.le ht
  have hI : 0 ≤ (∫ z, ψ z) ^ 2 := sq_nonneg _
  have e1 := LocalSets.zeroGFFTestCov_eq_of_isClopen hS sdiff_subset hDo hDS
    (LocalSets.isOpen_diff_of_forall_connectedComponentIn_subset hS hDc) ψ hsD
  have hmono : zeroGFFTestCov (W : Set ℂ) ψ ψ ≤ zeroGFFTestCov V ψ ψ :=
    LocalSets.zeroGFFTestCov_mono hWo hVo hWV hVH ψ
  rw [e1]
  calc zeroGFFTestCov D ψ ψ - zeroGFFTestCov V ψ ψ
      ≤ zeroGFFTestCov D ψ ψ - zeroGFFTestCov (W : Set ℂ) ψ ψ := by linarith
    _ ≤ _ := hmain
    _ ≤ 4 * t * (∫ z, ψ z) ^ 2 := mul_le_mul_of_nonneg_right hΔ hI

end Variance

end RetZone

end RLC

end InteractingSLE
