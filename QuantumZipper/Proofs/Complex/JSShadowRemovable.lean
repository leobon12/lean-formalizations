import QuantumZipper.Proofs.Complex.JSShadowACL7
import QuantumZipper.Analysis.Removability

/-!
# EXT-JS nodes B1 (vertical lines) and B3/C0: the shadow condition implies removability

Blueprint `blueprint/EXT_JS_BLUEPRINT.md`, §2 "(C0: SH ⇒ removable.)", steps 5 (last sentence)
and 6, and §3 node C0 `removable_of_shadow`.

Source: P. W. Jones and S. K. Smirnov, *Removability theorems for Sobolev functions and
quasiconformal maps*, Ark. Mat. 38 (2000) 263–279, §2: Proposition 1 (p. 269, proof pp. 270–272)
gives the absolute continuity of `f` on almost every line in every direction; the deduction of
Theorem 1 (p. 270) then concludes, for a homeomorphism conformal off `K`, by Weyl's lemma. Here the
last step is Morera's theorem from the line integrals (A4 `differentiable_of_acl`, `JSMorera.lean`),
which needs only horizontal and vertical lines and no area-zero statement for `K`.

Vertical lines come from horizontal ones by the rotation trick of the blueprint: apply
`acl_horizontal_of_shadow` to `w ↦ e (I w)`, the compact set `{w | I w ∈ K}` and the charts
`z ↦ -I · F_i z` (their shadow sums are unchanged, rotation being an isometry); the horizontal
line at height `-x` is mapped by `w ↦ I w` onto the vertical line `re = x`.

Main results: `acl_vertical_of_shadow`, `removable_of_shadow`.
-/

noncomputable section

open MeasureTheory Set Complex Metric Filter Topology
open scoped ENNReal

namespace QuantumZipper.JS

lemma I_mul_neg_I_mul (w : ℂ) : I * (-I * w) = w := by
  rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]

lemma I_mul_line (t y : ℝ) : I * ((t : ℂ) + (y : ℂ) * I) = ((-y : ℝ) : ℂ) + (t : ℂ) * I := by
  push_cast
  linear_combination (y : ℂ) * I_mul_I

/-- Rotating a chart by `-I` does not change its shadow sum. -/
lemma shadowSum_rot (R : ℝ) (F : ℂ → ℂ) : shadowSum R (fun z => -I * F z) = shadowSum R F := by
  have hiso : Isometry fun w : ℂ => -I * w := Isometry.of_dist_eq fun w₁ w₂ => by
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, norm_neg, norm_I, one_mul]
  unfold shadowSum
  refine tsum_congr fun m => Finset.sum_congr rfl fun j _ => ?_
  rw [show (fun z => -I * F z) '' tent R m j = (fun w => -I * w) '' (F '' tent R m j) from
    (image_image _ _ _).symm, hiso.ediam_image]

/-- A rotated chart is a chart for the rotated set. -/
lemma isChart_rot {K : Set ℂ} {R : ℝ} {F : ℂ → ℂ} (hF : IsChart K R F) :
    IsChart ((fun w => I * w) ⁻¹' K) R (fun z => -I * F z) where
  pos := hF.pos
  cont := continuousOn_const.mul hF.cont
  holo := hF.holo.const_mul _
  inj := fun z hz w hw h => hF.inj hz hw (mul_left_cancel₀ (neg_ne_zero.2 I_ne_zero) h)
  mapsTo := fun z hz => by
    simp only [mem_compl_iff, mem_preimage, I_mul_neg_I_mul]
    exact hF.mapsTo hz

/-- **EXT-JS node B1, vertical lines.** Hypothesis `hv` of A4 (`differentiable_of_acl`). -/
theorem acl_vertical_of_shadow {K : Set ℂ} (hK : IsCompact K) {ι : Type*} [Fintype ι] {R : ℝ}
    {F : ι → ℂ → ℂ} (hF : ∀ i, IsChart K R (F i)) (hSH : ∀ i, shadowSum R (F i) < ⊤)
    (hcov : K ⊆ ⋃ i, F i '' ((↑) '' Set.Icc (-R) R)) (e : ℂ ≃ₜ ℂ)
    (he : DifferentiableOn ℂ e Kᶜ) :
    ∀ᵐ x : ℝ, ∀ a b : ℝ,
      e (x + b * Complex.I) - e (x + a * Complex.I)
        = Complex.I * ∫ t in a..b, Kᶜ.indicator (deriv e) (x + t * Complex.I) := by
  set r : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ I I_ne_zero with hr
  have hrapp : ∀ w, r w = I * w := fun w => rfl
  set K' : Set ℂ := (fun w => I * w) ⁻¹' K with hK'
  set e' : ℂ ≃ₜ ℂ := r.trans e with he'
  have he'app : ∀ w, e' w = e (I * w) := fun w => rfl
  have hK'c : IsCompact K' := r.isCompact_preimage.2 hK
  have hmaps : MapsTo (fun w => I * w) K'ᶜ Kᶜ := fun w hw => hw
  have he'd : DifferentiableOn ℂ e' K'ᶜ :=
    he.comp ((differentiable_id.const_mul I).differentiableOn) hmaps
  have hcov' : K' ⊆ ⋃ i, (fun z => -I * F i z) '' ((↑) '' Set.Icc (-R) R) := by
    intro w hw
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hcov hw
    obtain ⟨z, hz, hzw⟩ := hi
    refine mem_iUnion.2 ⟨i, z, hz, ?_⟩
    simp only [hzw, ← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]
  have hH := acl_horizontal_of_shadow hK'c (fun i => isChart_rot (hF i))
    (fun i => by rw [shadowSum_rot]; exact hSH i) hcov' e' he'd
  -- the density of `e'`
  have hind : ∀ w, K'ᶜ.indicator (deriv e') w = I * Kᶜ.indicator (deriv e) (I * w) := by
    intro w
    by_cases hw : I * w ∈ K
    · rw [indicator_of_notMem (show w ∉ K'ᶜ from fun h => h hw),
        indicator_of_notMem (show I * w ∉ Kᶜ from fun h => h hw), mul_zero]
    · rw [indicator_of_mem (show w ∈ K'ᶜ from hw), indicator_of_mem (show I * w ∈ Kᶜ from hw)]
      have hd := (he.differentiableAt (hK.isClosed.isOpen_compl.mem_nhds hw)).hasDerivAt
      have h2 := hd.comp w ((hasDerivAt_id w).const_mul I)
      rw [mul_one] at h2
      rw [show (⇑e' : ℂ → ℂ) = ⇑e ∘ fun w => I * w from rfl, h2.deriv, mul_comm]
  have hH2 : ∀ᵐ y : ℝ, ∀ a b : ℝ,
      e (((-y : ℝ) : ℂ) + b * I) - e (((-y : ℝ) : ℂ) + a * I)
        = I * ∫ t in a..b, Kᶜ.indicator (deriv e) (((-y : ℝ) : ℂ) + t * I) := by
    filter_upwards [hH] with y hy a b
    calc e (((-y : ℝ) : ℂ) + b * I) - e (((-y : ℝ) : ℂ) + a * I)
        = e' (b + y * I) - e' (a + y * I) := by rw [he'app, he'app, I_mul_line, I_mul_line]
      _ = ∫ t in a..b, K'ᶜ.indicator (deriv e') (t + y * I) := hy a b
      _ = ∫ t in a..b, I * Kᶜ.indicator (deriv e) (((-y : ℝ) : ℂ) + t * I) :=
          intervalIntegral.integral_congr fun t _ => by
            simp only [hind, I_mul_line]
      _ = I * ∫ t in a..b, Kᶜ.indicator (deriv e) (((-y : ℝ) : ℂ) + t * I) :=
          intervalIntegral.integral_const_mul _ _
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hH2
  filter_upwards [hneg] with x hx
  simpa only [neg_neg] using hx

/-- **EXT-JS node B3/C0 (`removable_of_shadow`).** A compact set covered by finitely many charts
with finite shadow sums is conformally removable. -/
theorem removable_of_shadow {K : Set ℂ} (hK : IsCompact K) {ι : Type*} [Fintype ι] {R : ℝ}
    {F : ι → ℂ → ℂ} (hF : ∀ i, IsChart K R (F i)) (hSH : ∀ i, shadowSum R (F i) < ⊤)
    (hcov : K ⊆ ⋃ i, F i '' ((↑) '' Set.Icc (-R) R)) : IsConformallyRemovable K :=
  ⟨hK, fun φ hφ => differentiable_of_acl φ.continuous (locallyIntegrable_indicator_deriv hK hφ)
    (acl_horizontal_of_shadow hK hF hSH hcov φ hφ) (acl_vertical_of_shadow hK hF hSH hcov φ hφ)⟩

end QuantumZipper.JS
