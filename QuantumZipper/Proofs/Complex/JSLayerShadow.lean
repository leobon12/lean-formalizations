import QuantumZipper.Proofs.Complex.JSCharts
import QuantumZipper.Proofs.Complex.JSArea
import QuantumZipper.Proofs.Complex.JSTents
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# EXT-JS node C1, part 1: layer decay and the layer area of the chart

Blueprint `blueprint/EXT_JS_BLUEPRINT.md`, §2 ("(C1: layer decay LA ⇒ SH.)") and §3 node C1.

Source: P. W. Jones and S. K. Smirnov, *Removability theorems for Sobolev functions and
quasiconformal maps*, Ark. Mat. 38 (2000) 263–279, §2–3 (the Whitney-square "shadow" estimate of
Proposition 1); the dyadic tents of `JSTents.lean` replace the Whitney squares, as in the
blueprint.

This file contains the *geometric* half of C1, all of it for a single level `m`:

* `LayerDecay R F` (the hypothesis LA of the blueprint): the image of the horizontal layer
  `I_{3R/2} × (0,δ)` has area `≤ C δ^η`;
* `ediam_image_topBox_sq_le`: A1 for the top box — `diam F(Q)² ≤ (20/π) area F(Q*)`;
* `sum_volume_image_bigBox_le_layer`: the enlarged boxes of one level overlap at most twice
  (A3 `sum_indicator_bigBox_level_le_two`), so the sum of the areas of their images is at most
  twice the area of the layer they sit in (read through the area formula A2, which needs no
  measurability of the images).

The counting half (chain along descendants, Cauchy–Schwarz with a geometric weight, summation
over levels) is in `JSLayerShadowSum.lean`.
-/

noncomputable section

open Set Metric MeasureTheory Complex
open scoped ENNReal

namespace QuantumZipper
namespace JS

/-- **LA (layer decay).** The area of the image of the horizontal layer
`I_{3R/2} × (0,δ)` decays like `δ^η` — the quantitative form of "the boundary layer of a Hölder
domain has area `O(δ^η)`" (Smith–Stegenga; Jones–Smirnov, Ark. Mat. 38 (2000), §2; blueprint
EXT-JS §2, node D). -/
def LayerDecay (R : ℝ) (F : ℂ → ℂ) : Prop :=
  ∃ C η : ℝ, 0 < η ∧ ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    volume (F '' (Set.Icc (-3 * R / 2) (3 * R / 2) ×ℂ Set.Ioo 0 δ)) ≤ ENNReal.ofReal (C * δ ^ η)

/-- The closed horizontal layer `I_{3R/2} × (0,δ)` whose image `LayerDecay` controls. -/
def layer (R δ : ℝ) : Set ℂ := Icc (-3 * R / 2) (3 * R / 2) ×ℂ Ioo 0 δ

/-- The open horizontal layer, on which the area formula applies. -/
def layerOpen (R δ : ℝ) : Set ℂ := Ioo (-3 * R / 2) (3 * R / 2) ×ℂ Ioo 0 δ

lemma layerOpen_subset_layer (R δ : ℝ) : layerOpen R δ ⊆ layer R δ :=
  fun z hz => ⟨Ioo_subset_Icc_self hz.1, hz.2⟩

lemma isOpen_layerOpen (R δ : ℝ) : IsOpen (layerOpen R δ) :=
  isOpen_Ioo.reProdIm isOpen_Ioo

lemma layerOpen_subset_H (hR : 0 ≤ R) (δ : ℝ) : layerOpen R δ ⊆ H := by
  intro z hz
  rw [layerOpen, mem_reProdIm] at hz
  exact hz.2.1

/-- The enlarged boxes of one level lie in the open layer of height `5ℓ_m/4`. -/
lemma bigBox_subset_layerOpen (hR : 0 ≤ R) {m j : ℕ} (hj : j < 2 ^ m) :
    bigBox R m j ⊆ layerOpen R (5 * dyLen R m / 4) := by
  intro w hw
  rw [bigBox, mem_reProdIm] at hw
  simp only [layerOpen, mem_reProdIm]
  have hℓ0 := dyLen_nonneg hR m
  have hℓ2 : dyLen R m ≤ 2 * R := dyLen_le hR m
  have hj' : ((j : ℝ) + 1) ≤ 2 ^ m := by exact_mod_cast hj
  have hjℓ : ((j : ℝ) + 1) * dyLen R m ≤ 2 * R := by
    have h := pow_mul_dyLen R m
    nlinarith [hj', hℓ0, h]
  have hj0 : (0 : ℝ) ≤ j * dyLen R m := mul_nonneg (Nat.cast_nonneg j) hℓ0
  exact ⟨⟨by linarith [hw.1.1, hj0, hℓ2], by linarith [hw.1.2, hjℓ, hℓ2]⟩,
    ⟨by linarith [hw.2.1], hw.2.2⟩⟩

/-! ### A1 for the top box -/

/-- **A1, top box form.** For a chart `F`, the top box image has
`diam F(Q_{m,j})² ≤ (20/π) · area F(Q*_{m,j})`. Immediate from the box form of the Cauchy–area
estimate `ediam_image_rect_sq_le` (`JSArea.lean`), applied to the rectangle
`[-R+jℓ, -R+(j+1)ℓ] × [ℓ/2, ℓ]` and its `ℓ/4`-enlargement `Q*_{m,j}`. -/
theorem ediam_image_topBox_sq_le {K : Set ℂ} {R : ℝ} {F : ℂ → ℂ} (hF : IsChart K R F)
    (m j : ℕ) :
    ediam (F '' topBox R m j) ^ 2 ≤
      ENNReal.ofReal (20 / Real.pi) * volume (F '' bigBox R m j) := by
  have hℓ := dyLen_pos hF.pos m
  have hQ : Ioo (-R + j * dyLen R m - dyLen R m / 4)
      (-R + (j + 1) * dyLen R m + dyLen R m / 4) ×ℂ
      Ioo (dyLen R m / 2 - dyLen R m / 4) (dyLen R m + dyLen R m / 4) = bigBox R m j := by
    simp only [bigBox]
    ring_nf
  have hsubQ : (Ioo (-R + j * dyLen R m - dyLen R m / 4)
      (-R + (j + 1) * dyLen R m + dyLen R m / 4) ×ℂ
      Ioo (dyLen R m / 2 - dyLen R m / 4) (dyLen R m + dyLen R m / 4)) ⊆ H := by
    rw [hQ]; exact bigBox_subset_upper hF.pos.le m j
  have hmain := ediam_image_rect_sq_le (a := -R + j * dyLen R m) (b := -R + (j + 1) * dyLen R m)
    (c := dyLen R m / 2) (d := dyLen R m) (ρ := dyLen R m / 4) (h := F) (by positivity)
    (hF.holo.mono hsubQ) (hF.inj.mono hsubQ)
  rw [hQ, show Icc (-R + j * dyLen R m) (-R + (j + 1) * dyLen R m) ×ℂ
      Icc (dyLen R m / 2) (dyLen R m) = topBox R m j from rfl,
    show (-R + (j + 1) * dyLen R m - (-R + j * dyLen R m)) ^ 2 +
      (dyLen R m - dyLen R m / 2) ^ 2 = 5 * (dyLen R m) ^ 2 / 4 by ring] at hmain
  have hposπ : 0 < Real.pi * (dyLen R m / 4) ^ 2 :=
    mul_pos Real.pi_pos (pow_pos (div_pos hℓ (by norm_num)) 2)
  have hπ : ENNReal.ofReal (Real.pi * (dyLen R m / 4) ^ 2) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; exact hposπ
  have hπtop : ENNReal.ofReal (Real.pi * (dyLen R m / 4) ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc ediam (F '' topBox R m j) ^ 2
      = (ENNReal.ofReal (Real.pi * (dyLen R m / 4) ^ 2))⁻¹ *
          (ENNReal.ofReal (Real.pi * (dyLen R m / 4) ^ 2) * ediam (F '' topBox R m j) ^ 2) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hπ hπtop, one_mul]
    _ ≤ (ENNReal.ofReal (Real.pi * (dyLen R m / 4) ^ 2))⁻¹ *
          (ENNReal.ofReal (5 * (dyLen R m) ^ 2 / 4) * volume (F '' bigBox R m j)) :=
        mul_le_mul_right hmain _
    _ = ENNReal.ofReal (20 / Real.pi) * volume (F '' bigBox R m j) := by
        rw [← mul_assoc]
        have hcoef : (ENNReal.ofReal (Real.pi * (dyLen R m / 4) ^ 2))⁻¹ *
            ENNReal.ofReal (5 * (dyLen R m) ^ 2 / 4) = ENNReal.ofReal (20 / Real.pi) := by
          rw [← ENNReal.ofReal_inv_of_pos hposπ,
            ← ENNReal.ofReal_mul (inv_nonneg.mpr hposπ.le)]
          congr 1
          have hπ0 : Real.pi ≠ 0 := Real.pi_ne_zero
          have hℓ0 : dyLen R m ≠ 0 := hℓ.ne'
          field_simp
          ring
        rw [hcoef]

/-! ### The enlarged boxes of one level sit in a layer and overlap at most twice -/

/-- **Layer area of one level.** The images of the enlarged boxes of level `m` have total area at
most twice the area of the image of the layer `I_{3R/2} × (0, 5ℓ_m/4)` they sit in. The factor `2`
is the bounded overlap `sum_indicator_bigBox_level_le_two` of A3, read through the area formula
A2 (which needs no measurability of the images: everything is an integral over the *domain*). -/
theorem sum_volume_image_bigBox_le_layer {K : Set ℂ} {R : ℝ} {F : ℂ → ℂ} (hF : IsChart K R F)
    (m : ℕ) :
    ∑ j ∈ Finset.range (2 ^ m), volume (F '' bigBox R m j) ≤
      2 * volume (F '' layerOpen R (5 * dyLen R m / 4)) := by
  have hR := hF.pos.le
  set S := layerOpen R (5 * dyLen R m / 4) with hSdef
  have hSH : S ⊆ H := layerOpen_subset_H hR _
  have hsub : ∀ j ∈ Finset.range (2 ^ m), bigBox R m j ⊆ S := fun j hj =>
    bigBox_subset_layerOpen hR (Finset.mem_range.1 hj)
  set f : ℂ → ℝ≥0∞ := fun z => ‖deriv F z‖ₑ ^ 2 with hfdef
  have hfmeas : Measurable f := by
    have h2 : Measurable fun z : ℂ => ‖deriv F z‖ₑ ^ 2 := by
      simpa only [Function.comp_apply, ofReal_norm] using
        (ENNReal.measurable_ofReal.comp (measurable_norm.comp (measurable_deriv F))).pow_const (2 : ℕ)
    rwa [hfdef]
  -- each enlarged box contributes the integral of `f` over it, restricted to the layer `S`
  have h1 : ∀ j ∈ Finset.range (2 ^ m),
      volume (F '' bigBox R m j) = ∫⁻ z, (bigBox R m j).indicator f z ∂(volume.restrict S) := by
    intro j hj
    rw [volume_image_eq_lintegral_normSq_deriv (isOpen_bigBox R m j) (hF.holo.mono (fun z hz =>
        bigBox_subset_upper hR m j hz)) (hF.inj.mono (fun z hz => bigBox_subset_upper hR m j hz)),
      ← hfdef]
    rw [← Measure.restrict_restrict_of_subset (hsub j hj), lintegral_indicator
      (isOpen_bigBox R m j).measurableSet]
  rw [Finset.sum_congr rfl h1]
  have hswap : ∑ x ∈ Finset.range (2 ^ m),
        ∫⁻ z in S, (bigBox R m x).indicator f z =
      ∫⁻ z in S, ∑ x ∈ Finset.range (2 ^ m), (bigBox R m x).indicator f z :=
    (lintegral_finsetSum' _ fun j _ =>
      (hfmeas.indicator (isOpen_bigBox R m j).measurableSet).aemeasurable.restrict).symm
  rw [hswap]
  have hν : volume (F '' S) = ∫⁻ z in S, f z := by
    rw [volume_image_eq_lintegral_normSq_deriv (isOpen_layerOpen R _)
      (hF.holo.mono hSH) (hF.inj.mono hSH), ← hfdef]
  rw [hν]
  calc ∫⁻ z in S, ∑ j ∈ Finset.range (2 ^ m), (bigBox R m j).indicator f z
      ≤ ∫⁻ z in S, 2 * f z := by
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ S
        · have hsum : ∑ j ∈ Finset.range (2 ^ m), (bigBox R m j).indicator (1 : ℂ → ℝ≥0∞) z ≤ 2 :=
            sum_indicator_bigBox_level_le_two hF.pos m _ z
          have hpt : ∀ j, (bigBox R m j).indicator f z =
              (bigBox R m j).indicator (1 : ℂ → ℝ≥0∞) z * f z := by
            intro j
            by_cases hj : z ∈ bigBox R m j <;>
              simp [Set.indicator_of_mem, Set.indicator_of_notMem, hj]
          calc ∑ j ∈ Finset.range (2 ^ m), (bigBox R m j).indicator f z
              = (∑ j ∈ Finset.range (2 ^ m), (bigBox R m j).indicator (1 : ℂ → ℝ≥0∞) z) * f z := by
                rw [Finset.sum_congr rfl fun j _ => hpt j, Finset.sum_mul]
            _ ≤ 2 * f z := mul_le_mul hsum le_rfl bot_le bot_le
        · have h0 : ∀ j ∈ Finset.range (2 ^ m), (bigBox R m j).indicator f z = 0 := fun j hj =>
            Set.indicator_of_notMem (fun hc => hz (hsub j hj hc)) f
          rw [Finset.sum_eq_zero h0]; exact bot_le
    _ = 2 * ∫⁻ z in S, f z := lintegral_const_mul' 2 f (by norm_num)

/-! ### The layer areas decay geometrically -/

lemma dyLen_eq_mul (R : ℝ) (n : ℕ) : dyLen R n = 2 * R * (1 / 2 : ℝ) ^ n := by
  unfold dyLen; rw [one_div_pow]; ring

/-- `LayerDecay` with a nonnegative constant. -/
lemma LayerDecay.exists_nonneg {R : ℝ} {F : ℂ → ℂ} (hL : LayerDecay R F) :
    ∃ C η : ℝ, 0 ≤ C ∧ 0 < η ∧ ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
      volume (F '' layer R δ) ≤ ENNReal.ofReal (C * δ ^ η) := by
  obtain ⟨C, η, hη, hC⟩ := hL
  refine ⟨Max.max C 0, η, le_max_right _ _, hη, fun δ hδ => (hC δ hδ).trans ?_⟩
  refine ENNReal.ofReal_le_ofReal ?_
  rcases le_total 0 C with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h]
    have hδ' : (0:ℝ) < δ ^ η := Real.rpow_pos_of_pos hδ.1 η
    nlinarith [hδ']

/-- `ℓ_n^η = (2R)^η β^n` with `β = (1/2)^η`. -/
lemma dyLen_rpow (R η : ℝ) (n : ℕ) (hR : 0 ≤ R) :
    dyLen R n ^ η = (2 * R) ^ η * ((1 / 2 : ℝ) ^ η) ^ n := by
  have hβ : ((1 / 2 : ℝ) ^ n) ^ η = ((1 / 2 : ℝ) ^ η) ^ n := by
    rw [← Real.rpow_natCast ((1 / 2 : ℝ)) n, ← Real.rpow_natCast ((1 / 2 : ℝ) ^ η) n,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    ring
  rw [dyLen_eq_mul, Real.mul_rpow (by linarith : (0:ℝ) ≤ 2 * R)
    (by positivity : (0:ℝ) ≤ (1 / 2) ^ n), hβ]

/-- **Layer decay, geometric form.** For `n` with `5ℓ_n/4 ≤ 1`, the area of the image of the
layer of height `5ℓ_n/4` is at most `C(5/4)^η(2R)^η β^n`, `β = (1/2)^η`. -/
theorem volume_image_layer_le {R : ℝ} {F : ℂ → ℂ} {C η : ℝ} (hC : 0 ≤ C) (hη : 0 < η)
    (h : ∀ δ ∈ Set.Ioc (0 : ℝ) 1, volume (F '' layer R δ) ≤ ENNReal.ofReal (C * δ ^ η))
    (hR0 : 0 ≤ R) {n : ℕ} (h0 : 0 < dyLen R n) (hn : 5 * dyLen R n / 4 ≤ 1) :
    volume (F '' layer R (5 * dyLen R n / 4)) ≤
      ENNReal.ofReal (C * (5 / 4) ^ η * (2 * R) ^ η) *
        (ENNReal.ofReal ((1 / 2 : ℝ) ^ η)) ^ n := by
  have h5 : (0:ℝ) < 5 * dyLen R n / 4 := by linarith
  have hmem : 5 * dyLen R n / 4 ∈ Set.Ioc (0 : ℝ) 1 := ⟨h5, hn⟩
  refine (h _ hmem).trans (le_of_eq ?_)
  have hpow : (5 * dyLen R n / 4) ^ η = (5 / 4) ^ η * dyLen R n ^ η := by
    rw [show 5 * dyLen R n / 4 = 5 / 4 * dyLen R n by ring,
      Real.mul_rpow (by norm_num) (le_of_lt h0)]
  have hsplit : C * ((5 / 4) ^ η * ((2 * R) ^ η * ((1 / 2 : ℝ) ^ η) ^ n)) =
      C * (5 / 4) ^ η * (2 * R) ^ η * ((1 / 2 : ℝ) ^ η) ^ n := by ring
  rw [hpow, dyLen_rpow R η n hR0, hsplit,
    ENNReal.ofReal_mul (by
      exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (by norm_num) η))
        (Real.rpow_nonneg (by positivity) η)),
    ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num) η)]

end JS

end QuantumZipper
