/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MoHull

/-!
# Normalized charts of one domain differ by a real translation

Packet PROVE-SB2-LCMEAN, round 11 (item F2). The relative chart of `EL`'s stage (the relative run chart composed with
the upper chart, `Mn.stageRelChart`) and the canonical chart of the retained hull (`Mo.hullChart`) map the same domain
onto `ℍ`, and both inverses stay within bounded distance of the identity (run charts are `WalkIntCanon.IsNormalized`;
the mapping-out function is hydrodynamic). Such charts differ by a real translation:

* `translate_of_realMobius_bounded`: a real Möbius map of `ℍ` with bounded displacement is a real translation;
* **`exists_translate_of_isDomainChart`**: two domain charts of one domain whose inverses are within bounded distance
  of the identity have forward maps differing by a real constant;
* `IsMapOut.exists_norm_sub_le`, **`hullChart_inv_bounded`**: the mapping-out function of a compact `ℍ`-hull has
  bounded displacement, so the canonical hull chart's inverse stays within bounded distance of the identity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Function
open QuantumZipper (H)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE.Theorem14.SB.Mo

theorem ofReal_mul_I_mem_H {y : ℝ} (hy : 0 < y) : (y : ℂ) * I ∈ H := show 0 < ((y : ℂ) * I).im by simpa

/-- **A real Möbius map of `ℍ` with bounded displacement is a real translation.** -/
theorem translate_of_realMobius_bounded {a b c d : ℝ} (hdet : 0 < a * d - b * c) {M : ℝ}
    (hb : ∀ w ∈ H, ‖realMobius a b c d w - w‖ ≤ M) : ∃ t : ℝ, ∀ w ∈ H, realMobius a b c d w = w + t := by
  -- the lower-left coefficient vanishes
  have hc : c = 0 := by
    by_contra hc
    have hcpos : 0 < |c| := abs_pos.2 hc
    set y : ℝ := max 1 ((|a| + |b|) / |c| + M + 1) with hy
    have hy1 : 1 ≤ y := le_max_left _ _
    have hy2 : (|a| + |b|) / |c| + M + 1 ≤ y := le_max_right _ _
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
    have hw := hb _ (ofReal_mul_I_mem_H hy0)
    have hden : ‖(c : ℂ) * ((y : ℂ) * I) + d‖ ≥ |c| * y := by
      have : ((c : ℂ) * ((y : ℂ) * I) + d).im = c * y := by simp
      calc ‖(c : ℂ) * ((y : ℂ) * I) + d‖ ≥ |((c : ℂ) * ((y : ℂ) * I) + d).im| := abs_im_le_norm _
        _ = |c| * y := by rw [this, abs_mul, abs_of_pos hy0]
    have hnum : ‖(a : ℂ) * ((y : ℂ) * I) + b‖ ≤ |a| * y + |b| := by
      calc ‖(a : ℂ) * ((y : ℂ) * I) + b‖ ≤ ‖(a : ℂ) * ((y : ℂ) * I)‖ + ‖(b : ℂ)‖ := norm_add_le _ _
        _ = |a| * y + |b| := by
          simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
    have hcy : 0 < |c| * y := mul_pos hcpos hy0
    have hφ : ‖realMobius a b c d ((y : ℂ) * I)‖ ≤ (|a| + |b|) / |c| := by
      unfold realMobius
      rw [norm_div, div_le_div_iff₀ (lt_of_lt_of_le hcy hden) hcpos]
      calc ‖(a : ℂ) * ((y : ℂ) * I) + b‖ * |c| ≤ (|a| * y + |b|) * |c| :=
            mul_le_mul_of_nonneg_right hnum (abs_nonneg c)
        _ ≤ (|a| + |b|) * (|c| * y) := by
            have := mul_le_mul_of_nonneg_left hy1 (mul_nonneg (abs_nonneg b) (abs_nonneg c))
            nlinarith [this]
        _ ≤ (|a| + |b|) * ‖(c : ℂ) * ((y : ℂ) * I) + d‖ :=
            mul_le_mul_of_nonneg_left hden (by positivity)
    have hiy : ‖(y : ℂ) * I‖ = y := by simp [abs_of_pos hy0]
    have h1 : y - (|a| + |b|) / |c| ≤ ‖realMobius a b c d ((y : ℂ) * I) - (y : ℂ) * I‖ := by
      have := norm_sub_norm_le ((y : ℂ) * I) (realMobius a b c d ((y : ℂ) * I))
      rw [hiy, norm_sub_rev] at this
      linarith
    linarith
  subst hc
  have hd : d ≠ 0 := by
    rintro rfl
    simp at hdet
  -- the leading ratio is one
  have hr : a / d = 1 := by
    by_contra hr
    have hpos : 0 < |a / d - 1| := abs_pos.2 (sub_ne_zero.2 hr)
    set y : ℝ := max 1 ((M + |b / d| + 1) / |a / d - 1|) with hy
    have hy1 : 1 ≤ y := le_max_left _ _
    have hy2 : (M + |b / d| + 1) / |a / d - 1| ≤ y := le_max_right _ _
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
    have hw := hb _ (ofReal_mul_I_mem_H hy0)
    have hd' : (d : ℂ) ≠ 0 := ofReal_ne_zero.2 hd
    have e : realMobius a b 0 d ((y : ℂ) * I) - (y : ℂ) * I =
        (((a / d - 1) * y : ℝ) : ℂ) * I + ((b / d : ℝ) : ℂ) := by
      unfold realMobius
      simp only [ofReal_zero, zero_mul, zero_add]
      rw [sub_eq_iff_eq_add, div_eq_iff hd']
      push_cast
      field_simp
      ring
    rw [e] at hw
    have h2 : |a / d - 1| * y - |b / d| ≤ ‖(((a / d - 1) * y : ℝ) : ℂ) * I + ((b / d : ℝ) : ℂ)‖ := by
      have h3 := norm_sub_norm_le ((((a / d - 1) * y : ℝ) : ℂ) * I) (-((b / d : ℝ) : ℂ))
      rw [sub_neg_eq_add, norm_neg] at h3
      have h4 : ‖(((a / d - 1) * y : ℝ) : ℂ) * I‖ = |a / d - 1| * y := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hy0]
      have h5 : ‖((b / d : ℝ) : ℂ)‖ = |b / d| := by rw [Complex.norm_real, Real.norm_eq_abs]
      rw [h4, h5] at h3
      exact h3
    have h6 : M + |b / d| + 1 ≤ |a / d - 1| * y := by
      have := (div_le_iff₀ hpos).1 hy2
      linarith
    linarith
  refine ⟨b / d, fun w _ => ?_⟩
  have hd' : (d : ℂ) ≠ 0 := ofReal_ne_zero.2 hd
  have ha : (a : ℂ) = d := by
    have : a = d := by field_simp at hr; linarith
    rw [this]
  unfold realMobius
  simp only [ofReal_zero, zero_mul, zero_add]
  rw [ha, div_eq_iff hd']
  push_cast
  field_simp

/-- **Two domain charts of one domain whose inverses stay within bounded distance of the identity differ by a real
translation.** -/
theorem exists_translate_of_isDomainChart {D : Set ℂ} {c₁ c₂ : Chart} (h₁ : IsDomainChart D c₁)
    (h₂ : IsDomainChart D c₂) {M₁ M₂ : ℝ} (hb₁ : ∀ y ∈ H, ‖c₁.2.1 y - y‖ ≤ M₁)
    (hb₂ : ∀ y ∈ H, ‖c₂.2.1 y - y‖ ≤ M₂) : ∃ t : ℝ, ∀ z ∈ D, c₂.1 z = c₁.1 z + t := by
  set f : ℂ → ℂ := fun y => c₂.1 (c₁.2.1 y) with hf
  have hfd : DifferentiableOn ℂ f H :=
    h₂.differentiableOn_fwd.comp h₁.1.1 fun y hy => h₁.inv_mem hy
  have hbij : BijOn f H H := by
    refine ⟨fun y hy => h₂.fwd_mem (h₁.inv_mem hy), fun y₁ hy₁ y₂ hy₂ he => ?_, fun w hw => ?_⟩
    · have e1 : c₁.2.1 y₁ = c₁.2.1 y₂ := by
        have := congrArg c₂.2.1 he
        simp only [hf] at this
        rwa [h₂.inv_fwd (h₁.inv_mem hy₁), h₂.inv_fwd (h₁.inv_mem hy₂)] at this
      have := congrArg c₁.1 e1
      rwa [h₁.fwd_inv hy₁, h₁.fwd_inv hy₂] at this
    · refine ⟨c₁.1 (c₂.2.1 w), h₁.fwd_mem (h₂.inv_mem hw), ?_⟩
      simp only [hf]
      rw [h₁.inv_fwd (h₂.inv_mem hw), h₂.fwd_inv hw]
  obtain ⟨a, b, c, d, hdet, hfm⟩ := QuantumZipper.CA.exists_realMobius_of_bijOn_H hfd hbij
  have hdisp : ∀ y ∈ H, ‖realMobius a b c d y - y‖ ≤ M₂ + M₁ := by
    intro y hy
    rw [← hfm hy]
    simp only [hf]
    have hz := h₁.inv_mem hy
    have hw := h₂.fwd_mem hz
    have e : c₂.1 (c₁.2.1 y) - y = (c₂.1 (c₁.2.1 y) - c₂.2.1 (c₂.1 (c₁.2.1 y))) + (c₁.2.1 y - y) := by
      rw [h₂.inv_fwd hz]
      ring
    rw [e]
    calc _ ≤ ‖c₂.1 (c₁.2.1 y) - c₂.2.1 (c₂.1 (c₁.2.1 y))‖ + ‖c₁.2.1 y - y‖ := norm_add_le _ _
      _ ≤ M₂ + M₁ := by
        refine add_le_add ?_ (hb₁ y hy)
        rw [norm_sub_rev]
        exact hb₂ _ hw
  obtain ⟨t, ht⟩ := translate_of_realMobius_bounded hdet hdisp
  refine ⟨t, fun z hz => ?_⟩
  have hy := h₁.fwd_mem hz
  have e := (hfm hy).trans (ht _ hy)
  simp only [hf] at e
  rwa [h₁.inv_fwd hz] at e

/-- **The mapping-out function of a compact `ℍ`-hull has bounded displacement** on the complement. -/
theorem IsMapOut.exists_norm_sub_le {A : Set ℂ} {g : ℂ → ℂ} (hA : IsHPHull A) (hg : IsMapOut A g) :
    ∃ M, ∀ z ∈ H \ A, ‖g z - z‖ ≤ M := by
  obtain ⟨R, hR⟩ := eventually_cobounded_inf_principal_iff.1
    (hg.2.eventually (Metric.ball_mem_nhds (0 : ℂ) one_pos))
  obtain ⟨C, hC⟩ := hg.exists_norm_le hA
  refine ⟨max 1 (2 * |R| + C), fun z hz => ?_⟩
  by_cases hzR : R ≤ ‖z‖
  · have h := hR z hz hzR
    rw [dist_zero_right] at h
    exact h.le.trans (le_max_left _ _)
  · push Not at hzR
    have h1 : ‖z‖ ≤ |R| := hzR.le.trans (le_abs_self R)
    calc ‖g z - z‖ ≤ ‖g z‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ (‖z‖ + C) + ‖z‖ := by linarith [hC z hz]
      _ ≤ 2 * |R| + C := by linarith
      _ ≤ max 1 (2 * |R| + C) := le_max_right _ _

/-- **The canonical hull chart's inverse stays within bounded distance of the identity.** -/
theorem hullChart_inv_bounded {A : Set ℂ} (hA : IsHPHull A) (x₀ : ℝ) :
    ∃ M, ∀ y ∈ H, ‖(hullChart A x₀).2.1 y - y‖ ≤ M := by
  have hg := ConformalImage.isMapOut_mapOut hA
  obtain ⟨M, hM⟩ := hg.exists_norm_sub_le hA
  have hD := isDomainChart_hullChart hA x₀
  refine ⟨M + |x₀|, fun y hy => ?_⟩
  have hz := hD.inv_mem hy
  have e : (hullChart A x₀).1 ((hullChart A x₀).2.1 y) = y := hD.fwd_inv hy
  simp only [hullChart_fwd] at e
  have e2 : (hullChart A x₀).2.1 y - y =
      -(ConformalImage.mapOut A ((hullChart A x₀).2.1 y) - (hullChart A x₀).2.1 y) + (x₀ : ℂ) := by
    linear_combination e
  rw [e2]
  calc _ ≤ ‖-(ConformalImage.mapOut A ((hullChart A x₀).2.1 y) - (hullChart A x₀).2.1 y)‖ + ‖((x₀ : ℝ) : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ M + |x₀| := by
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
        exact add_le_add (hM _ hz) le_rfl

end InteractingSLE.Theorem14.SB.Mo
