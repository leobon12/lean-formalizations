/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRIotaReflect
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # GW4: side preservation also at endpoint driver contacts -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap isOpen_H)

namespace InteractingSLE.Theorem14.GW4Fix

open Sec7.R5Lift

/-- Positive reflection gives the ordinary positive real derivative of the
boundary map, with the boundary function itself as the differentiated map. -/
theorem exists_pos_hasDerivAt_re_boundary {g : ℂ → ℂ} {x r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ g (H ∩ ball (x : ℂ) r))
    (hc : ContinuousOn g (Hbar ∩ ball (x : ℂ) r))
    (hreal : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → (g z).im = 0)
    (hmaps : ∀ z ∈ H ∩ ball (x : ℂ) r, g z ∈ H)
    (hinj : InjOn g (H ∩ ball (x : ℂ) r)) :
    ∃ b : ℝ, 0 < b ∧ HasDerivAt (fun v : ℝ => (g v).re) b x := by
  obtain ⟨b, hb, hder⟩ := exists_pos_tendsto_deriv_of_reflect' hr hd hc hreal hmaps hinj
  obtain ⟨G, hG, hGg, -⟩ := QuantumZipper.CA.exists_reflection_extension hd hc hreal
  have hxB : (x : ℂ) ∈ ball (x : ℂ) r := mem_ball_self hr
  have hHB : H ∩ ball (x : ℂ) r ⊆ Hbar ∩ ball (x : ℂ) r :=
    inter_subset_inter_left _ fun z (hz : 0 < z.im) => (le_of_lt hz : 0 ≤ z.im)
  have hGder : deriv G x = (b : ℂ) := by
    have hcontd : ContinuousAt (deriv G) x :=
      ((hG.deriv isOpen_ball).continuousOn).continuousAt (isOpen_ball.mem_nhds hxB)
    have h1 : Tendsto (deriv G) (𝓝[H] (x : ℂ)) (𝓝 (b : ℂ)) := by
      refine hder.congr' ?_
      filter_upwards [inter_mem_nhdsWithin H (isOpen_ball.mem_nhds hxB)] with y hy
      exact (Filter.eventuallyEq_of_mem ((isOpen_H.inter isOpen_ball).mem_nhds hy)
        fun z hz => (hGg (hHB hz)).symm).deriv_eq
    have := nhdsWithin_H_neBot x
    exact tendsto_nhds_unique (hcontd.tendsto.mono_left nhdsWithin_le_nhds) h1
  have hGx : HasDerivAt G (b : ℂ) (x : ℂ) := by
    rw [← hGder]; exact (hG.differentiableAt (isOpen_ball.mem_nhds hxB)).hasDerivAt
  have hφ := hGx.real_of_complex
  rw [ofReal_re] at hφ
  refine ⟨b, hb, hφ.congr_of_eventuallyEq ?_⟩
  filter_upwards [continuous_ofReal.continuousAt.preimage_mem_nhds
    (isOpen_ball.mem_nhds hxB)] with v hv
  rw [hGg ⟨show (0 : ℝ) ≤ (v : ℂ).im by rw [ofReal_im], hv⟩]

/-- A transition anchored at zero preserves sides throughout its open
real interval, even when zero is an endpoint of that interval. -/
theorem side_of_anchored_interval_notMem {cur : Chart} (hcur : cur.IsConformal)
    {Fc : ℂ → ℂ} (hFc : EqOn Fc cur.2.1 H) (hFcc : ContinuousOn Fc Hbar)
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    (hK : (cur.dom : Set ℂ) ⊆ H \ fwdHull W T) {a b : ℝ}
    (hland : ∀ u ∈ Ioo a b, Fc u ∉ H \ fwdHull W T)
    (ha : a ≤ 0) (hb : 0 ≤ b)
    (htip : Tendsto (fun z => fwdMap W T (cur.2.1 z)) (𝓝[H] 0) (𝓝 0)) :
    ∀ u ∈ Ioo a b, ∀ y : ℝ,
      Tendsto (fun z => fwdMap W T (cur.2.1 z)) (𝓝[H] (u : ℂ)) (𝓝 (y : ℂ)) →
      (u < 0 ↔ y < 0) := by
  let S : ℂ → ℂ := fun z => fwdMap W T (cur.2.1 z)
  let g : ℂ → ℂ := extendFrom H S
  let φ : ℝ → ℝ := fun u => (g u).re
  have hlandB : ∀ u ∈ Ioo a b, ∃ ρ > 0,
      ∀ v : ℝ, (v : ℂ) ∈ ball (u : ℂ) ρ → Fc v ∉ H \ fwdHull W T := by
    intro u hu
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 isOpen_Ioo u hu
    exact ⟨ρ, hρ, fun v hv => hland v (hball (mem_ball_of_ofReal_mem_ball hv))⟩
  have hdat : ∀ u ∈ Ioo a b, Tendsto S (𝓝[H] (u : ℂ)) (𝓝 (g u)) ∧ (g u).im = 0 := by
    intro u hu
    obtain ⟨ρ, hρ, hl⟩ := hlandB u hu
    obtain ⟨-, -, hgr, -, -, -, hgl⟩ := reflect_data_of_notMem (x := u) (ρ := ρ)
      hcur hFc hFcc hη hW hW0 hT hK hl
    exact ⟨hgl u ⟨show (0 : ℝ) ≤ (u : ℂ).im by rw [ofReal_im], mem_ball_self hρ⟩,
      hgr u (mem_ball_self hρ) (ofReal_im u)⟩
  have hg0 : g 0 = 0 := extendFrom_eq (show (0 : ℂ) ∈ closure H from by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact (show (0 : ℝ) ≤ (0 : ℂ).im from le_rfl)) htip
  have hφ0 : φ 0 = 0 := by change (g 0).re = 0; rw [hg0]; rfl
  have hφc : ContinuousOn φ (insert 0 (Ioo a b)) :=
    continuousOn_of_tendsto_nhdsWithin_H (f := fun z => (S z).re) fun u hu => by
      rcases hu with h0 | hu
      · subst u
        simpa only [Function.comp_def, S, φ, ofReal_zero, hg0, zero_re] using
          (continuous_re.tendsto 0).comp htip
      · exact (continuous_re.tendsto _).comp (hdat u hu).1
  have hφd : ∀ u ∈ Ioo a b, 0 < deriv φ u := by
    intro u hu
    obtain ⟨ρ, hρ, hl⟩ := hlandB u hu
    obtain ⟨-, hgc, hgr, hm, hi, hgd, -⟩ := reflect_data_of_notMem (x := u) (ρ := ρ)
      hcur hFc hFcc hη hW hW0 hT hK hl
    obtain ⟨c, hc, hder⟩ := exists_pos_hasDerivAt_re_boundary hρ hgd hgc hgr hm hi
    change 0 < deriv (fun v : ℝ => (g v).re) u
    rw [hder.deriv]
    exact hc
  intro u hu y hy
  have hyφ : y = φ u := by
    have := nhdsWithin_H_neBot u
    have heq := tendsto_nhds_unique hy (hdat u hu).1
    exact congrArg Complex.re heq
  rw [hyφ]
  rcases lt_trichotomy u 0 with hneg | hzero | hpos
  · have hsub : Icc u 0 ⊆ insert 0 (Ioo a b) := by
      intro v hv
      rcases hv.2.eq_or_lt with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨hu.1.trans_le hv.1, h0.trans_le hb⟩
    have hm := strictMonoOn_of_deriv_pos (convex_Icc u 0) (hφc.mono hsub) (fun v hv => by
      rw [interior_Icc] at hv
      exact hφd v ⟨hu.1.trans hv.1, hv.2.trans_le hb⟩)
    have hφu : φ u < 0 := by simpa only [hφ0] using hm ⟨le_rfl, hneg.le⟩ ⟨hneg.le, le_rfl⟩ hneg
    exact iff_of_true hneg hφu
  · simp only [hzero, hφ0, lt_self_iff_false]
  · have hsub : Icc 0 u ⊆ insert 0 (Ioo a b) := by
      intro v hv
      rcases hv.1.eq_or_lt with h0 | h0
      · exact Or.inl h0.symm
      · exact Or.inr ⟨ha.trans_lt h0, hv.2.trans_lt hu.2⟩
    have hm := strictMonoOn_of_deriv_pos (convex_Icc 0 u) (hφc.mono hsub) (fun v hv => by
      rw [interior_Icc] at hv
      exact hφd v ⟨ha.trans_lt hv.1, hv.2.trans hu.2⟩)
    have hφu : 0 < φ u := by simpa only [hφ0] using hm ⟨le_rfl, hpos.le⟩ ⟨hpos.le, le_rfl⟩ hpos
    exact iff_of_false (not_lt.2 hpos.le) (not_lt.2 hφu.le)

end InteractingSLE.Theorem14.GW4Fix
