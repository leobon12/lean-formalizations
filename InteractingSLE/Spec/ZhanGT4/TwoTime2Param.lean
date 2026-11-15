/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Holomorphic dependence of time integrals on a complex parameter

Packet PROVE-ZHAN-GT4-A4, a tool for the two-time Loewner calculus (D1)–(D5) of Astra's follow-up note, Part A.1.1
(`source/external/AstraIG1/ig1_followup_proofs.txt` L245–L275). The derivatives `g_t'`, `g_t''`, `g_t'''` of a Loewner
map are time integrals of holomorphic functions of the starting point; this file differentiates such integrals.

Let `F : ℝ → ℂ → ℂ` be jointly continuous on `[0, T] × B(p, r)` with every `F s` holomorphic on the disc. Then

* `continuousOn_deriv_of_holo`: `(s, z) ↦ (F s)'(z)` is jointly continuous (Cauchy's formula for the derivative,
  `Complex.cderiv`, and uniform continuity on compact sets);
* `hasDerivAt_integral_of_holo`: `z ↦ ∫₀ᵗ F s z ds` is holomorphic with derivative `∫₀ᵗ (F s)'(z) ds`
  (differentiation under the integral sign, dominated by Cauchy's estimate);
* `continuousOn_integral_of_holo`: `(t, z) ↦ ∫₀ᵗ F s z ds` is jointly continuous.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped Interval

namespace InteractingSLE.ZhanGT4

variable {F : ℝ → ℂ → ℂ} {T r : ℝ} {p : ℂ}

/-- A closed disc of radius `2ρ` around a point of an open disc, inside that disc. -/
theorem exists_closedBall_two_mul_subset {z : ℂ} (hz : z ∈ ball p r) :
    ∃ ρ > 0, closedBall z (2 * ρ) ⊆ ball p r := by
  have h : 0 < r - dist z p := sub_pos.2 hz
  refine ⟨(r - dist z p) / 4, by positivity, fun w hw => ?_⟩
  rw [mem_closedBall] at hw
  rw [mem_ball]
  calc dist w p ≤ dist w z + dist z p := dist_triangle _ _ _
    _ < r := by linarith

/-- **The derivative of a jointly continuous family of holomorphic functions is jointly continuous.** -/
theorem continuousOn_deriv_of_holo {b : ℝ} (hd : ∀ s ∈ Icc b T, DifferentiableOn ℂ (F s) (ball p r))
    (hc : ContinuousOn (fun q : ℝ × ℂ => F q.1 q.2) (Icc b T ×ˢ ball p r)) :
    ContinuousOn (fun q : ℝ × ℂ => deriv (F q.1) q.2) (Icc b T ×ˢ ball p r) := by
  rintro ⟨s₀, z₀⟩ ⟨hs₀, hz₀⟩
  obtain ⟨ρ, hρ, hρsub⟩ := exists_closedBall_two_mul_subset hz₀
  have hK : IsCompact (Icc b T ×ˢ closedBall z₀ (2 * ρ)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKsub : Icc b T ×ˢ closedBall z₀ (2 * ρ) ⊆ Icc b T ×ˢ ball p r := prod_mono le_rfl hρsub
  have huc := Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous (hc.mono hKsub))
  have hder : ContinuousAt (deriv (F s₀)) z₀ :=
    ((hd s₀ hs₀).deriv isOpen_ball).continuousOn.continuousAt (isOpen_ball.mem_nhds hz₀)
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := huc (ε * ρ / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuousAt_iff.1 hder (ε / 2) (by positivity)
  refine ⟨min (min δ₁ δ₂) ρ, by positivity, ?_⟩
  rintro ⟨s, z⟩ ⟨hs, hz⟩ hdist
  have hds : dist s s₀ < min (min δ₁ δ₂) ρ := lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_left _ _) hdist
  have hdz : dist z z₀ < min (min δ₁ δ₂) ρ := lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_right _ _) hdist
  simp only [lt_min_iff] at hds hdz
  have hzρ : closedBall z ρ ⊆ ball p r := fun w hw => hρsub (by
    rw [mem_closedBall] at hw ⊢
    linarith [dist_triangle w z z₀])
  have hsph : sphere z ρ ⊆ closedBall z₀ (2 * ρ) := fun w hw => by
    rw [mem_sphere] at hw
    rw [mem_closedBall]
    linarith [dist_triangle w z z₀]
  have e1 : deriv (F s) z = cderiv ρ (F s) z := (cderiv_eq_deriv isOpen_ball (hd s hs) hρ hzρ).symm
  have e2 : deriv (F s₀) z = cderiv ρ (F s₀) z :=
    (cderiv_eq_deriv isOpen_ball (hd s₀ hs₀) hρ hzρ).symm
  have hcs : ∀ σ ∈ Icc b T, ContinuousOn (F σ) (sphere z ρ) := fun σ hσ =>
    ((hd σ hσ).continuousOn).mono (sphere_subset_closedBall.trans hzρ |>.trans (subset_refl _))
  have hlt : ‖cderiv ρ (F s) z - cderiv ρ (F s₀) z‖ < ε * ρ / 2 / ρ := by
    refine norm_cderiv_sub_lt hρ (fun w hw => ?_) (hcs s hs) (hcs s₀ hs₀)
    have hm1 : (s, w) ∈ Icc b T ×ˢ closedBall z₀ (2 * ρ) := ⟨hs, hsph hw⟩
    have hm2 : (s₀, w) ∈ Icc b T ×ˢ closedBall z₀ (2 * ρ) := ⟨hs₀, hsph hw⟩
    have hd' : dist (s, w) (s₀, w) < δ₁ := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      exact hds.1.1
    have := h₁ _ hm1 _ hm2 hd'
    rwa [dist_eq_norm] at this
  have hρ' : ε * ρ / 2 / ρ = ε / 2 := by field_simp
  rw [hρ'] at hlt
  have h2 := h₂ hdz.1.2
  rw [dist_eq_norm] at h2 ⊢
  calc ‖deriv (F s) z - deriv (F s₀) z₀‖
      ≤ ‖deriv (F s) z - deriv (F s₀) z‖ + ‖deriv (F s₀) z - deriv (F s₀) z₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := by
        have h3 : ‖deriv (F s) z - deriv (F s₀) z‖ < ε / 2 := by rw [e1, e2]; exact hlt
        exact add_lt_add h3 h2
    _ = ε := by ring

/-- A bound for `F` on a compact sub-box. -/
theorem exists_bound_of_holo (hc : ContinuousOn (fun q : ℝ × ℂ => F q.1 q.2) (Icc 0 T ×ˢ ball p r))
    {z : ℂ} {ρ : ℝ} (hρsub : closedBall z ρ ⊆ ball p r) :
    ∃ M, 0 ≤ M ∧ ∀ s ∈ Icc 0 T, ∀ w ∈ closedBall z ρ, ‖F s w‖ ≤ M := by
  have hK : IsCompact (Icc 0 T ×ˢ closedBall z ρ) := isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hc.mono (prod_mono le_rfl hρsub))
  refine ⟨max M 0, le_max_right _ _, fun s hs w hw => (hM (s, w) ⟨hs, hw⟩).trans (le_max_left _ _)⟩

/-- **Differentiation under the integral sign** for a jointly continuous family of holomorphic functions:
`(∫₀ᵗ F s · ds)'(z) = ∫₀ᵗ (F s)'(z) ds` for `t ∈ [0, T]`. -/
theorem hasDerivAt_integral_of_holo (hd : ∀ s ∈ Icc 0 T, DifferentiableOn ℂ (F s) (ball p r))
    (hc : ContinuousOn (fun q : ℝ × ℂ => F q.1 q.2) (Icc 0 T ×ˢ ball p r)) {z : ℂ} (hz : z ∈ ball p r)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivAt (fun w => ∫ s in (0 : ℝ)..t, F s w) (∫ s in (0 : ℝ)..t, deriv (F s) z) z := by
  obtain ⟨ρ, hρ, hρsub⟩ := exists_closedBall_two_mul_subset hz
  obtain ⟨M, hM0, hM⟩ := exists_bound_of_holo hc hρsub
  have hΙ : Ι (0 : ℝ) t ⊆ Icc 0 T := by
    rw [uIoc_of_le ht.1]
    exact fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩
  have hIcc : uIcc (0 : ℝ) t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc_right ht.2
  have hcs : ∀ w ∈ ball p r, ContinuousOn (fun s => F s w) (Icc 0 T) := fun w hw =>
    hc.comp (continuous_id.prodMk continuous_const).continuousOn (fun s hs => ⟨hs, hw⟩)
  have hdc := continuousOn_deriv_of_holo hd hc
  have hball : ball z ρ ⊆ ball p r := fun w hw => hρsub (by
    rw [mem_closedBall]; rw [mem_ball] at hw; linarith)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun w s => F s w) (F' := fun w s => deriv (F s) w) (bound := fun _ => M / ρ)
    (ball_mem_nhds z hρ) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_).2
  · filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact ((hcs w hw).mono hΙ).aestronglyMeasurable measurableSet_uIoc
  · exact ((hcs z hz).mono hIcc).intervalIntegrable
  · exact (hdc.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, hz⟩) |>.mono hΙ).aestronglyMeasurable measurableSet_uIoc
  · refine Eventually.of_forall fun s hs w hw => ?_
    have hs' := hΙ hs
    have hwρ : closedBall w ρ ⊆ ball p r := fun y hy => hρsub (by
      rw [mem_closedBall] at hy ⊢; rw [mem_ball] at hw; linarith [dist_triangle y w z])
    rw [← cderiv_eq_deriv isOpen_ball (hd s hs') hρ hwρ]
    refine norm_cderiv_le hρ fun y hy => hM s hs' y ?_
    rw [mem_sphere] at hy; rw [mem_closedBall]; rw [mem_ball] at hw
    linarith [dist_triangle y w z]
  · refine Eventually.of_forall fun s hs w hw => ?_
    exact ((hd s (hΙ hs)).differentiableAt (isOpen_ball.mem_nhds (hball hw))).hasDerivAt

/-- **Joint continuity of time integrals**: `(t, z) ↦ ∫₀ᵗ F s z ds` is continuous on `[0, T] × B(p, r)`. -/
theorem continuousOn_integral_of_holo
    (hc : ContinuousOn (fun q : ℝ × ℂ => F q.1 q.2) (Icc 0 T ×ˢ ball p r)) :
    ContinuousOn (fun q : ℝ × ℂ => ∫ s in (0 : ℝ)..q.1, F s q.2) (Icc 0 T ×ˢ ball p r) := by
  rintro ⟨t₀, z₀⟩ ⟨ht₀, hz₀⟩
  obtain ⟨ρ, hρ, hρsub⟩ := exists_closedBall_two_mul_subset hz₀
  have hρsub' : closedBall z₀ ρ ⊆ ball p r := (closedBall_subset_closedBall (by linarith)).trans hρsub
  obtain ⟨M, hM0, hM⟩ := exists_bound_of_holo hc hρsub'
  have hK : IsCompact (Icc 0 T ×ˢ closedBall z₀ ρ) := isCompact_Icc.prod (isCompact_closedBall _ _)
  have huc := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous (hc.mono (prod_mono le_rfl hρsub')))
  have hcs : ∀ w ∈ ball p r, ContinuousOn (fun s => F s w) (Icc 0 T) := fun w hw =>
    hc.comp (continuous_id.prodMk continuous_const).continuousOn (fun s hs => ⟨hs, hw⟩)
  have hint : ∀ w ∈ ball p r, ∀ a b, a ∈ Icc 0 T → b ∈ Icc 0 T →
      IntervalIntegrable (fun s => F s w) volume a b := fun w hw a b ha hb =>
    ((hcs w hw).mono (uIcc_subset_Icc ha hb)).intervalIntegrable
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := huc (ε / (2 * (T + 1))) (by
    have : 0 ≤ T := ht₀.1.trans ht₀.2
    positivity)
  refine ⟨min (min δ₁ ρ) (ε / (2 * (M + 1))), by positivity, ?_⟩
  rintro ⟨t, z⟩ ⟨ht, hz⟩ hdist
  have hdt : dist t t₀ < min (min δ₁ ρ) (ε / (2 * (M + 1))) :=
    lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_left _ _) hdist
  have hdz : dist z z₀ < min (min δ₁ ρ) (ε / (2 * (M + 1))) :=
    lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_right _ _) hdist
  simp only [lt_min_iff] at hdt hdz
  have hzK : z ∈ closedBall z₀ ρ := by rw [mem_closedBall]; exact hdz.1.2.le
  have hT0 : 0 ≤ T := ht₀.1.trans ht₀.2
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT0⟩
  -- split: `∫₀ᵗ F(·, z) − ∫₀^{t₀} F(·, z₀) = ∫₀ᵗ (F(·, z) − F(·, z₀)) + ∫_{t₀}^t F(·, z₀)`
  have hsplit : (∫ s in (0 : ℝ)..t, F s z) - ∫ s in (0 : ℝ)..t₀, F s z₀ =
      (∫ s in (0 : ℝ)..t, (F s z - F s z₀)) + ∫ s in t₀..t, F s z₀ := by
    rw [intervalIntegral.integral_sub (hint z hz 0 t h0 ht) (hint z₀ hz₀ 0 t h0 ht),
      ← intervalIntegral.integral_add_adjacent_intervals (hint z₀ hz₀ 0 t₀ h0 ht₀)
        (hint z₀ hz₀ t₀ t ht₀ ht)]
    ring
  have hA : ‖∫ s in (0 : ℝ)..t, (F s z - F s z₀)‖ ≤ ε / (2 * (T + 1)) * |t - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    have hs' : s ∈ Icc 0 T := by
      rw [uIoc_of_le ht.1] at hs; exact ⟨hs.1.le, hs.2.trans ht.2⟩
    have := h₁ (s, z) ⟨hs', hzK⟩ (s, z₀) ⟨hs', mem_closedBall_self hρ.le⟩ (by
      rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]; exact hdz.1.1)
    rw [dist_eq_norm] at this
    exact this.le
  have hB : ‖∫ s in t₀..t, F s z₀‖ ≤ M * |t - t₀| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    exact hM s (uIcc_subset_Icc ht₀ ht (uIoc_subset_uIcc hs)) z₀ (mem_closedBall_self hρ.le)
  rw [dist_eq_norm, hsplit]
  have htT : |t - 0| ≤ T := by rw [sub_zero, abs_of_nonneg ht.1]; exact ht.2
  have hdt' : |t - t₀| < ε / (2 * (M + 1)) := by rw [← Real.dist_eq]; exact hdt.2
  calc ‖(∫ s in (0 : ℝ)..t, (F s z - F s z₀)) + ∫ s in t₀..t, F s z₀‖
      ≤ ε / (2 * (T + 1)) * |t - 0| + M * |t - t₀| := (norm_add_le _ _).trans (add_le_add hA hB)
    _ ≤ ε / (2 * (T + 1)) * T + M * (ε / (2 * (M + 1))) := by
        gcongr
    _ < ε / 2 + ε / 2 := by
        have h1 : ε / (2 * (T + 1)) * T < ε / 2 := by
          rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        have h2 : M * (ε / (2 * (M + 1))) < ε / 2 := by
          rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        linarith
    _ = ε := by ring

theorem integral_shift_eq (G : ℝ → ℂ) (b t : ℝ) :
    ∫ s in (0 : ℝ)..t - b, G (s + b) = ∫ s in b..t, G s := by
  rw [intervalIntegral.integral_comp_add_right G b]; simp

/-- `hasDerivAt_integral_of_holo` on a time interval `[b, c]`, integrating from `b`. -/
theorem hasDerivAt_integral_of_holo_Icc {b c : ℝ} (hd : ∀ s ∈ Icc b c, DifferentiableOn ℂ (F s) (ball p r))
    (hc : ContinuousOn (fun q : ℝ × ℂ => F q.1 q.2) (Icc b c ×ˢ ball p r)) {z : ℂ} (hz : z ∈ ball p r)
    {t : ℝ} (ht : t ∈ Icc b c) :
    HasDerivAt (fun w => ∫ s in b..t, F s w) (∫ s in b..t, deriv (F s) z) z := by
  have hdG : ∀ s ∈ Icc (0 : ℝ) (c - b), DifferentiableOn ℂ (F (s + b)) (ball p r) := fun s hs =>
    hd _ ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hcl : Continuous fun q : ℝ × ℂ => (q.1 + b, q.2) := by fun_prop
  have hcG : ContinuousOn (fun q : ℝ × ℂ => F (q.1 + b) q.2) (Icc 0 (c - b) ×ˢ ball p r) :=
    hc.comp hcl.continuousOn fun q hq => (⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, hq.2⟩ :
      (q.1 + b, q.2) ∈ Icc b c ×ˢ ball p r)
  have h := hasDerivAt_integral_of_holo (F := fun s => F (s + b)) hdG hcG hz
    (t := t - b) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hfun : (fun w => ∫ s in (0 : ℝ)..t - b, F (s + b) w) = fun w => ∫ s in b..t, F s w :=
    funext fun w => integral_shift_eq (fun s => F s w) b t
  rw [hfun, integral_shift_eq (fun s => deriv (F s) z)] at h
  exact h

/-- `continuousOn_integral_of_holo` on a time interval `[b, c]`, integrating from `b`. -/
theorem continuousOn_integral_of_holo_Icc {b c : ℝ}
    (hc : ContinuousOn (fun q : ℝ × ℂ => F q.1 q.2) (Icc b c ×ˢ ball p r)) :
    ContinuousOn (fun q : ℝ × ℂ => ∫ s in b..q.1, F s q.2) (Icc b c ×ˢ ball p r) := by
  have hcl : Continuous fun q : ℝ × ℂ => (q.1 + b, q.2) := by fun_prop
  have hcG : ContinuousOn (fun q : ℝ × ℂ => F (q.1 + b) q.2) (Icc 0 (c - b) ×ˢ ball p r) :=
    hc.comp hcl.continuousOn fun q hq => (⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, hq.2⟩ :
      (q.1 + b, q.2) ∈ Icc b c ×ˢ ball p r)
  have hcl' : Continuous fun q : ℝ × ℂ => (q.1 - b, q.2) := by fun_prop
  have h := (continuousOn_integral_of_holo (F := fun s => F (s + b)) hcG).comp hcl'.continuousOn
    (fun q hq => ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, hq.2⟩ :
      MapsTo (fun q : ℝ × ℂ => (q.1 - b, q.2)) (Icc b c ×ˢ ball p r) (Icc 0 (c - b) ×ˢ ball p r))
  refine h.congr fun q _ => ?_
  simp only [Function.comp_apply]
  exact (integral_shift_eq (fun s => F s q.2) b q.1).symm

/-- Continuity of `x ↦ ∫₀¹ g x θ dθ` on a set `S` when `g` is jointly continuous on `S × [0, 1]`. -/
theorem continuousOn_integral_unit {X : Type*} [TopologicalSpace X] {S : Set X} {g : X → ℝ → ℂ}
    (hg : ContinuousOn (fun p : X × ℝ => g p.1 p.2) (S ×ˢ Icc 0 1)) :
    ContinuousOn (fun x => ∫ θ in (0 : ℝ)..1, g x θ) S := by
  rw [continuousOn_iff_continuous_domRestrict]
  set f : S → ℝ → ℂ := fun x θ => g x (projIcc 0 1 zero_le_one θ) with hfdef
  have hf : Continuous (Function.uncurry f) := by
    have hc : Continuous fun p : S × ℝ => ((p.1 : X), ((projIcc 0 1 zero_le_one p.2 : Icc (0 : ℝ) 1) : ℝ)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))
    exact hg.comp_continuous hc fun p => ⟨p.1.2, (projIcc 0 1 zero_le_one p.2).2⟩
  have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := MeasureTheory.volume)
    hf 0 1
  refine h.congr fun x => ?_
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  rw [uIcc_of_le zero_le_one] at hθ
  simp only [hfdef, projIcc_of_mem _ hθ]

end InteractingSLE.ZhanGT4
