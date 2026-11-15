/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualJoint
import InteractingSLE.Spec.ZhanGT4.DualSeedMeas

/-!
# Random-hull own maps at clear real seed coordinates

PROVE-ZHAN-GT4-A22. Extends the fixed-hull boundary-limit argument of `DualSeedMeas`
to `FrzMeasR`. Both the other hull and its chart can depend on the sample. No
measurable choice of image driving functions is required: the observable is the
unique mapping-out function, evaluated by limits from the upper half-plane.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory

namespace InteractingSLE.ZhanGT4.FrzMeasR

open QuantumZipper (H)

variable {Ω : Type*} [MeasurableSpace Ω]
  {W W' a : Ω → ℝ → ℝ} {A : Ω → Set ℂ} {φ : Ω → ℂ → ℂ}
  {T : Ω → ℝ} {G : Set Ω} {t : ℝ}
  (hM : FrzMeasR W W' a A φ T G t)

include hM

/-- **`F_t^{(k)}(q)` is measurable at a random real point `q` with a clear disc**, `F_t = ownExt … t`: a forward
limit of `R_t^{(k)}` at `q` along `ℍ \ E_t` (`R_t` the mapping-out function of `E_t`). The case `q = W_t` is A8's
`measurable_iterDeriv_ownExt`. -/
theorem measurable_iterDeriv_ownExt_at (k : ℕ) {q : Ω → ℝ} (hq : Measurable (G.indicator q))
    (hcl : ∀ ω ∈ G, ∃ ρ > 0, Disjoint (ball (q ω : ℂ) ρ) (imgHull (W ω) (A ω) t)) :
    Measurable (G.indicator fun ω => deriv^[k] (ownExt (W ω) (W' ω) (a ω) (φ ω) t) (q ω)) := by
  have hqC : Measurable (G.indicator fun ω => ((q ω : ℝ) : ℂ)) := by
    rw [indicator_ofReal]; exact Complex.measurable_ofReal.comp hq
  refine measurable_indicator_of_tendsto' hM.meas (D := fun ω => H \ imgHull (W ω) (A ω) t)
    (f := fun ω => deriv^[k] (ConformalImage.mapOut (imgHull (W ω) (A ω) t))) (q := fun ω => (q ω : ℂ))
    (fun ω hω => (hM.isHPHull hω).2.2.1) hM.measurableSet_mem_diff (hM.measurable_iterDeriv_mapOut k) hqC
    (fun ω hω => ?_) (fun ω hω => ?_)
  · obtain ⟨ρ, hρ, hdisj⟩ := hcl ω hω
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hs : 0 < min ε ρ / 2 := by positivity
    have hlt : min ε ρ / 2 < ρ := by have := min_le_right ε ρ; linarith
    have hlt' : min ε ρ / 2 < ε := by have := min_le_left ε ρ; linarith
    have hd : dist (q ω : ℂ) ((q ω : ℂ) + ((min ε ρ / 2 : ℝ) : ℂ) * I) = min ε ρ / 2 := by
      rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    refine ⟨(q ω : ℂ) + ((min ε ρ / 2 : ℝ) : ℂ) * I, ⟨?_, fun hE => ?_⟩, by rw [hd]; exact hlt'⟩
    · show 0 < ((q ω : ℂ) + ((min ε ρ / 2 : ℝ) : ℂ) * I).im
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add]
      exact hs
    · refine Set.disjoint_left.1 hdisj ?_ hE
      rw [mem_ball, dist_comm, hd]
      exact hlt
  · obtain ⟨ρ, hρ, hdisj⟩ := hcl ω hω
    obtain ⟨hd, -, -, -, -, hR⟩ := (hM.own ω hω).ownExt_props (hM.mem ω hω) hdisj
    have hR' := hR _ (ConformalImage.isMapOut_mapOut (hM.isHPHull hω))
    have hc : ContinuousAt (deriv^[k] (ownExt (W ω) (W' ω) (a ω) (φ ω) t)) (q ω) :=
      (differentiableOn_iterate_deriv hd isOpen_ball k).continuousOn.continuousAt
        (ball_mem_nhds _ (half_pos hρ))
    refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (q ω : ℂ) (half_pos hρ)),
      self_mem_nhdsWithin] with z hz1 hz2
    have hU : IsOpen (ball (q ω : ℂ) (ρ / 2) ∩ H) := isOpen_ball.inter QuantumZipper.isOpen_H
    exact (eventuallyEq_iterate_deriv (Filter.eventuallyEq_of_mem (hU.mem_nhds ⟨hz1, hz2.1⟩) hR') k).eq_of_nhds

/-- **`Re F_t^{(k)}(q)` is measurable** at a random clear real point `q` (on `G`). -/
theorem measurable_F_at (k : ℕ) {q : Ω → ℝ} (hq : Measurable (G.indicator q))
    (hcl : ∀ ω ∈ G, ∃ ρ > 0, Disjoint (ball (q ω : ℂ) ρ) (imgHull (W ω) (A ω) t)) :
    Measurable (G.indicator fun ω => (deriv^[k] (ownExt (W ω) (W' ω) (a ω) (φ ω) t) (q ω)).re) := by
  have heq : (G.indicator fun ω => (deriv^[k] (ownExt (W ω) (W' ω) (a ω) (φ ω) t) (q ω)).re) = fun ω =>
      (G.indicator (fun ω => deriv^[k] (ownExt (W ω) (W' ω) (a ω) (φ ω) t) (q ω)) ω).re := by
    funext ω
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω]
    · simp only [indicator_of_notMem hω, zero_re]
  rw [heq]
  exact Complex.measurable_re.comp (hM.measurable_iterDeriv_ownExt_at k hq hcl)


end InteractingSLE.ZhanGT4.FrzMeasR
