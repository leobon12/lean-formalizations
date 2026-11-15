/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61RestartFinCanonical
import InteractingSLE.Spec.Sec5.Aux61GContEndpoint
import InteractingSLE.Spec.Sec5.Aux61GInstChartLanding

/-! # Inverse continuity at the retained original target

The canonical mapping-out representation of the retained chart implies the
inverse-target condition used in the finite access landing theorem. The
original target is the physical point 1 throughout.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Metric Filter Topology
open QuantumZipper (H)
open QuantumZipper.CA (cayley)

namespace InteractingSLE.Sec5.Aux61GNext
open Aux61Restart Aux61GInst

/-- Mapping-out growth and the positive-scale chart formula give uniform
inverse continuity at the original right target, over all accesses at infinity. -/
theorem inverse_target_of_scale {c : Chart} (hc : c.IsConformal)
    (hB : IsHPHull (stripTargetHull (c.dom : Set ℂ)))
    {a x : ℝ} (ha : 0 < a)
    (hscale : EqOn c.1 (fun z => (a : ℂ) *
      (ConformalImage.mapOut (stripTargetHull (c.dom : Set ℂ)) (stripRightRetarget z) - x)) c.dom) :
    ∀ ε > 0, ∃ R : ℝ, ∀ z ∈ H, R ≤ ‖z‖ → dist (c.2.1 z) 1 < ε := by
  intro ε hε
  have hev : ∀ᶠ w in Bornology.cobounded ℂ ⊓ 𝓟 H,
      dist (stripRightUntarget w) 1 < ε :=
    (tendsto_stripRightUntarget_infty.mono_right nhdsWithin_le_nhds).eventually
      (ball_mem_nhds (1 : ℂ) hε)
  obtain ⟨R₁, hR₁⟩ := eventually_cobounded_inf_principal_iff.1 hev
  obtain ⟨C, hC⟩ := (ConformalImage.isMapOut_mapOut hB).exists_norm_le hB
  refine ⟨a * (R₁ + C + |x|), fun z hz hzR => ?_⟩
  let w := stripRightRetarget (c.2.1 z)
  have hzin : c.2.1 z ∈ c.dom := hc.inv_mem_dom hz
  have hw : w ∈ H \ stripTargetHull (c.dom : Set ℂ) := by
    rw [H_diff_stripTargetHull hc.dom_subset]
    exact ⟨c.2.1 z, hzin, rfl⟩
  have hnorm : ‖z‖ ≤ a * (‖w‖ + C + |x|) := by
    calc
      ‖z‖ = a * ‖ConformalImage.mapOut (stripTargetHull (c.dom : Set ℂ)) w - (x : ℂ)‖ := by
        conv_lhs => rw [← hc.2.2 z hz, hscale hzin]
        rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos ha]
      _ ≤ a * (‖ConformalImage.mapOut (stripTargetHull (c.dom : Set ℂ)) w‖ + |x|) := by
        simpa only [norm_real, Real.norm_eq_abs] using
          mul_le_mul_of_nonneg_left (norm_sub_le
            (ConformalImage.mapOut (stripTargetHull (c.dom : Set ℂ)) w) (x : ℂ)) ha.le
      _ ≤ a * (‖w‖ + C + |x|) := by
        apply mul_le_mul_of_nonneg_left _ ha.le
        linarith only [hC w hw]
  have hRw : R₁ ≤ ‖w‖ := by nlinarith only [ha, hzR, hnorm]
  have he := hR₁ w hw.1 hRw
  dsimp only [w] at he
  rw [stripRightUntarget_retarget (hc.dom_subset hzin)] at he
  exact he

/-- The canonical bounded inverse equals the physical inverse in Cayley
coordinates at every interior point of every conformal chart. -/
theorem boundedInverse_eqOn_of_conformal {c : Chart} (hc : c.IsConformal) :
    EqOn (boundedInverse c) (cayley ∘ c.2.1) H := by
  apply extendFrom_extends
  exact (isConformalBijection_comp
    (Sec7.Lemma71F.isConformalBijection_cayley_image hc.dom_subset)
    hc.isConformalBijection).1.continuousOn

/-- The exact former `hinverse_target` premise, now proved for the
original-target normalized retained chart. -/
theorem boundedInverse_target_of_scale {c : Chart} (hc : c.IsConformal)
    (hB : IsHPHull (stripTargetHull (c.dom : Set ℂ)))
    {a x : ℝ} (ha : 0 < a)
    (hscale : EqOn c.1 (fun z => (a : ℂ) *
      (ConformalImage.mapOut (stripTargetHull (c.dom : Set ℂ)) (stripRightRetarget z) - x)) c.dom) :
    ∀ ε > 0, ∃ R : ℝ, ∀ z ∈ H, R ≤ ‖z‖ → dist (boundedInverse c z) (cayley 1) < ε := by
  have hcy : ContinuousAt cayley (1 : ℂ) :=
    (QuantumZipper.CA.differentiableAt_cayley
      (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℂ).im))).continuousAt
  intro ε hε
  obtain ⟨δ, hδ, hδcy⟩ := Metric.continuousAt_iff.1 hcy ε hε
  obtain ⟨R, hR⟩ := inverse_target_of_scale hc hB ha hscale δ hδ
  refine ⟨R, fun z hz hzR => ?_⟩
  rw [boundedInverse_eqOn_of_conformal hc hz]
  exact hδcy (hR z hz hzR)

end InteractingSLE.Sec5.Aux61GNext
