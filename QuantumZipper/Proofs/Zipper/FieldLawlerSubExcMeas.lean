import QuantumZipper.Proofs.Zipper.FieldLawlerSubExcDefs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-EXCLOWER: the similarity `flSim` and the excursion integral / diameter

* `flSim_excR_le`: `∫_{x' ≥ 0} ∂_y (h ∘ flSim σ m⁻¹)(x') dx' ≤ ∫_{σ x ≥ 0} ∂_y h(x) dx` (in fact
  equality): scale invariance of the excursion integral (Lawler, *Conformally invariant processes
  in the plane*, §5.2; the pointwise rule `∂_y (h ∘ ψ) = |ψ'| (∂_y h) ∘ ψ` for the similarity
  `ψ(x' + iy) = σ m x' + i m y`, then the change of variables `x = σ m x'`). Own elementary proof.
* `flSim_diam`: `diam (flSim σ m '' S) = diam S / m`.
-/

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology ENNReal Pointwise

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

lemma flSim_sigma_sq {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : σ * σ = 1 := by
  rcases hσ with rfl | rfl <;> norm_num

/-- Pointwise transformation rule for `yDer` under the similarity. -/
lemma flSim_yDer_le {σ m : ℝ} (hm : 0 < m) (h : ℂ → ℝ) (x : ℝ) :
    ENNReal.ofReal (yDer (fun w => h (flSim σ m⁻¹ w)) x) ≤
      ENNReal.ofReal m * ENNReal.ofReal (yDer h (σ * m * x)) := by
  conv_lhs => unfold yDer
  split_ifs with hL
  · obtain ⟨L, hT⟩ := hL
    rw [hT.limUnder_eq]
    have ht : Tendsto (fun t : ℝ => t / m) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall
        fun t (htp : 0 < t) => div_pos htp hm⟩
      have := ((continuous_id.div_const m).tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    have h2 := (hT.comp ht).div_const m
    have hh : Tendsto (fun t : ℝ => h (((σ * m * x : ℝ) : ℂ) + (t : ℂ) * I) / t) (𝓝[>] 0)
        (𝓝 (L / m)) := by
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t (htp : 0 < t)
      have hg : flSim σ m⁻¹ ((x : ℂ) + ((t / m : ℝ) : ℂ) * I) =
          ((σ * m * x : ℝ) : ℂ) + (t : ℂ) * I := by
        apply Complex.ext <;> simp [flSim] <;> field_simp
      simp only [Function.comp_apply, hg]
      field_simp
    have hy : yDer h (σ * m * x) = L / m := by
      unfold yDer
      rw [if_pos ⟨_, hh⟩, hh.limUnder_eq]
    rw [hy, ← ENNReal.ofReal_mul hm.le]
    apply le_of_eq
    congr 1
    field_simp
  · simp

/-- **Scale invariance of the excursion integral** under `flSim σ m`. -/
theorem flSim_excR_le {σ m : ℝ} (hσ : σ = 1 ∨ σ = -1) (hm : 0 < m) (h : ℂ → ℝ) :
    excR (fun w => h (flSim σ m⁻¹ w)) (Ici 0) ≤ excR h {x : ℝ | 0 ≤ σ * x} := by
  have hσσ := flSim_sigma_sq hσ
  set c : ℝ := σ * m with hc
  have hc0 : c ≠ 0 := by
    rcases hσ with rfl | rfl <;> simp [hc, hm.ne']
  have hcabs : |c⁻¹| = m⁻¹ := by
    rcases hσ with rfl | rfl <;> simp [hc, abs_of_pos hm]
  set T : Set ℝ := {x : ℝ | 0 ≤ σ * x} with hT
  have hTm : MeasurableSet T := measurableSet_le measurable_const (measurable_const_mul σ)
  set F : ℝ → ℝ≥0∞ := T.indicator fun x => ENNReal.ofReal (yDer h x) with hF
  have hFc : ∀ x : ℝ, F (c * x) = (Ici (0 : ℝ)).indicator
      (fun x => ENNReal.ofReal (yDer h (σ * m * x))) x := by
    intro x
    have hmem : c * x ∈ T ↔ x ∈ Ici (0 : ℝ) := by
      simp only [hT, mem_ofPred_eq, mem_Ici, hc]
      rw [show σ * (σ * m * x) = (σ * σ) * m * x by ring, hσσ, one_mul]
      constructor
      · intro h1; by_contra h2; push Not at h2; nlinarith
      · intro h1; positivity
    by_cases hx : x ∈ Ici (0 : ℝ)
    · rw [hF, indicator_of_mem (hmem.2 hx), indicator_of_mem hx, hc]
    · rw [hF, indicator_of_notMem (fun h' => hx (hmem.1 h')), indicator_of_notMem hx]
  have hme : MeasurableEmbedding fun t : ℝ => c * t := measurableEmbedding_mulLeft₀ hc0
  have hmap : Measure.map (fun t : ℝ => c * t) volume = ENNReal.ofReal m⁻¹ • volume := by
    rw [Real.map_volume_mul_left hc0, hcabs]
  have hchange : ∫⁻ x, F (c * x) = ENNReal.ofReal m⁻¹ * ∫⁻ x, F x := by
    rw [← hme.lintegral_map (f := F), hmap, lintegral_smul_measure, smul_eq_mul]
  unfold excR
  calc ∫⁻ x in Ici (0 : ℝ), ENNReal.ofReal (yDer (fun w => h (flSim σ m⁻¹ w)) x)
      ≤ ∫⁻ x in Ici (0 : ℝ), ENNReal.ofReal m * ENNReal.ofReal (yDer h (σ * m * x)) :=
        lintegral_mono fun x => flSim_yDer_le hm h x
    _ = ENNReal.ofReal m * ∫⁻ x in Ici (0 : ℝ), ENNReal.ofReal (yDer h (σ * m * x)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal m * ∫⁻ x, F (c * x) := by
        rw [← lintegral_indicator measurableSet_Ici]
        simp_rw [hFc]
    _ = ∫⁻ x, F x := by
        rw [hchange, ← mul_assoc, ← ENNReal.ofReal_mul hm.le, mul_inv_cancel₀ hm.ne',
          ENNReal.ofReal_one, one_mul]
    _ = ∫⁻ x in T, ENNReal.ofReal (yDer h x) := by
        rw [hF, lintegral_indicator hTm]

/-- The reflection-or-identity `z ↦ σ Re z + i Im z`. -/
lemma flSim_refl_isometry {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    Isometry fun z : ℂ => (⟨σ * z.re, z.im⟩ : ℂ) := by
  have hσσ := flSim_sigma_sq hσ
  refine Isometry.of_dist_eq fun z w => ?_
  rw [dist_eq_norm, dist_eq_norm, Complex.norm_def, Complex.norm_def]
  congr 1
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  have : (σ * z.re - σ * w.re) * (σ * z.re - σ * w.re) =
      (σ * σ) * ((z.re - w.re) * (z.re - w.re)) := by ring
  rw [this, hσσ, one_mul]

/-- `diam (flSim σ m '' S) = diam S / m`. -/
theorem flSim_diam {σ m : ℝ} (hσ : σ = 1 ∨ σ = -1) (hm : 0 < m) (S : Set ℂ) :
    Metric.diam (flSim σ m '' S) = Metric.diam S / m := by
  set R : ℂ → ℂ := fun z => ⟨σ * z.re, z.im⟩ with hR
  have hfun : flSim σ m = fun z => (m⁻¹ : ℝ) • R z := by
    funext z
    apply Complex.ext <;> simp [flSim, hR] <;> ring
  have himg : flSim σ m '' S = (m⁻¹ : ℝ) • (R '' S) := by
    rw [hfun, ← Set.image_smul, Set.image_image]
  rw [himg, diam_smul₀, (flSim_refl_isometry hσ).diam_image, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hm), div_eq_inv_mul]

end FieldLawler
end QuantumZipper
