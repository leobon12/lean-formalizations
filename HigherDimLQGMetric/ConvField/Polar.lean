import HigherDimLQGMetric.ConvField.Regularize
import HigherDimLQGMetric.Sphere.Cont
import HigherDimLQGMetric.Kernel.OneVarFourier
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Polar integration for the convolution field

Packet L2b. The first lemma is the dimension-generic change of variables from
Lebesgue measure to unit-sphere direction and positive radius.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem l2b_toSphere_eq_smul_sphereMeasure (hd : 2 ≤ d) :
    (volume : Measure (Rd d)).toSphere =
      (volume : Measure (Rd d)).toSphere univ • sphereMeasure d := by
  have : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [finrank_euclideanSpace_fin]; omega)
  let a : ℝ≥0∞ := (volume : Measure (Rd d)).toSphere univ
  have ha0 : a ≠ 0 := by
    change (volume : Measure (Rd d)).toSphere univ ≠ 0
    rw [Measure.toSphere_apply_univ, finrank_euclideanSpace_fin]
    exact mul_ne_zero (by exact_mod_cast (show d ≠ 0 by omega))
      (ne_of_gt (measure_ball_pos volume (0 : Rd d) one_pos))
  have haTop : a ≠ ⊤ := (measure_lt_top _ _).ne
  rw [sphereMeasure]
  change (volume : Measure (Rd d)).toSphere =
    a • (a⁻¹ • (volume : Measure (Rd d)).toSphere)
  rw [smul_smul, ENNReal.mul_inv_cancel ha0 haTop, one_smul]

theorem l2b_integral_polar_prod (hd : 2 ≤ d) (f : Rd d → ℝ) :
    ∫ x : Rd d, f x =
      ∫ p : sphere (0 : Rd d) 1 × Ioi (0 : ℝ),
        f ((p.2 : ℝ) • (p.1 : Rd d)) ∂
          ((volume : Measure (Rd d)).toSphere.prod (Measure.volumeIoiPow (d - 1))) := by
  have : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [finrank_euclideanSpace_fin]; omega)
  calc
    (∫ x : Rd d, f x) =
        ∫ x : ({(0 : Rd d)}ᶜ : Set (Rd d)), f x.1 ∂
          (volume : Measure (Rd d)).comap Subtype.val := by
          rw [integral_subtype_comap (measurableSet_singleton _).compl,
            restrict_compl_singleton]
    _ = ∫ p : sphere (0 : Rd d) 1 × Ioi (0 : ℝ),
        f ((p.2 : ℝ) • (p.1 : Rd d)) ∂
          ((volume : Measure (Rd d)).toSphere.prod (Measure.volumeIoiPow (d - 1))) := by
          have h := (volume : Measure (Rd d)).measurePreserving_homeomorphUnitSphereProd.integral_comp
            (Homeomorph.measurableEmbedding _)
            (fun p : sphere (0 : Rd d) 1 × Ioi (0 : ℝ) => f ((p.2 : ℝ) • (p.1 : Rd d)))
          rw [finrank_euclideanSpace_fin] at h
          have h' :
              (∫ x : ({(0 : Rd d)}ᶜ : Set (Rd d)),
                f ((‖(x : Rd d)‖ * ‖(x : Rd d)‖⁻¹) • (x : Rd d)) ∂
                  (volume : Measure (Rd d)).comap Subtype.val) =
              ∫ p : sphere (0 : Rd d) 1 × Ioi (0 : ℝ),
                f ((p.2 : ℝ) • (p.1 : Rd d)) ∂
                  ((volume : Measure (Rd d)).toSphere.prod (Measure.volumeIoiPow (d - 1))) := by
            simpa only [homeomorphUnitSphereProd_apply_fst_coe,
              homeomorphUnitSphereProd_apply_snd_coe, smul_smul] using h
          calc
            _ = ∫ x : ({(0 : Rd d)}ᶜ : Set (Rd d)),
                f ((‖(x : Rd d)‖ * ‖(x : Rd d)‖⁻¹) • (x : Rd d)) ∂
                  (volume : Measure (Rd d)).comap Subtype.val := by
              apply integral_congr_ae
              filter_upwards [] with x
              have hx : (x : Rd d) ≠ 0 := by
                intro h0
                exact x.2 (by simp [h0])
              simp [hx]
            _ = _ := h'

theorem l2b_integrable_polar_prod (hd : 2 ≤ d) {f : Rd d → ℝ}
    (hfi : Integrable f) :
    Integrable (fun p : sphere (0 : Rd d) 1 × Ioi (0 : ℝ) =>
      f ((p.2 : ℝ) • (p.1 : Rd d)))
      ((volume : Measure (Rd d)).toSphere.prod (Measure.volumeIoiPow (d - 1))) := by
  have : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [finrank_euclideanSpace_fin]; omega)
  have hsub : Integrable (fun x : ({(0 : Rd d)}ᶜ : Set (Rd d)) => f x.1)
      ((volume : Measure (Rd d)).comap Subtype.val) :=
    (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).1 hfi.integrableOn
  have hp := (volume : Measure (Rd d)).measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
    (Homeomorph.measurableEmbedding _)
    (g := fun p : sphere (0 : Rd d) 1 × Ioi (0 : ℝ) =>
      f ((p.2 : ℝ) • (p.1 : Rd d)))
  rw [finrank_euclideanSpace_fin] at hp
  apply hp.mp
  convert hsub using 1
  funext x
  simp only [Function.comp_apply, homeomorphUnitSphereProd_apply_fst_coe,
    homeomorphUnitSphereProd_apply_snd_coe, smul_smul]
  have hx : (x : Rd d) ≠ 0 := by
    intro h0
    exact x.2 (by simp [h0])
  simp [hx]

theorem l2b_integral_polar_sphere (hd : 2 ≤ d) {f : Rd d → ℝ}
    (hfi : Integrable f) :
    (∫ x : Rd d, f x) =
      ((volume : Measure (Rd d)).toSphere univ).toReal *
        ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
          (∫ u : sphere (0 : Rd d) 1, f (r • (u : Rd d)) ∂sphereMeasure d) := by
  have hp := l2b_integrable_polar_prod hd hfi
  rw [l2b_integral_polar_prod hd f, integral_prod_symm _ hp]
  have hinner (r : Ioi (0 : ℝ)) :
      (∫ u : sphere (0 : Rd d) 1, f ((r : ℝ) • (u : Rd d)) ∂
        (volume : Measure (Rd d)).toSphere) =
      ((volume : Measure (Rd d)).toSphere univ).toReal *
        (∫ u : sphere (0 : Rd d) 1, f ((r : ℝ) • (u : Rd d)) ∂sphereMeasure d) := by
    calc
      _ = ∫ u : sphere (0 : Rd d) 1, f ((r : ℝ) • (u : Rd d)) ∂
          (((volume : Measure (Rd d)).toSphere univ) • sphereMeasure d) :=
            congrArg (fun μ : Measure (sphere (0 : Rd d) 1) =>
              ∫ u, f ((r : ℝ) • (u : Rd d)) ∂μ) (l2b_toSphere_eq_smul_sphereMeasure hd)
      _ = _ := by rw [integral_smul_measure, smul_eq_mul]
  simp_rw [hinner]
  rw [← integral_const_mul]
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul]
  · simp only [NNReal.smul_def]
    have hconv :
        (∫ r : Ioi (0 : ℝ),
            ((r : ℝ) ^ (d - 1)).toNNReal *
              (((volume : Measure (Rd d)).toSphere univ).toReal *
                ∫ u : sphere (0 : Rd d) 1, f ((r : ℝ) • (u : Rd d)) ∂sphereMeasure d)
              ∂Measure.comap Subtype.val volume) =
          ∫ r : Ioi (0 : ℝ),
            (r : ℝ) ^ (d - 1) *
              (((volume : Measure (Rd d)).toSphere univ).toReal *
                ∫ u : sphere (0 : Rd d) 1, f ((r : ℝ) • (u : Rd d)) ∂sphereMeasure d)
              ∂Measure.comap Subtype.val volume := by
      apply integral_congr_ae
      filter_upwards [] with r
      rw [Real.coe_toNNReal _ (pow_nonneg r.2.le _)]
    change (∫ r : Ioi (0 : ℝ),
            ((r : ℝ) ^ (d - 1)).toNNReal *
              (((volume : Measure (Rd d)).toSphere univ).toReal *
                ∫ u : sphere (0 : Rd d) 1, f ((r : ℝ) • (u : Rd d)) ∂sphereMeasure d)
              ∂Measure.comap Subtype.val volume) = _
    rw [hconv]
    let g : ℝ → ℝ := fun a => a ^ (d - 1) *
      (((volume : Measure (Rd d)).toSphere univ).toReal *
        ∫ u : sphere (0 : Rd d) 1, f (a • (u : Rd d)) ∂sphereMeasure d)
    calc
      (∫ r : Ioi (0 : ℝ), g r ∂Measure.comap Subtype.val volume) =
          ∫ a in Ioi (0 : ℝ), g a := integral_subtype_comap measurableSet_Ioi g
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        dsimp [g]
        ring
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

end HigherDimLQGMetric
