/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafDualNRepresentation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # A probability perturbation from an L¹ functional annihilating constants -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

namespace InteractingSLE.WFS

/-- A real L¹ functional annihilating `1` gives a dominated probability measure,
whose expectations are the original expectations plus the normalized functional. -/
theorem exists_probability_of_l1_functional
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Lp ℝ 1 P →L[ℝ] ℝ) (hL : L (Lp.const 1 P (1 : ℝ)) = 0) :
    ∃ Q : Measure Ω, IsProbabilityMeasure Q ∧ Q ≤ (2 : ℝ≥0∞) • P ∧
      ∀ (f : Ω → ℝ) (hf : Integrable f P),
        (∫ x, f x ∂Q) = (∫ x, f x ∂P) + L (hf.toL1 f) / (‖L‖ + 1) := by
  obtain ⟨h, hm, hb, hr⟩ := exists_bounded_l1_representative P L
  let K := ‖L‖ + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hKn : K ≠ 0 := ne_of_gt hK
  let d : Ω → ℝ := fun x => 1 + h x / K
  have hdb : ∀ᵐ x ∂P, 0 ≤ d x ∧ d x ≤ 2 := by
    filter_upwards [hb] with x hx
    have ha := abs_le.1 hx
    constructor
    · dsimp only [d]
      have : -K ≤ h x := by dsimp only [K]; linarith only [ha.1]
      have : (-1 : ℝ) ≤ h x / K := (le_div_iff₀ hK).2 (by simpa only [neg_one_mul] using this)
      linarith only [this]
    · dsimp only [d]
      have : h x ≤ K := by dsimp only [K]; linarith only [ha.2]
      have := (div_le_one hK).2 this
      linarith only [this]
  have hdm : AEStronglyMeasurable d P := aestronglyMeasurable_const.add (by simpa only [div_eq_mul_inv] using hm.mul_const K⁻¹)
  have hi : Integrable h P := (integrable_const (1 : ℝ)).bdd_mul hm hb |>.congr
    (Eventually.of_forall fun x => mul_one (h x))
  have hdi : Integrable d P := (integrable_const (1 : ℝ)).add (hi.div_const K)
  have hh : (∫ x, h x ∂P) = 0 := by
    have he := hr (fun _ => 1) (integrable_const (1 : ℝ))
    simpa only [mul_one, Integrable.toL1, MemLp.toLp_const, hL] using he
  have hd : (∫ x, d x ∂P) = 1 := by
    dsimp only [d]
    rw [integral_add (integrable_const (1 : ℝ)) (hi.div_const K), integral_div,
      hh, zero_div, add_zero, integral_const]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  let Q := P.withDensity (fun x => ENNReal.ofReal (d x))
  have hQ : IsProbabilityMeasure Q := by
    constructor
    change P.withDensity (fun x => ENNReal.ofReal (d x)) univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hdi (hdb.mono fun _ hx => hx.1), hd]
    norm_num
  have hQP : Q ≤ (2 : ℝ≥0∞) • P := by
    rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [hdb] with x hx
    exact (ENNReal.ofReal_le_ofReal hx.2).trans_eq (by norm_num)
  refine ⟨Q, hQ, hQP, fun f hf => ?_⟩
  have hmul : Integrable (fun x => h x * f x) P := hf.bdd_mul hm hb
  calc
    (∫ x, f x ∂Q) = ∫ x, d x * f x ∂P := by
      rw [integral_withDensity_eq_integral_toReal_smul₀ hdm.aemeasurable.ennreal_ofReal
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      filter_upwards [hdb] with x hx
      rw [ENNReal.toReal_ofReal hx.1, smul_eq_mul]
    _ = (∫ x, f x + (h x * f x) / K ∂P) := by
      congr 1
      funext x
      dsimp only [d]
      ring
    _ = (∫ x, f x ∂P) + L (hf.toL1 f) / (‖L‖ + 1) := by
      rw [integral_add hf (hmul.div_const K), integral_div, hr f hf]

end InteractingSLE.WFS
