import QuantumZipper.Proofs.GFF.K3.MixedM5Lip

/-!
# M6 preparation: the annulus data in terms of `neumannH`

Blueprint: `blueprint/GFF_K3_BLUEPRINT.md`, §3.M (M5 "Universality", M6).

* `annProfile_eq`: `annProfile s s' u = log max(s', √u) − log max(s, √u)`.
* `annulusPot_eq_integral_neumannH`: the annulus potential is the difference of the
  `neumannH`-potentials of two concentric folded circles:
  `ã_{z,s,s'}(y) = ∫ neumannH(·, y) d fold_{z,s} − ∫ neumannH(·, y) d fold_{z,s'}`
  (mean value property `integral_neumannH_foldedCircle`).
* `inner_annulusFeat_eq_integral_annulusPot`: the annulus Gram matrix of a local problem is
  `⟪A_{z,s,s'}, A_{w,t,t'}⟫ = ∫ ã_{z,s,s'} d(fold_{w,t} − fold_{w,t'})`, hence (by the previous
  item) the explicit `kernelCov2 neumannH` Gram of the free field: the Gram matrix and the
  pairings `⟪v_μ, A⟫ = ∫ ã dμ` are universal (blueprint M5 "Universality").

Own elementary computations (cost rule).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Real Topology ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace QuantumZipper.K3

theorem integral_annIntegrand_of_mem {s s' a b : ℝ} (hs : 0 < s) (hsa : s ^ 2 ≤ a) (hab : a ≤ b)
    (hbs : b ≤ s' ^ 2) :
    ∫ t in a..b, -((Ioo (s ^ 2) (s' ^ 2)).indicator 1 t) / (2 * t) =
      -(1 / 2) * Real.log (b / a) := by
  have ha : 0 < a := lt_of_lt_of_le (by positivity) hsa
  have hae : ∀ᵐ t : ℝ, t ≠ s' ^ 2 := by
    rw [ae_iff]; simp
  rw [intervalIntegral.integral_congr_ae (g := fun t => -(1 / 2) * t⁻¹) ?_,
    intervalIntegral.integral_const_mul, integral_inv_of_pos ha (ha.trans_le hab)]
  filter_upwards [hae] with t ht htab
  rw [uIoc_of_le hab] at htab
  have hmem : t ∈ Ioo (s ^ 2) (s' ^ 2) :=
    ⟨lt_of_le_of_lt hsa htab.1, lt_of_le_of_ne (htab.2.trans hbs) ht⟩
  have ht0 : t ≠ 0 := (ha.trans htab.1).ne'
  rw [indicator_of_mem hmem, Pi.one_apply]
  field_simp

theorem integral_annIntegrand_zero {s s' a b : ℝ} (h : ∀ t ∈ uIcc a b, t ∉ Ioo (s ^ 2) (s' ^ 2)) :
    ∫ t in a..b, -((Ioo (s ^ 2) (s' ^ 2)).indicator 1 t) / (2 * t) = 0 := by
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t ht => ?_),
    intervalIntegral.integral_zero]
  simp [indicator_of_notMem (h t ht)]

theorem intervalIntegrable_annIntegrand {s s' : ℝ} (hs : 0 < s) (a b : ℝ) :
    IntervalIntegrable (fun t => -((Ioo (s ^ 2) (s' ^ 2)).indicator (1 : ℝ → ℝ) t) / (2 * t))
      volume a b := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hm : Measurable fun t : ℝ => -((Ioo (s ^ 2) (s' ^ 2)).indicator (1 : ℝ → ℝ) t) / (2 * t) :=
    ((measurable_const.indicator measurableSet_Ioo).neg).div (measurable_const.mul measurable_id)
  refine (Measure.integrableOn_of_bounded (M := (2 * s ^ 2)⁻¹) (by simp)
    hm.aestronglyMeasurable (Eventually.of_forall fun t => ?_)).intervalIntegrable
  refine norm_neg_div_two_mul_le hs2 ?_ ?_
  · by_cases h : t ∈ Ioo (s ^ 2) (s' ^ 2) <;> simp [h]
  · intro ht
    rw [indicator_of_notMem (fun h => absurd h.1 (not_lt.mpr ht))]

/-- The annulus profile in closed form. -/
theorem annProfile_eq {s s' : ℝ} (hs : 0 < s) (hss' : s < s') {u : ℝ} (hu : 0 ≤ u) :
    annProfile s s' u = Real.log (max s' (Real.sqrt u)) - Real.log (max s (Real.sqrt u)) := by
  unfold annProfile
  have hs2 : s ^ 2 < s' ^ 2 := by nlinarith
  have hsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu
  rcases le_or_gt (s' ^ 2) u with h1 | h1
  · -- `u ≥ s'²`
    have hsu : s' ≤ Real.sqrt u := by
      rw [← Real.sqrt_sq (by linarith : 0 ≤ s')]; exact Real.sqrt_le_sqrt h1
    rw [integral_annIntegrand_zero (fun t ht h => ?_), max_eq_right hsu,
      max_eq_right (by linarith), sub_self]
    rw [uIcc_of_le h1] at ht
    exact absurd h.2 (not_lt.mpr ht.1)
  rcases le_or_gt (s ^ 2) u with h2 | h2
  · -- `s² ≤ u < s'²`
    have hsu : s ≤ Real.sqrt u := by
      rw [← Real.sqrt_sq hs.le]; exact Real.sqrt_le_sqrt h2
    have hus : Real.sqrt u < s' := by
      rw [← Real.sqrt_sq (by linarith : 0 ≤ s')]
      exact Real.sqrt_lt_sqrt hu h1
    have hu0 : 0 < u := lt_of_lt_of_le (by positivity) h2
    rw [intervalIntegral.integral_symm, integral_annIntegrand_of_mem hs h2 h1.le le_rfl,
      max_eq_left hus.le, max_eq_right hsu, Real.log_sqrt hu,
      Real.log_div (pow_pos (hs.trans hss') 2).ne' hu0.ne', Real.log_pow]
    push_cast; ring
  · -- `u < s²`
    have hus : Real.sqrt u < s := by
      rw [← Real.sqrt_sq hs.le]; exact Real.sqrt_lt_sqrt hu h2
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := s ^ 2)
      (intervalIntegrable_annIntegrand hs _ _) (intervalIntegrable_annIntegrand hs _ _),
      integral_annIntegrand_zero (a := s ^ 2) (b := u) (fun t ht h => ?_), add_zero,
      intervalIntegral.integral_symm, integral_annIntegrand_of_mem hs le_rfl hs2.le le_rfl,
      max_eq_left (hus.trans hss').le, max_eq_left hus.le,
      Real.log_div (pow_pos (hs.trans hss') 2).ne' (pow_pos hs 2).ne', Real.log_pow, Real.log_pow]
    · push_cast; ring
    · rw [uIcc_of_ge h2.le] at ht
      exact absurd h.1 (not_lt.mpr ht.2)

/-- **Universality of the pairings.** The annulus potential is the difference of the
`neumannH`-potentials of two concentric folded circles. -/
theorem annulusPot_eq_integral_neumannH (z y : ℂ) {s s' : ℝ} (hs : 0 < s) (hss' : s < s') :
    annulusPot z s s' y =
      (∫ x, neumannH x y ∂(foldedCircle z s)) - ∫ x, neumannH x y ∂(foldedCircle z s') := by
  rw [integral_neumannH_foldedCircle z y hs, integral_neumannH_foldedCircle z y (hs.trans hss'),
    annulusPot, annProfile_eq hs hss' (sq_nonneg _), annProfile_eq hs hss' (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _), norm_sub_rev y z,
    norm_sub_conj_comm y z]
  ring

end QuantumZipper.K3
