/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6CoordBReadout
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurable separation of physical GB6 prefixes

Inversion contact is detected without putting a measurable metric on the
Riemann sphere: the two physical points meet precisely when `z*w+1=0`.
The compact-prefix minimum is measurable by Mathlib's semicontinuous
infimum theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.SourceC

/-- The algebraic contact test includes the zero/infinity cases exactly. -/
theorem sphereInv_eq_iff (z w : ℂ) :
    sphereInv (z : OnePoint ℂ) = (w : OnePoint ℂ) ↔ z * w + 1 = 0 := by
  by_cases hz : z = 0
  · subst z
    simp only [sphereInv_coe, ↓reduceIte, zero_mul, zero_add, one_ne_zero, iff_false]
    exact OnePoint.infty_ne_coe w
  · rw [sphereInv_coe_of_ne hz, OnePoint.coe_eq_coe]
    constructor
    · intro h
      rw [← h]
      field_simp
      ring
    · intro h
      apply (mul_left_cancel₀ hz)
      field_simp
      linear_combination -h

/-- A measurable compact-prefix separation quantity in the two physical charts. -/
def prefixGap (γ α : ℝ≥0 → ℂ) (T s : ℝ≥0) : ℝ≥0∞ :=
  ⨅ p : (Icc 0 T) × (Icc 0 s), ENNReal.ofReal ‖γ p.1.val * α p.2.val + 1‖

/-- The compact minimum is positive exactly when no inversion contact occurs. -/
theorem prefixGap_pos_iff {γ α : ℝ≥0 → ℂ} (hγ : Continuous γ) (hα : Continuous α) (T s : ℝ≥0) :
    0 < prefixGap γ α T s ↔ ∀ t ∈ Icc 0 T, ∀ u ∈ Icc 0 s, γ t * α u + 1 ≠ 0 := by
  let K : Set (ℝ≥0 × ℝ≥0) := Icc 0 T ×ˢ Icc 0 s
  let f : ℝ≥0 × ℝ≥0 → ℝ≥0∞ := fun p => ENNReal.ofReal ‖γ p.1 * α p.2 + 1‖
  have hc : Continuous f := ENNReal.continuous_ofReal.comp
    (((hγ.comp continuous_fst).mul (hα.comp continuous_snd)).add_const 1).norm
  constructor
  · intro hp t ht u hu
    have hle : prefixGap γ α T s ≤ ENNReal.ofReal ‖γ t * α u + 1‖ :=
      iInf_le (fun p : (Icc 0 T) × (Icc 0 s) => ENNReal.ofReal ‖γ p.1.val * α p.2.val + 1‖)
        (⟨t, ht⟩, ⟨u, hu⟩)
    exact norm_pos_iff.1 (ENNReal.ofReal_pos.1 (hp.trans_le hle))
  · intro h
    obtain ⟨p, hp, hmin⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMinOn
      (show K.Nonempty from ⟨(0, 0), ⟨⟨le_rfl, zero_le⟩, ⟨le_rfl, zero_le⟩⟩⟩) hc.continuousOn
    have hpos : 0 < f p := ENNReal.ofReal_pos.2 (norm_pos_iff.2 (h p.1 hp.1 p.2 hp.2))
    have hle : f p ≤ prefixGap γ α T s := by
      apply le_iInf
      intro q
      exact hmin (show (q.1.val, q.2.val) ∈ K from ⟨q.1.property, q.2.property⟩)
    exact hpos.trans_le hle

/-- Strictly before contact iff the two compact physical prefixes are separated. -/
theorem lt_firstContactTime_iff {γ α : ℝ≥0 → ℂ} (hγ : Continuous γ) (hα : Continuous α) (T s : ℝ≥0) :
    (T : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) ↔ 0 < prefixGap γ α T s := by
  rw [prefixGap_pos_iff hγ hα]
  constructor
  · intro hT t ht u hu hzero
    have htT : (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) := (ENNReal.coe_le_coe.2 ht.2).trans_lt hT
    exact notMem_of_lt_firstContactTime htT ⟨u, hu, ((sphereInv_eq_iff _ _).2 hzero).symm⟩
  · intro hsep
    by_contra hn
    have hle := le_of_not_gt hn
    have hfin := hle.trans_lt (ENNReal.coe_lt_top (r := T))
    let q := (firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)).toNNReal
    have hq : firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) = (q : ℝ≥0∞) := (ENNReal.coe_toNNReal hfin.ne).symm
    have hAc : IsCompact ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) :=
      isCompact_Icc.image (OnePoint.continuous_coe.comp hα)
    obtain ⟨u, hu, he⟩ := firstContactTime_mem
      (continuous_sphereInv.comp (OnePoint.continuous_coe.comp hγ)) hAc.isClosed hq
    exact hsep q ⟨zero_le, ENNReal.coe_le_coe.1 (hq ▸ hle)⟩ u hu
      ((sphereInv_eq_iff _ _).1 he.symm)

variable {Ω : Type*} [MeasurableSpace Ω] {γ α : Ω → ℝ≥0 → ℂ}

/-- Compact-prefix separation is measurable from fixed-time curve evaluations. -/
theorem measurable_prefixGap (hγc : ∀ ω, Continuous (γ ω)) (hαc : ∀ ω, Continuous (α ω))
    (hγm : ∀ t, Measurable fun ω => γ ω t) (hαm : ∀ t, Measurable fun ω => α ω t) (T s : ℝ≥0) :
    Measurable fun ω => prefixGap (γ ω) (α ω) T s := by
  have hm : Measurable (⨅ p : (Icc 0 T) × (Icc 0 s),
      fun ω => ENNReal.ofReal ‖γ ω p.1.val * α ω p.2.val + 1‖) := by
    apply measurable_iInf_of_upperSemicontinuous
      (fun p : (Icc 0 T) × (Icc 0 s) => ENNReal.measurable_ofReal.comp
        (((hγm p.1.val).mul (hαm p.2.val)).add_const 1).norm)
    intro ω
    apply Continuous.upperSemicontinuous
    exact ENNReal.continuous_ofReal.comp
      ((((hγc ω).comp (continuous_subtype_val.comp continuous_fst)).mul
        ((hαc ω).comp (continuous_subtype_val.comp continuous_snd))).add_const 1).norm
  have he : (⨅ p : (Icc 0 T) × (Icc 0 s),
      fun ω => ENNReal.ofReal ‖γ ω p.1.val * α ω p.2.val + 1‖) =
      (fun ω => prefixGap (γ ω) (α ω) T s) := by
    funext ω
    exact iInf_apply
  rwa [he] at hm

/-- The events used for the rational physical-prefix atlas are measurable. -/
theorem measurableSet_lt_firstContactTime (hγc : ∀ ω, Continuous (γ ω)) (hαc : ∀ ω, Continuous (α ω))
    (hγm : ∀ t, Measurable fun ω => γ ω t) (hαm : ∀ t, Measurable fun ω => α ω t) (T s : ℝ≥0) :
    MeasurableSet {ω | (T : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
      ((fun u => (α ω u : OnePoint ℂ)) '' Icc 0 s)} := by
  simp_rw [lt_firstContactTime_iff (hγc _) (hαc _)]
  exact measurableSet_lt measurable_const (measurable_prefixGap hγc hαc hγm hαm T s)

end InteractingSLE.Supp8.GB6.SourceC
