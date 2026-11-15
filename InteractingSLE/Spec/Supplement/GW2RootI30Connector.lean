/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootH29Arc

/-!
# A zero-based carrier for a low-arc trace

Packet PROVE-T14-GW2ROOT2. Adjoining the untouched real connector gives
a path from zero with the same upper-half-plane points. Its inversion
misses the retained trace by precisely the cover's arc inequality and
the original trace separation.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootI30

/-- Prepending the real connector changes no interior points of the path. -/
theorem exists_zero_carrier {α γ : ℝ≥0 → ℂ} {s v : ℝ≥0} {x : ℝ}
    (hx : 0 ≤ x) (hv : 0 < v) (hγ : ContinuousOn γ (Icc 0 v))
    (hγ0 : γ 0 = x) (hγH : MapsTo γ (Icc 0 v) Hbar)
    (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1)
    (hsep : Disjoint (α '' Icc 0 s)
      ((fun z : ℂ => -z⁻¹) '' (γ '' Icc 0 v \ {0}))) :
    ∃ δ : ℝ≥0 → ℂ, ContinuousOn δ (Icc 0 1) ∧ δ 0 = 0 ∧
      MapsTo δ (Icc 0 1) Hbar ∧
      δ '' Icc 0 1 ∩ H = γ '' Icc 0 v ∩ H ∧
      Disjoint (α '' Icc 0 s)
        ((fun z : ℂ => -z⁻¹) '' (δ '' Icc 0 1 \ {0})) := by
  let A : Path (0 : ℂ) (x : ℂ) :=
    { toFun := fun r => ((r.val * x : ℝ) : ℂ)
      continuous_toFun := Complex.continuous_ofReal.comp
        (continuous_subtype_val.mul continuous_const)
      source' := by change ((0 * x : ℝ) : ℂ) = 0; rw [zero_mul, ofReal_zero]
      target' := by change ((1 * x : ℝ) : ℂ) = x; rw [one_mul] }
  have hpar : ∀ r : unitInterval, r.val.toNNReal * v ∈ Icc 0 v := fun r =>
    ⟨zero_le, mul_le_of_le_one_left (zero_le : (0 : ℝ≥0) ≤ v)
      (Real.toNNReal_le_one.mpr r.2.2)⟩
  let B : Path (x : ℂ) (γ v) :=
    { toFun := fun r => γ (r.val.toNNReal * v)
      continuous_toFun := hγ.comp_continuous
        ((continuous_real_toNNReal.comp continuous_subtype_val).mul continuous_const) hpar
      source' := by change γ ((0 : ℝ).toNNReal * v) = x
                    rw [Real.toNNReal_zero, zero_mul, hγ0]
      target' := by change γ ((1 : ℝ).toNNReal * v) = γ v
                    rw [Real.toNNReal_one, one_mul] }
  let C := A.trans B
  let δ : ℝ≥0 → ℂ := fun t => C.extend t
  have hδrange : δ '' Icc 0 1 = range C := by
    apply Subset.antisymm
    · rintro z ⟨t, _, rfl⟩
      rw [← C.extend_range]
      exact mem_range_self _
    · rintro z ⟨r, rfl⟩
      refine ⟨r.val.toNNReal, ⟨zero_le, Real.toNNReal_le_one.mpr r.2.2⟩, ?_⟩
      change C.extend (r.val.toNNReal : ℝ) = C r
      rw [Real.coe_toNNReal _ r.2.1]
      exact C.extend_extends' r
  have hBrange : range B = γ '' Icc 0 v := by
    apply Subset.antisymm
    · rintro z ⟨r, rfl⟩
      exact ⟨_, hpar r, rfl⟩
    · rintro z ⟨t, ht, rfl⟩
      let r : unitInterval := ⟨(t / v : ℝ≥0), by
        exact ⟨(t / v).coe_nonneg, by exact_mod_cast (div_le_one₀ hv).mpr ht.2⟩⟩
      refine ⟨r, ?_⟩
      change γ (Real.toNNReal ((t / v : ℝ≥0) : ℝ) * v) = γ t
      rw [Real.toNNReal_coe, div_mul_cancel₀ _ hv.ne']
  have hδset : δ '' Icc 0 1 = range A ∪ γ '' Icc 0 v := by
    rw [hδrange, Path.trans_range, hBrange]
  have hAH : ∀ z ∈ range A, z ∈ Hbar ∧ z ∉ H := by
    rintro _ ⟨r, rfl⟩
    constructor
    · change 0 ≤ (((r.val * x : ℝ) : ℂ)).im
      rw [ofReal_im]
    · change ¬0 < (((r.val * x : ℝ) : ℂ)).im
      rw [ofReal_im]
      exact lt_irrefl _
  refine ⟨δ, (C.continuous_extend.comp NNReal.continuous_coe).continuousOn,
    C.extend_zero, ?_, ?_, ?_⟩
  · intro t ht
    rcases hδset ▸ mem_image_of_mem δ ht with hz | ⟨q, hq, heq⟩
    · exact (hAH _ hz).1
    · exact heq ▸ hγH hq
  · rw [hδset, union_inter_distrib_right]
    have hempty : range A ∩ H = ∅ := eq_empty_iff_forall_notMem.mpr
      fun z hz => (hAH z hz.1).2 hz.2
    rw [hempty, empty_union]
  · apply disjoint_left.mpr
    rintro _ hα ⟨z, ⟨hz, hn⟩, rfl⟩
    rw [hδset] at hz
    rcases hz with ⟨r, rfl⟩ | hz
    · obtain ⟨u, hu, heq⟩ := hα
      have hne := RootH29.real_arc_mul_add_one_ne_zero
        (mul_nonneg r.2.1 hx) (mul_le_of_le_one_left hx r.2.2) (harc u hu)
      apply hne
      change α u = -(((r.val * x : ℝ) : ℂ))⁻¹ at heq
      change ((r.val * x : ℝ) : ℂ) ≠ 0 at hn
      rw [heq, mul_neg, mul_inv_cancel₀ hn, neg_add_cancel]
    · exact disjoint_left.mp hsep hα ⟨z, ⟨hz, hn⟩, rfl⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootI30
