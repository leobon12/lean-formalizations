/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootR18Safe

/-!
# Boundary-root paths stay outside the retained counterflow hull

Packet PROVE-T14-GW2ROOT2. Prepend the untouched real arc from zero to
the positive root, then reuse the landed no-entry theorem for paths
from zero. Thus trace separation implies safety for the whole closed
retained hull, including real visits of a switched path.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootH29

open Supp8.GB6 Supp8.GB6.CoordB

/-- The cover's arc bound excludes every inversion contact on the
entire real connector, rather than only at its right endpoint. -/
theorem real_arc_mul_add_one_ne_zero {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x)
    {a : ℂ} (ha : x * ‖a‖ < 1) : (y : ℂ) * a + 1 ≠ 0 := by
  have hn : ‖(y : ℂ) * a‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy]
    exact (mul_le_mul_of_nonneg_right hyx (norm_nonneg a)).trans_lt ha
  intro he
  have hm : (y : ℂ) * a = -1 := eq_neg_of_add_eq_zero_left he
  rw [hm, norm_neg, norm_one] at hn
  exact (lt_irrefl (1 : ℝ)) hn

/-- A continuous path from a nonnegative real root is safe in the
retained chart whenever its trace is disjoint and the connector arc
satisfies the cover's bound. No closed-hull avoidance is assumed. -/
theorem path_mem_relSafe_of_real_arc {w : ℝ≥0 → ℝ} {T : ℝ≥0∞}
    {α γ : ℝ≥0 → ℂ} (hα : IsGeneratingTrace w T α)
    (hw : Continuous w) (hw0 : w 0 = 0) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < T)
    {x : ℝ} (hx : 0 ≤ x) {v : ℝ≥0} (hγ : ContinuousOn γ (Icc 0 v))
    (hγ0 : γ 0 = x) (hγH : MapsTo γ (Icc 0 v) Hbar)
    (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1)
    (hsep : Disjoint (α '' Icc 0 s)
      ((fun z : ℂ => -z⁻¹) '' (γ '' Icc 0 v \ {0}))) :
    MapsTo γ (Icc 0 v) (relSafe (Ito.rpath w) s) := by
  intro t ht
  let A : Path (0 : ℂ) (x : ℂ) :=
    { toFun := fun r => ((r.val * x : ℝ) : ℂ)
      continuous_toFun := Complex.continuous_ofReal.comp
        (continuous_subtype_val.mul continuous_const)
      source' := by change ((0 * x : ℝ) : ℂ) = 0; rw [zero_mul, ofReal_zero]
      target' := by change ((1 * x : ℝ) : ℂ) = x; rw [one_mul] }
  have hpar : ∀ r : unitInterval, (r.val.toNNReal * t) ∈ Icc 0 v := by
    intro r
    exact ⟨zero_le, (mul_le_of_le_one_left (zero_le : (0 : ℝ≥0) ≤ t)
      (Real.toNNReal_le_one.mpr r.2.2)).trans ht.2⟩
  let B : Path (x : ℂ) (γ t) :=
    { toFun := fun r => γ (r.val.toNNReal * t)
      continuous_toFun := hγ.comp_continuous
        ((continuous_real_toNNReal.comp continuous_subtype_val).mul continuous_const) hpar
      source' := by change γ ((0 : ℝ).toNNReal * t) = x
                    rw [Real.toNNReal_zero, zero_mul, hγ0]
      target' := by change γ ((1 : ℝ).toNNReal * t) = γ t
                    rw [Real.toNNReal_one, one_mul] }
  let C := A.trans B
  have hC : ∀ z ∈ range C, z ∈ Hbar ∧
      (z ≠ 0 → -z⁻¹ ∉ α '' Icc 0 s) := by
    intro z hz
    rw [Path.trans_range] at hz
    rcases hz with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · have hy : 0 ≤ r.val * x := mul_nonneg r.2.1 hx
      have hyx : r.val * x ≤ x := mul_le_of_le_one_left hx r.2.2
      refine ⟨by change 0 ≤ (((r.val * x : ℝ) : ℂ)).im; rw [ofReal_im], ?_⟩
      intro hn ⟨u, hu, he⟩
      change ((r.val * x : ℝ) : ℂ) ≠ 0 at hn
      have hne := real_arc_mul_add_one_ne_zero hy hyx (harc u hu)
      apply hne
      change α u = -(((r.val * x : ℝ) : ℂ))⁻¹ at he
      rw [he, mul_neg, mul_inv_cancel₀ hn, neg_add_cancel]
    · refine ⟨hγH (hpar r), ?_⟩
      intro hn hbad
      exact disjoint_left.mp hsep hbad ⟨_, ⟨⟨_, hpar r, rfl⟩, hn⟩, rfl⟩
  have hsub : ∀ q : ℝ≥0, q ∈ Icc 0 1 → C.extend q ∈ range C := by
    intro q _
    rw [← C.extend_range]
    exact mem_range_self _
  have hc : ContinuousOn (fun q : ℝ≥0 => C.extend q) (Icc 0 1) :=
    (C.continuous_extend.comp NNReal.continuous_coe).continuousOn
  have hd : Disjoint (α '' Icc 0 s)
      ((fun z : ℂ => -z⁻¹) '' ((fun q : ℝ≥0 => C.extend q) '' Icc 0 1 \ {0})) := by
    apply disjoint_left.mpr
    rintro _ hαz ⟨z, ⟨⟨q, hq, rfl⟩, hn⟩, rfl⟩
    exact (hC _ (hsub q hq)).2 hn hαz
  have hsafe := RootR18.path_mem_relSafe_of_trace_disjoint hα hw hw0 hs hc
    (C.extend_zero) (fun q hq => (hC _ (hsub q hq)).1) hd
  have hend := hsafe (show (1 : ℝ≥0) ∈ Icc 0 1 from ⟨zero_le, le_rfl⟩)
  simpa only [NNReal.coe_one, Path.extend_one] using hend

end InteractingSLE.Theorem14.GW2TipSystem.RootH29
