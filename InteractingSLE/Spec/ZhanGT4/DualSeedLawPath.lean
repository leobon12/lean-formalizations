/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.Assembly3Cont

/-!
# Capacity-coordinate image paths with seeds

Packet PROVE-ZHAN-GT4-A22. Initial force positions may equal the driver.
The geometric input is deterministic: order, positive-time separation,
entrance integrability and the integrated force equations. The stochastic
input is Brownianity of the actual compensated driver, not an image law.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open Sec2 Sec2.Assembly2

/-- The noise determined by the capacity-coordinate image driver and its
force coordinates. Its Brownianity is precisely the remaining stochastic
(D10) and capacity-time-change input. -/
def seedCapacityNoise {nL nR : ℕ} (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  (w t - (∑ i, ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal)) -
    (∑ j, ∫ s in (0 : ℝ)..t, ρR j / (w s.toNNReal - vR j s.toNNReal))) / Real.sqrt κ

/-- Deterministic geometry and force equations for a seeded image path.
The zero-time word may contain seeds; strict separation is required only
at positive times. No stochastic driving equation is assumed. -/
structure SeedImageGeometry {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ)
    (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (T : ℝ≥0) : Prop where
  w_zero : w 0 = 0
  left_zero : ∀ i, vL i 0 = xL i
  right_zero : ∀ j, vR j 0 = xR j
  continuous_w : Continuous w
  continuous_left : ∀ i, Continuous (vL i)
  continuous_right : ∀ j, Continuous (vR j)
  order_left : ∀ t ≤ T, Antitone fun i => vL i t
  order_right : ∀ t ≤ T, Monotone fun j => vR j t
  left_le : ∀ t ≤ T, ∀ i, vL i t ≤ w t
  right_ge : ∀ t ≤ T, ∀ j, w t ≤ vR j t
  left_lt : ∀ t, 0 < t → t ≤ T → ∀ i, vL i t < w t
  right_gt : ∀ t, 0 < t → t ≤ T → ∀ j, w t < vR j t
  integrable_left : ∀ t ≤ T, ∀ i,
    IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vL i s.toNNReal)⁻¹) volume 0 t
  integrable_right : ∀ t ≤ T, ∀ j,
    IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vR j s.toNNReal)⁻¹) volume 0 t
  force_left : ∀ t ≤ T, ∀ i,
    vL i t = xL i + ∫ s in (0 : ℝ)..t, 2 / (vL i s.toNNReal - w s.toNNReal)
  force_right : ∀ t ≤ T, ∀ j,
    vR j t = xR j + ∫ s in (0 : ℝ)..t, 2 / (vR j s.toNNReal - w s.toNNReal)
  seed_left : -2 < seedSum xL ρL
  seed_right : -2 < seedSum xR ρR

namespace SeedImageGeometry

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
  {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {T : ℝ≥0}
  (h : SeedImageGeometry xL xR ρL ρR w vL vR T)

include h

/-- The initial threshold test uses the total charge of each seed group;
strict separation discharges it at every positive time. -/
theorem not_threshold {t : ℝ≥0} (ht : t ≤ T) :
    ¬ ForceWord.ThresholdCondition ρL ρR (w t) (fun i => vL i t) (fun j => vR j t) := by
  by_cases hz : t = 0
  · subst t
    simpa only [h.w_zero, h.left_zero, h.right_zero] using
      (not_thr_iff_seedSum xL xR ρL ρR).2 ⟨h.seed_left, h.seed_right⟩
  · have hp : 0 < t := lt_of_le_of_ne (zero_le (a := t)) (Ne.symm hz)
    unfold ForceWord.ThresholdCondition
    rw [Finset.filter_false_of_mem (fun i _ => (h.left_lt t hp ht i).ne),
      Finset.filter_false_of_mem (fun j _ => (h.right_gt t hp ht j).ne'), Finset.sum_empty]
    norm_num

omit h in
/-- A seed can collide at time zero without violating the collision-null
condition in Definition 2.1. -/
theorem collision_null {v : ℝ≥0 → ℝ}
    (hne : ∀ t, 0 < t → t ≤ T → w t ≠ v t) :
    volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < T ∧ w s.toNNReal = v s.toNNReal} = 0 := by
  apply measure_mono_null (t := ({0} : Set ℝ)) ?_ (measure_singleton 0)
  intro s hs
  apply Set.mem_singleton_iff.2
  by_contra hz
  have hp : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hz)
  have ht : s.toNNReal ≤ T := le_of_lt (by exact_mod_cast hs.2.1)
  exact hne _ (Real.toNNReal_pos.2 hp) ht hs.2.2

/-- The deterministic image equations, with the actual compensated noise,
satisfy the local integrated path definition including its seeded entrance. -/
theorem isSLEPathUpTo {κ : ℝ} (hκ : 0 < κ) :
    IsSLEPathUpTo κ xL xR ρL ρR w vL vR (seedCapacityNoise κ ρL ρR w vL vR) T := by
  have hlt {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) : t ≤ T := le_of_lt (by exact_mod_cast ht)
  refine
    { w_zero := h.w_zero
      vL_zero := h.left_zero
      vR_zero := h.right_zero
      continuousOn_w := h.continuous_w.continuousOn
      continuousOn_vL := fun i => (h.continuous_left i).continuousOn
      continuousOn_vR := fun j => (h.continuous_right j).continuousOn
      antitone_vL := fun ht => h.order_left _ (hlt ht)
      monotone_vR := fun ht => h.order_right _ (hlt ht)
      vL_le_w := fun ht => h.left_le _ (hlt ht)
      w_le_vR := fun ht => h.right_ge _ (hlt ht)
      integrable_gapL := fun ht => h.integrable_left _ (hlt ht)
      integrable_gapR := fun ht => h.integrable_right _ (hlt ht)
      w_eq := fun ht => ?_
      vL_eq := fun ht => h.force_left _ (hlt ht)
      vR_eq := fun ht => h.force_right _ (hlt ht)
      volume_collisionL := fun i => SeedImageGeometry.collision_null (fun t hp ht => (h.left_lt t hp ht i).ne')
      volume_collisionR := fun j => SeedImageGeometry.collision_null (fun t hp ht => (h.right_gt t hp ht j).ne)
      not_threshold := fun ht => h.not_threshold (hlt ht) }
  unfold seedCapacityNoise
  rw [mul_div_cancel₀ _ (Real.sqrt_pos.2 hκ).ne']
  ring

/-- The word at a positive stopping horizon is good even though the
initial word had seeds. This supplies the landed continuation theorem. -/
theorem goodWord (hT : 0 < T) :
    GoodWord ρL ρR (fun i => vL i T - w T, fun j => vR j T - w T) := by
  refine ⟨fun i j => sub_lt_sub_right ((h.left_lt T hT le_rfl i).trans
    (h.right_gt T hT le_rfl j)) _,
    ⟨fun i j hij => sub_le_sub_right (h.order_left T le_rfl hij) _,
      fun i => sub_nonpos.2 (h.left_le T le_rfl i),
      fun i j hij => sub_le_sub_right (h.order_right T le_rfl hij) _,
      fun j => sub_nonneg.2 (h.right_ge T le_rfl j)⟩, ?_⟩
  exact (thresholdCondition_sub_self_iff _ _ _).not.2 (h.not_threshold le_rfl)

end SeedImageGeometry

end InteractingSLE.ZhanGT4
