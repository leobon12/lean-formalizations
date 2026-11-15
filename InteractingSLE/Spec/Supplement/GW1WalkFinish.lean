/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1ParamEvery
import Mathlib.Order.Interval.Set.Monotone

/-!
# GW1: real-record bounds and finite progress

The real-record invariant in R53 D.4 bounds every retained real contact by the current
outward record. It implies clearance of the entire outgoing real ray. Finite progress is
proved by counting the strictly ordered original marks, independently of curve parametrization.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW1WalkFinish

open Exist Exist.Staged Exist.StagedLaw GW1WalkChain GW1Bookkeep

/-- The oriented coordinate, increasing towards the outgoing boundary ray. -/
def sideCoord (right : Bool) (x : ℝ) : ℝ := if right then x else -x

theorem sideCoord_injective (right : Bool) : Function.Injective (sideCoord right) := by
  cases right
  · exact neg_injective
  · exact Function.injective_id

/-- All retained original-real contacts are behind the current outward record. -/
def RealPrefixBound (right : Bool) (root : ℝ) (s : ExplState) : Prop :=
  ∀ x : ℝ, (x : ℂ) ∈ statePhysicalSet root s → sideCoord right x ≤ sideCoord right (stPt s)

theorem realPrefixBound_init (right : Bool) (root : ℝ) :
    RealPrefixBound right root (ExplState.init root) := by
  intro x hx
  have heq : x = root := by
    apply Complex.ofReal_injective
    simpa only [statePhysicalSet, ExplState.init, List.not_mem_nil, iUnion_of_empty,
      iUnion_empty, union_empty, mem_singleton_iff] using hx
  subst x
  exact le_rfl

theorem connectorClearance_ray_of_realPrefixBound {right : Bool} {root : ℝ} {s : ExplState}
    (h : RealPrefixBound right root s) :
    ConnectorClearance root s (range (realRay right (stPt s))) := by
  intro z hz hA
  obtain ⟨t, rfl⟩ := hz
  cases right
  · have hbound := h (stPt s - (t : ℝ)) hA
    change -(stPt s - (t : ℝ)) ≤ -stPt s at hbound
    have ht : (t : ℝ) = 0 := by linarith only [hbound, t.2]
    simp only [realRay, Bool.false_eq_true, ↓reduceIte, ht, sub_zero]
  · have hbound := h (stPt s + (t : ℝ)) hA
    change stPt s + (t : ℝ) ≤ stPt s at hbound
    have ht : (t : ℝ) = 0 := by linarith only [hbound, t.2]
    simp only [realRay, ↓reduceIte, ht, add_zero]

theorem connectorClearance_interval_of_realPrefixBound {right : Bool} {root : ℝ}
    {s : ExplState} (h : RealPrefixBound right root s) (x : ℝ) :
    ConnectorClearance root s (((↑) : ℝ → ℂ) ''
      (if right then Icc (stPt s) x else Icc x (stPt s))) := by
  intro z hz hA
  obtain ⟨y, hy, rfl⟩ := hz
  have hbound := h y hA
  apply congrArg ((↑) : ℝ → ℂ)
  cases right
  · change -y ≤ -stPt s at hbound
    exact le_antisymm (mem_Icc.1 hy).2 (by linarith only [hbound])
  · change y ≤ stPt s at hbound
    exact le_antisymm hbound (mem_Icc.1 hy).1

/-- A finite sequence cannot select more distinct original marks than exist. A live
round selects a strictly later mark, while a finished round stays finished. -/
theorem done_of_finite_progress (J : Finset ℝ) (q : ℕ → ℝ) (done : ℕ → Prop)
    (right : Bool) (hpersist : ∀ n, done n → done (n + 1))
    (hstep : ∀ n ≤ J.card, ¬ done n →
      done (n + 1) ∨ (q (n + 1) ∈ J ∧ sideCoord right (q n) < sideCoord right (q (n + 1)))) :
    done (J.card + 1) := by
  by_contra hlast
  have hnot : ∀ n ≤ J.card + 1, ¬ done n := by
    intro n hn hd
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
    have hdone : ∀ k, done (n + k) := by
      intro k
      induction k with
      | zero => exact hd
      | succ k ih => exact hpersist (n + k) ih
    exact hlast (hm ▸ hdone m)
  have hnext (n : ℕ) (hn : n ≤ J.card) :
      q (n + 1) ∈ J ∧ sideCoord right (q n) < sideCoord right (q (n + 1)) :=
    (hstep n hn (hnot n (by omega))).resolve_left (hnot (n + 1) (by omega))
  have hmono : StrictMonoOn (fun n => sideCoord right (q n)) (Iic (J.card + 1)) :=
    strictMonoOn_Iic_of_lt_succ (fun n hn => (hnext n (by omega)).2)
  have hinj : Function.Injective (fun i : Fin (J.card + 1) => q (i.val + 1)) := by
    intro i j hij
    apply Fin.ext
    have heq : i.val + 1 = j.val + 1 := hmono.injOn
      (mem_Iic.2 (by omega)) (mem_Iic.2 (by omega)) (congrArg (sideCoord right) hij)
    omega
  let f : Fin (J.card + 1) → J := fun i => ⟨q (i.val + 1), (hnext i.val (by omega)).1⟩
  have hf : Function.Injective f := fun i j hij => hinj (congrArg Subtype.val hij)
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin, Fintype.card_coe] at hcard
  omega

end InteractingSLE.Theorem14.GW1WalkFinish
