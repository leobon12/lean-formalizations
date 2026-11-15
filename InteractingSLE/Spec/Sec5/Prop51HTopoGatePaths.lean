/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HTopoGateCrosscut
import InteractingSLE.Spec.Sec5.Prop51HTopoAccessCrossing
import Mathlib.Data.Set.Card

/-!
# Exit paths with the least number of crossed excursions

All exit paths have a finite nonempty crossed-excursion family. Choose a path
minimizing its natural cardinality. A geometric bypass crossing a strict subset
of that family would contradict minimality. This completes the finite descent
argument; constructing the bypass is a separate planar obligation.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Bornology Metric
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Prop51HTopo

open WangWu hiding ratPt exists_ratPt_dist_lt

/-- An actual compact half-plane path from the gate point to the outer face.
No condition on its crossings is included as a premise. -/
structure GateExitPath {η : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ}
    (c : PositiveGateComponent η w s) where
  curve : ℝ → ℂ
  continuous : ContinuousOn curve (Icc 0 1)
  in_H : MapsTo curve (Icc 0 1) H
  start : curve 0 = c.point
  finish : curve 1 ∈ outerChartFace η w s

variable {η : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ} {c : PositiveGateComponent η w s}

theorem PositiveGateComponent.domain_subset_fillH (c : PositiveGateComponent η w s) :
    c.domain ⊆ fillH (chartFlowSet η w s) := by
  intro z hz
  refine ⟨(c.domain_subset hz).1, Or.inr ?_⟩
  rw [← connectedComponentIn_eq hz]
  exact c.bounded

theorem GateExitPath.finish_notMem_domain (p : GateExitPath c) : p.curve 1 ∉ c.domain :=
  fun h => p.finish.2 (c.domain_subset_fillH h)

/-- The actual time components of the excursions crossed by this path. -/
def GateExitPath.crossed (p : GateExitPath c) : Set (Set ℝ) :=
  (fun t => connectedComponentIn (excursionTimes η w s) t) ''
    (Ici 0 ∩ η ⁻¹' (revChartInv w s '' (p.curve '' Icc 0 1)))

theorem GateExitPath.finite_crossed (p : GateExitPath c) (hη : IsProperArc η)
    (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) : p.crossed.Finite :=
  (c.finite_nonempty_crossed_excursions hη hw hw0 hs
    p.continuous p.in_H p.start p.finish_notMem_domain).1

theorem GateExitPath.nonempty_crossed (p : GateExitPath c) (hη : IsProperArc η)
    (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) : p.crossed.Nonempty :=
  (c.finite_nonempty_crossed_excursions hη hw hw0 hs
    p.continuous p.in_H p.start p.finish_notMem_domain).2

theorem GateExitPath.ncard_crossed_pos (p : GateExitPath c) (hη : IsProperArc η)
    (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) : 0 < p.crossed.ncard :=
  (p.nonempty_crossed hη hw hw0 hs).ncard_pos (p.finite_crossed hη hw hw0 hs)

theorem PositiveGateComponent.exists_gateExitPath (c : PositiveGateComponent η w s)
    (hb : IsBounded (chartFlowSet η w s)) :
    Nonempty (GateExitPath c) := by
  obtain ⟨R, hR, hsub⟩ := exists_closure_subset_ball hb
  let q : ℂ := ((R + 1 : ℝ) : ℂ) * I
  have hqH : q ∈ H := by
    show 0 < q.im
    simpa [q] using (by positivity : 0 < R + 1)
  have hqn : ‖q‖ = R + 1 := by
    simp only [q, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  have hqU : q ∈ outerChartFace η w s := by
    refine ⟨hqH, fun hf => ?_⟩
    have hlt := mem_ball_zero_iff.1 (fillH_subset_ball hR hsub hf)
    rw [hqn] at hlt
    linarith
  let γ : ℝ → ℂ := fun t => (1 - t) • c.point + t • q
  refine ⟨⟨γ, (by fun_prop : Continuous γ).continuousOn, ?_, by simp [γ], ?_⟩⟩
  · intro t ht
    exact convex_H c.point_mem.2 hqH (sub_nonneg.2 ht.2) ht.1 (by ring)
  · simpa only [γ, sub_self, zero_smul, one_smul, zero_add] using hqU

/-- Natural-number well-ordering selects a path of least crossed cardinality.
Finiteness of every such family is independently proved above. -/
theorem PositiveGateComponent.exists_minimal_exitPath (c : PositiveGateComponent η w s)
    (hb : IsBounded (chartFlowSet η w s)) :
    ∃ p : GateExitPath c, ∀ q : GateExitPath c, p.crossed.ncard ≤ q.crossed.ncard := by
  classical
  have hex : ∃ n : ℕ, ∃ p : GateExitPath c, p.crossed.ncard = n := by
    obtain ⟨p⟩ := c.exists_gateExitPath hb
    exact ⟨p.crossed.ncard, p, rfl⟩
  obtain ⟨p, hp⟩ := Nat.find_spec hex
  refine ⟨p, fun q => ?_⟩
  rw [hp]
  exact Nat.find_min' hex ⟨q, rfl⟩

/-- A bypass crossing a strict subset is impossible for a minimal path. -/
theorem GateExitPath.not_strict_bypass (p : GateExitPath c) (hη : IsProperArc η)
    (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    (hmin : ∀ q : GateExitPath c, p.crossed.ncard ≤ q.crossed.ncard)
    (q : GateExitPath c) : ¬ q.crossed ⊂ p.crossed :=
  fun h => not_lt_of_ge (hmin q) (Set.ncard_lt_ncard h (p.finite_crossed hη hw hw0 hs))

end InteractingSLE.Sec5.Prop51HTopo
