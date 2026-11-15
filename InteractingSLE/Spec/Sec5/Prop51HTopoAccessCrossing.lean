/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HTopoAccessComponent

/-!
# Finite candidate excursions across a bounded positive-gate face

A compact chart path leaving the actual gate component must cross visible flow
range, and only finitely many excursions meet its image. Such a path always
exists, by convexity of the half-plane and boundedness of the component. These
are concrete finite candidate data for the remaining positive-exit selection;
they do not assume that one of the candidates separates the entire face.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Bornology
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Prop51HTopo

open WangWu hiding ratPt exists_ratPt_dist_lt

variable {η : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ}

/-- There is an actual compact half-plane path from the gate point to outside
the bounded component. No new separation assumption is used to obtain it. -/
theorem PositiveGateComponent.exists_exit_path (c : PositiveGateComponent η w s) :
    ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc 0 1) ∧ MapsTo γ (Icc 0 1) H ∧
      γ 0 = c.point ∧ γ 1 ∉ c.domain := by
  obtain ⟨R, hR⟩ := c.bounded.exists_norm_le
  let q : ℂ := ((|R| + 1 : ℝ) : ℂ) * I
  have hqH : q ∈ H := by
    show 0 < q.im
    simpa [q] using (by positivity : (0 : ℝ) < |R| + 1)
  have hqn : ‖q‖ = |R| + 1 := by
    simp only [q, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  have hqout : q ∉ c.domain := by
    intro hq
    have hle := hR q hq
    rw [hqn] at hle
    linarith [le_abs_self R]
  let γ : ℝ → ℂ := fun t => (1 - t) • c.point + t • q
  refine ⟨γ, (by fun_prop : Continuous γ).continuousOn, ?_, by simp [γ], ?_⟩
  · intro t ht
    exact convex_H c.point_mem.2 hqH (sub_nonneg.2 ht.2) ht.1 (by ring)
  · simpa only [γ, sub_self, zero_smul, one_smul, zero_add] using hqout

/-- A path leaving the component must meet actual chart flow points. Relative
closedness excludes a spurious crossing of closure-only points in `H`. -/
theorem PositiveGateComponent.exists_flow_crossing (c : PositiveGateComponent η w s)
    (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    {γ : ℝ → ℂ} (hc : ContinuousOn γ (Icc 0 1)) (hγH : MapsTo γ (Icc 0 1) H)
    (hγ0 : γ 0 = c.point) (hγ1 : γ 1 ∉ c.domain) :
    ∃ t ∈ Icc (0 : ℝ) 1, γ t ∈ chartFlowSet η w s := by
  by_contra hn
  have hsub : γ '' Icc 0 1 ⊆ H \ closure (chartFlowSet η w s) := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨hγH ht, fun hzcl => hn ⟨t, ht, ?_⟩⟩
    exact mem_chartFlowSet_of_mem_closure hη hw hw0 hs hzcl (hγH ht)
  have hpc : IsPreconnected (γ '' Icc 0 1) := isPreconnected_Icc.image _ hc
  have hstart : c.point ∈ γ '' Icc 0 1 := ⟨0, ⟨le_rfl, zero_le_one⟩, hγ0⟩
  have hin := hpc.subset_connectedComponentIn hstart hsub
    (show γ 1 ∈ γ '' Icc 0 1 from ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩)
  exact hγ1 hin

/-- The excursions crossed by such a path form an actual finite nonempty set.
This is a finite candidate family, not an asserted boundary-arm selection. -/
theorem PositiveGateComponent.finite_nonempty_crossed_excursions
    (c : PositiveGateComponent η w s) (hη : IsProperArc η)
    (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    {γ : ℝ → ℂ} (hc : ContinuousOn γ (Icc 0 1)) (hγH : MapsTo γ (Icc 0 1) H)
    (hγ0 : γ 0 = c.point) (hγ1 : γ 1 ∉ c.domain) :
    let E := (fun t => connectedComponentIn (excursionTimes η w s) t) ''
      (Ici 0 ∩ η ⁻¹' (revChartInv w s '' (γ '' Icc 0 1)))
    E.Finite ∧ E.Nonempty := by
  dsimp only
  have hK : IsCompact (γ '' Icc 0 1) := isCompact_Icc.image_of_continuousOn hc
  have hKH : γ '' Icc 0 1 ⊆ H := by rintro _ ⟨t, ht, rfl⟩; exact hγH ht
  refine ⟨finite_excursions_meeting_chart_compact hη hw hw0 hs hK hKH, ?_⟩
  obtain ⟨t, ht, p, hp, he⟩ := c.exists_flow_crossing hη hw hw0 hs hc hγH hγ0 hγ1
  obtain ⟨u, hu, hue⟩ := hp.1
  refine ⟨connectedComponentIn (excursionTimes η w s) u, u, ⟨hu, ?_⟩, rfl⟩
  refine ⟨γ t, ⟨t, ht, rfl⟩, ?_⟩
  rw [← he, revChartInv_revChart hw hw0 hs hp.2, hue]

end InteractingSLE.Sec5.Prop51HTopo
