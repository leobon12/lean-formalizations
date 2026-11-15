/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootR18Path
import InteractingSLE.Spec.Supplement.GW2aContPass

/-!
# Changing the physical root of a fixed switched driver family

Packet PROVE-T14-GW2ROOT2. GW2's launch indices depend on its stopped
drivers and own times. Changing the root translates every inverse chart
and physical tip. The identities include killed schedules.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootU19

open GW2Schedule GW2Tip Exist Staged StagedLaw CounterflowRange

/-- Changing the root translates the inverse of every successful-prefix chart. -/
theorem succChart_inv_add (x : ℝ) (Δ : ℕ → ℝ≥0∞)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (z : ℂ) :
    (succChart x Δ D k).2.1 z = (succChart 0 Δ D k).2.1 z + x := by
  induction k generalizing z with
  | zero => simp only [succChart, recenter_id_inv, ofReal_zero, add_zero]
  | succ k ih => exact ih _

/-- Translating an inverse chart translates precisely its radial-limit tip set. -/
theorem tipSet_eq_image_of_inverse_add {c c' : Chart} (x : ℝ)
    (hc : ∀ z, c.2.1 z = c'.2.1 z + x) (W : ℝ≥0 → ℝ) (T : ℝ≥0∞) :
    c.tipSet W T = (fun z : ℂ => z + x) '' c'.tipSet W T := by
  ext z
  constructor
  · rintro ⟨t, ht, hlim⟩
    refine ⟨z - x, ⟨t, ht, ?_⟩, sub_add_cancel _ _⟩
    have h := hlim.sub_const (x : ℂ)
    simpa only [hc, add_sub_cancel_right] using h
  · rintro ⟨z, ⟨t, ht, hlim⟩, rfl⟩
    refine ⟨t, ht, ?_⟩
    simpa only [hc] using hlim.add_const (x : ℂ)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- Each actual launched piece translates with the root; an unlaunched
piece contributes the empty set at both roots. -/
theorem pieceTips_sched_root_image (x : ℝ) (l : List (ℝ × ℝ≥0))
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} (hk : k < l.length) :
    GW2aCont.pieceTips κ b jumps (schedSpec x l) D k =
      (fun z : ℂ => z + x) '' GW2aCont.pieceTips κ b jumps (schedSpec 0 l) D k := by
  have hk' : k < (scheduleProgram 0 l).length := hk.trans_eq (length_scheduleProgram 0 l).symm
  have hx := launches_run_gw2 (κ := κ) (b := b) (jumps := jumps)
    (spec := schedSpec x l) rfl (isFlowProg_scheduleProgram 0 l) (schedDelta_ne_top 0 l) D hk'
  have h0 := launches_run_gw2 (κ := κ) (b := b) (jumps := jumps)
    (spec := schedSpec 0 l) rfl (isFlowProg_scheduleProgram 0 l) (schedDelta_ne_top 0 l) D hk'
  by_cases hs : AllSucc (schedDelta 0 l) D k
  · have hcx := (run_gw2 (κ := κ) (b := b) (jumps := jumps)
      (spec := schedSpec x l) rfl (isFlowProg_scheduleProgram 0 l)
      (schedDelta_ne_top 0 l) D k hk'.le).1 hs
    have hc0 := (run_gw2 (κ := κ) (b := b) (jumps := jumps)
      (spec := schedSpec 0 l) rfl (isFlowProg_scheduleProgram 0 l)
      (schedDelta_ne_top 0 l) D k hk'.le).1 hs
    rw [GW2aCont.pieceTips, hx.1 hs, GW2aCont.pieceTips, h0.1 hs]
    simp only [Option.some_ne_none, ↓reduceIte]
    change (stChart (ExplState.run κ b jumps (schedSpec x l) D k)).tipSet _ _ =
      (fun z : ℂ => z + x) '' (stChart (ExplState.run κ b jumps (schedSpec 0 l) D k)).tipSet _ _
    rw [hcx.2, hc0.2]
    exact tipSet_eq_image_of_inverse_add x (succChart_inv_add x _ D k) _ _
  · simp only [GW2aCont.pieceTips, hx.2 hs, h0.2 hs, ↓reduceIte, image_empty]

/-- The actual physical set of a finite switched family translates with
its root, including its initial point and all killed-ending records. -/
theorem physSet_sched_root_image (x : ℝ) (l : List (ℝ × ℝ≥0))
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ExplState.physSet κ b jumps (schedSpec x l) D =
      (fun z : ℂ => z + x) '' ExplState.physSet κ b jumps (schedSpec 0 l) D := by
  have hax := (GW2aMulti.run_flowProgram κ b jumps
    (spec := schedSpec x l) (GW2aMulti.isFlowProgram_scheduleProgram 0 l) D
    (schedSpec x l).2.2.length).1
  have ha0 := (GW2aMulti.run_flowProgram κ b jumps
    (spec := schedSpec 0 l) (GW2aMulti.isFlowProgram_scheduleProgram 0 l) D
    (schedSpec 0 l).2.2.length).1
  unfold ExplState.physSet
  dsimp only
  rw [hax, ha0, GW2aCont.iUnion_pieces_run, GW2aCont.iUnion_pieces_run]
  simp only [schedSpec, List.not_mem_nil, iUnion_of_empty, iUnion_empty, union_empty,
    image_union, image_singleton, ofReal_zero, zero_add, image_iUnion,
    length_scheduleProgram]
  congr 1
  apply iUnion_congr
  intro k
  apply iUnion_congr
  intro hk
  exact pieceTips_sched_root_image x l D (Finset.mem_range.mp hk)

end InteractingSLE.Theorem14.GW2TipSystem.RootU19
