/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LsHit
import InteractingSLE.Spec.Supplement.SB2LtRun

/-!
# The record invariants of a walk run: the steps

Packet PROVE-T14-SB2LIFT (round 11; item 2 of handoff §R9.2, the GW1-type record invariants). This file proves the
step facts of the record invariants of a run.

* **`run_succ_cases_of_noLaunch`**: a step without a launch leaves the state unchanged, marks it dead, moves along the
  boundary, or follows it to the end (`flowStep_trichotomy`, `contStep_cases`).
* **`stRecR_run_succ_ge_of_noLaunch`**: such a step does not decrease the right record.
* **`isRealChart_run`**: every run chart maps the real line into the real line. This holds for recentrings and for
  Loewner maps at real points (`im_fwdMap_ofReal`).
* **`tendsto_recenter`**: a boundary limit of an inverse chart survives a real recentring.
* **`beyond_launch_step`** (the launch step of the record invariant). Assume a launch with a finite lifetime, and
  `BeyondOK` at every point beyond the old record. Then the record does not decrease, and every point beyond the new
  record was left alive by the piece and is off the closure of the new filled prefix. The proof uses the record
  formula `lRecR_run_eq`, boundedness of the new fill (`isBounded_fillH`, through `image_runChart_walk`'s compact
  set), and `lAlive_run_iff`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap IsForwardSol)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}

/-- **A step without a launch**: unchanged, dead, a move along the boundary, or the end. -/
theorem run_succ_cases_of_noLaunch (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ}
    (h : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = none) :
    ExplState.run κ b jumps spec D (k + 1) = ExplState.run κ b jumps spec D k ∨
      ExplState.run κ b jumps spec D (k + 1) = setDead (ExplState.run κ b jumps spec D k) ∨
      (∃ (r : Bool) (x : ℝ) (m : Bool),
        ExplState.run κ b jumps spec D (k + 1) = ExplState.moveAlong (ExplState.run κ b jumps spec D k) r x m) ∨
      ∃ r : Bool, ExplState.run κ b jumps spec D (k + 1) =
        ExplState.moveToEnd (ExplState.run κ b jumps spec D k) r := by
  rw [run_succ] at h ⊢
  cases hk : spec.2.2[k]? with
  | none => exact Or.inl rfl
  | some a =>
    rw [hk] at h
    simp only at h ⊢
    rcases a with ⟨θ', t⟩ | pref | ⟨v, pref⟩
    · change (ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ' t).2.2.2.1 k = none at h
      rcases flowStep_trichotomy (κ := κ) (b := b) spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ' t
        with e | e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · rw [e, launches_launch, Function.update_self] at h; exact absurd h (by simp)
    · have e0 : ExplState.step κ b jumps spec.2.1 D (ExplState.run κ b jumps spec D k) (Sum.inr (Sum.inl pref), k) =
          ExplState.contStep κ b jumps (ExplState.run κ b jumps spec D k) none pref := rfl
      rw [e0]
      rcases contStep_cases (κ := κ) (b := b) (jumps := jumps) (ExplState.run κ b jumps spec D k) none pref
        with e | e | ⟨r, x, m, e⟩ | ⟨r, e⟩
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inl ⟨r, x, m, e⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨r, e⟩))
    · have e0 : ExplState.step κ b jumps spec.2.1 D (ExplState.run κ b jumps spec D k)
          (Sum.inr (Sum.inr (v, pref)), k) =
          ExplState.contStep κ b jumps (ExplState.run κ b jumps spec D k) (some v) pref := rfl
      rw [e0]
      rcases contStep_cases (κ := κ) (b := b) (jumps := jumps) (ExplState.run κ b jumps spec D k) (some v) pref
        with e | e | ⟨r, x, m, e⟩ | ⟨r, e⟩
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inl ⟨r, x, m, e⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨r, e⟩))

theorem stRecR_setDead (s : ExplState) : stRecR (setDead s) = stRecR s := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  rfl

theorem stChart_setDead (s : ExplState) : stChart (setDead s) = stChart s := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  rfl

theorem stChart_moveToEnd' (s : ExplState) (r : Bool) : stChart (ExplState.moveToEnd s r) = stChart s := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  rfl

theorem stRecR_moveAlong_ge (s : ExplState) (r : Bool) (x : ℝ) (m : Bool) :
    stRecR s ≤ stRecR (ExplState.moveAlong s r x m) := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  cases r
  · exact le_rfl
  · exact le_max_left _ _

theorem stChart_moveAlong' (s : ExplState) (r : Bool) (x : ℝ) (m : Bool) :
    stChart (ExplState.moveAlong s r x m) = (stChart s).recenter ((stChart s).1 x).re := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  rfl

/-- **A step without a launch does not decrease the right record.** -/
theorem stRecR_run_succ_ge_of_noLaunch (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ}
    (h : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = none) :
    stRecR (ExplState.run κ b jumps spec D k) ≤ stRecR (ExplState.run κ b jumps spec D (k + 1)) := by
  rcases run_succ_cases_of_noLaunch (κ := κ) (b := b) (jumps := jumps) spec D h with e | e | ⟨r, x, m, e⟩ | ⟨r, e⟩
  · rw [e]
  · rw [e, stRecR_setDead]
  · rw [e]; exact stRecR_moveAlong_ge _ r x m
  · rw [e, stRecR_moveToEnd']

/-- **Every run chart maps the real line into the real line.** -/
theorem isRealChart_run (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ∀ n, IsRealChart (stChart (ExplState.run κ b jumps spec D n))
  | 0 => fun x => by simp [ExplState.run, ExplState.init, Chart.id, Chart.recenter]
  | n + 1 => by
    have ih := isRealChart_run spec D n
    rcases hl : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n with _ | ⟨c, θ'⟩
    · obtain ⟨a, ha⟩ := chart_run_succ_of_noLaunch (κ := κ) (b := b) (jumps := jumps) spec D hl
      intro x
      show ((ExplState.run κ b jumps spec D (n + 1)).2.2.2.2.1.1 x).im = 0
      rw [ha]
      show ((stChart (ExplState.run κ b jumps spec D n)).1 x - (a : ℂ)).im = 0
      simp [ih x]
    · obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hl
      intro x
      show ((ExplState.run κ b jumps spec D (n + 1)).2.2.2.2.1.1 x).im = 0
      rw [he]
      by_cases htop : min (instrTime spec n) (D n).2 = ⊤
      · rw [GW2aCont.chart_launch_of_top _ _ _ _ _ htop]
        exact ih x
      · rw [chart_launch _ _ _ _ _ htop]
        have hy : (stChart (ExplState.run κ b jumps spec D n)).1 x =
            (((stChart (ExplState.run κ b jumps spec D n)).1 x).re : ℂ) := Complex.ext (by simp) (by simp [ih x])
        show (fwdMap _ _ ((stChart (ExplState.run κ b jumps spec D n)).1 x)).im = 0
        rw [hy]
        exact im_fwdMap_ofReal _ (NNReal.coe_nonneg _) _

/-- **A boundary limit of an inverse chart survives a real recentring.** -/
theorem tendsto_recenter {c : Chart} {x : ℂ} {y : ℂ} (h : Tendsto c.2.1 (𝓝[H] (c.1 x)) (𝓝 y)) (a : ℝ) :
    Tendsto (c.recenter a).2.1 (𝓝[H] ((c.recenter a).1 x)) (𝓝 y) := by
  have ht : Tendsto (fun z : ℂ => z + (a : ℂ)) (𝓝[H] ((c.recenter a).1 x)) (𝓝[H] (c.1 x)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : Continuous fun z : ℂ => z + (a : ℂ) := continuous_id.add continuous_const
      simpa only [Chart.recenter, sub_add_cancel] using
        (hc.tendsto ((c.recenter a).1 x)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      show 0 < (z + (a : ℂ)).im
      simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using (show (0 : ℝ) < z.im from hz)
  exact h.comp ht

end InteractingSLE.Theorem14.SB.Lk
