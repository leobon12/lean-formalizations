/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2Root2Cap
import InteractingSLE.Spec.Supplement.WalkIntChronoRange

/-!
# GW2's physical prefixes increase under canonical schedule extension

Packet PROVE-T14-GW2ROOT2. Canonical construction consistency, followed by
the existing persistence of piece and connector records, proves inclusion
of the actual physical sets and their joint-chart images at every sample.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootC11

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (b : ℝ → ℝ)
  (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u}
  (h : Ω → DistOn upperHalfPlaneOpens)

/-- Appending an instruction preserves every earlier canonical driver. -/
theorem canonSpecFam_append (x : ℝ) {l : List (ℝ × ℝ≥0)}
    (y : ℝ × ℝ≥0) {j : ℕ} (hj : j < l.length) (ω : Ω) :
    canonSpecFam hκ h12p βA c₀ h (schedSpec x (l ++ [y])) j ω =
      canonSpecFam hκ h12p βA c₀ h (schedSpec x l) j ω := by
  have hs := canonState_congr₂ hκ h12p βA c₀ x (h ω)
    (fun i hi => specAngle_schedSpec_append x y (hi.trans hj))
    (fun i hi => specDelta_schedSpec_append x y (hi.trans hj))
  change canonDrive hκ h12p βA c₀ x _ _ (h ω) j =
    canonDrive hκ h12p βA c₀ x _ _ (h ω) j
  simp only [canonDrive, hs, specAngle_schedSpec_append x y hj]

private theorem run_schedSpec_append_sameDriver (x : ℝ) {l : List (ℝ × ℝ≥0)}
    (y : ℝ × ℝ≥0) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    {n : ℕ} (hn : n ≤ l.length) :
    ExplState.run κ b jumps (schedSpec x (l ++ [y])) D n =
      ExplState.run κ b jumps (schedSpec x l) D n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hnl : n < l.length := Nat.lt_of_succ_le hn
    rw [run_succ, run_succ, ih (Nat.le_of_succ_le hn)]
    have he : (schedSpec x (l ++ [y])).2.2[n]? = (schedSpec x l).2.2[n]? :=
      scheduleProgram_getElem?_append 0 y hnl
    rw [he]
    rfl

/-- The run of the extended canonical schedule agrees through the old end. -/
theorem run_schedSpec_append (x : ℝ) {l : List (ℝ × ℝ≥0)}
    (y : ℝ × ℝ≥0) (ω : Ω) {n : ℕ} (hn : n ≤ l.length) :
    ExplState.run κ b jumps (schedSpec x (l ++ [y]))
        (fun j => canonSpecFam hκ h12p βA c₀ h (schedSpec x (l ++ [y])) j ω) n =
      ExplState.run κ b jumps (schedSpec x l)
        (fun j => canonSpecFam hκ h12p βA c₀ h (schedSpec x l) j ω) n := by
  exact (run_congr (schedSpec x (l ++ [y]))
    (fun j hj => canonSpecFam_append hκ h12p βA c₀ h x y (hj.trans_le hn) ω)).trans
      (run_schedSpec_append_sameDriver b jumps x y _ hn)

/-- Physical prefixes increase, including real connectors and killed samples. -/
theorem prefixSet_subset_append (x : ℝ) (l : List (ℝ × ℝ≥0))
    (y : ℝ × ℝ≥0) (ω : Ω) :
    prefixSet hκ h12p βA b jumps c₀ h x l ω ⊆
      prefixSet hκ h12p βA b jumps c₀ h x (l ++ [y]) ω := by
  have he := run_schedSpec_append hκ h12p βA b jumps c₀ h x y ω (n := l.length) le_rfl
  have hn : l.length ≤ (schedSpec x (l ++ [y])).2.2.length := by
    simp only [schedSpec, length_scheduleProgram, List.length_append, List.length_singleton]
    omega
  intro z hz
  have hl : (schedSpec x l).2.2.length = l.length := length_scheduleProgram 0 l
  simp only [prefixSet, ExplState.physSet, hl] at hz
  unfold prefixSet ExplState.physSet
  rw [← he] at hz
  rcases hz with (hz | hz) | hz
  · exact Or.inl (Or.inl hz)
  · obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 hz
    exact Or.inl (Or.inr (mem_iUnion₂.2
      ⟨p, WalkSide.mem_pieces_run_mono _ _ hp _ hn, hzp⟩))
  · obtain ⟨a, ha, hza⟩ := mem_iUnion₂.1 hz
    exact Or.inr (mem_iUnion₂.2
      ⟨a, WalkIntChrono.mem_arcs_run_mono _ _ ha hn, hza⟩)

/-- A fixed joint chart preserves inclusion of the canonical physical prefixes. -/
theorem prefixImage_subset_append (W' : ℝ≥0 → Ω → ℝ) (s : ℝ≥0)
    (x : ℝ) (l : List (ℝ × ℝ≥0)) (y : ℝ × ℝ≥0) (ω : Ω) :
    prefixImage hκ h12p βA b jumps c₀ h W' s x l ω ⊆
      prefixImage hκ h12p βA b jumps c₀ h W' s x (l ++ [y]) ω :=
  image_mono (inter_subset_inter_left _
    (prefixSet_subset_append hκ h12p βA b jumps c₀ h x l y ω))

end InteractingSLE.Theorem14.GW2TipSystem.RootC11
