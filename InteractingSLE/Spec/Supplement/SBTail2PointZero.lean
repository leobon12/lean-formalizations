/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2RetainTail

/-!
# Zero-stop schedule pieces belong to the retained physical prefix

At the root the zero-time radial tip is the root itself. At every subsequent
actual schedule launch the same radial limit is the preceding stopped piece's
terminal tip. This deterministic inclusion keeps the closed terminal endpoint;
it requires only that the current driver starts at zero.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Retain

open Exist.Staged Exist.StagedLaw GW2Schedule

/-- Reading a constant zero driver at time zero is the inverse chart's radial
boundary limit at the origin. -/
theorem tipAt_const_zero_iff {c : Chart} {z : ℂ} :
    c.tipAt (fun _ => 0) 0 z ↔
      Tendsto (fun y : ℝ => c.2.1 ((y : ℂ) * Complex.I)) (𝓝[>] 0) (𝓝 z) := by
  unfold Chart.tipAt
  apply tendsto_congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [NNReal.coe_zero]
  rw [fwdMapInv_zero_time continuous_const rfl
    (show (y : ℂ) * Complex.I ∈ QuantumZipper.H from
      show 0 < ((y : ℂ) * Complex.I).im by simpa using hy)]

/-- A zero-stop actual schedule piece adds no point beyond the retained prefix.
No regularity of the earlier drivers is needed for this chart identity. -/
theorem schedulePiece_subset_prefix_of_stop_zero
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x : ℝ}
    {l : List (ℝ × ℝ≥0)} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (hk : k < (scheduleProgram 0 l).length)
    (hlaunch : (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩ D
      (k + 1)).2.2.2.1 k ≠ none)
    (hW0 : (D k).1 0 = 0) (hstop : min (schedDelta 0 l k) (D k).2 = 0) :
    schedulePiece κ b jumps x l D k ⊆
      prefixPhysSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩ D k := by
  have hs := (launch_ne_none_iff (κ := κ) (b := b) (jumps := jumps)
    (θ := schedAngle l) (Δ := schedDelta 0 l) rfl
    (isFlowProg_scheduleProgram 0 l) (schedDelta_ne_top 0 l) D hk).1 hlaunch
  have hc := ((run_gw2 (κ := κ) (b := b) (jumps := jumps)
    (spec := ⟨x, true, scheduleProgram 0 l⟩) rfl
    (isFlowProg_scheduleProgram 0 l) (schedDelta_ne_top 0 l) D k hk.le).1 hs).2
  intro z hz
  change ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ min (schedDelta 0 l k) (D k).2 ∧ _ at hz
  simp only [hstop, min_zero, ENNReal.toNNReal_zero, hW0] at hz
  obtain ⟨t, ht, hz⟩ := hz
  have ht0 : t = 0 := by simpa using ht
  subst t
  rw [show (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩ D k).2.2.2.2.1 =
      succChart x (schedDelta 0 l) D k from hc] at hz
  have hrad := tipAt_const_zero_iff.1 hz
  cases k with
  | zero =>
    have hlim : Tendsto (fun y : ℝ => (y : ℂ) * Complex.I + (x : ℂ))
        (𝓝[>] 0) (𝓝 (x : ℂ)) := by
      simpa using (((Complex.continuous_ofReal.mul_const Complex.I).add_const (x : ℂ)).tendsto 0)
        |>.mono_left nhdsWithin_le_nhds
    have he : z = (x : ℂ) := tendsto_nhds_unique hrad hlim
    exact Or.inl (Or.inl (mem_singleton_iff.2 he))
  | succ j =>
    have hj : j < (scheduleProgram 0 l).length := (Nat.lt_succ_self j).trans hk
    have hsj : AllSucc (schedDelta 0 l) D j := hs.mono (Nat.le_succ j)
    have hlj := (launches_run_gw2 (κ := κ) (b := b) (jumps := jumps)
      (spec := ⟨x, true, scheduleProgram 0 l⟩) rfl
      (isFlowProg_scheduleProgram 0 l) (schedDelta_ne_top 0 l) D hj).1 hsj
    have hcj := ((run_gw2 (κ := κ) (b := b) (jumps := jumps)
      (spec := ⟨x, true, scheduleProgram 0 l⟩) rfl
      (isFlowProg_scheduleProgram 0 l) (schedDelta_ne_top 0 l) D j hj.le).1 hsj).2
    rw [prefixPhysSet_schedule_succ_of_launch hj (by rw [hlj]; exact Option.some_ne_none _)]
    apply Or.inr
    change ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ min (schedDelta 0 l j) (D j).2 ∧ _
    refine ⟨(min (schedDelta 0 l j) (D j).2).toNNReal,
      ENNReal.coe_toNNReal_le_self, ?_⟩
    rw [show (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩ D j).2.2.2.2.1 =
      succChart x (schedDelta 0 l) D j from hcj]
    exact hrad

/-- R51 supplies the zero initial driver value at every actual launch, hence
the deterministic zero-stop inclusion almost surely for the original family. -/
theorem ae_schedulePiece_subset_prefix_of_stop_zero
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x : ℝ} {l : List (ℝ × ℝ≥0)}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : StagedPiecesRegular κ b jumps P ⟨x, true, scheduleProgram 0 l⟩ E)
    {k : ℕ} (hk : k < (scheduleProgram 0 l).length) :
    ∀ᵐ ω ∂P, ω ∈ Leaf.launchEvent κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k →
      min (schedDelta 0 l k) (E k ω).2 = 0 →
      schedulePiece κ b jumps x l (fun j => E j ω) k ⊆
        prefixPhysSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩ (fun j => E j ω) k := by
  filter_upwards [hR.ae_pieceRegular] with ω hω hl hs
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  exact schedulePiece_subset_prefix_of_stop_zero hk hl (hω k c θ hcθ).1 hs

/-- In the finite schedule induction the zero-stop branch preserves avoidance
of any forbidden set, including the actual right side used by SB4. -/
theorem ae_zero_stop_avoids_of_prefix
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x : ℝ} {l : List (ℝ × ℝ≥0)}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : StagedPiecesRegular κ b jumps P ⟨x, true, scheduleProgram 0 l⟩ E)
    {k : ℕ} (hk : k < (scheduleProgram 0 l).length) {S : Ω → Set ℂ}
    (hprev : ∀ᵐ ω ∂P, prefixPhysSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩
      (fun j => E j ω) k ∩ S ω = ∅) :
    ∀ᵐ ω ∂P, ω ∈ Leaf.launchEvent κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k →
      min (schedDelta 0 l k) (E k ω).2 = 0 →
      schedulePiece κ b jumps x l (fun j => E j ω) k ∩ S ω = ∅ := by
  filter_upwards [ae_schedulePiece_subset_prefix_of_stop_zero hR hk, hprev]
    with ω hsub hp hl hs
  apply eq_empty_of_forall_notMem
  rintro z ⟨hz, hzS⟩
  have hm : z ∈ prefixPhysSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩
      (fun j => E j ω) k ∩ S ω := ⟨hsub hl hs hz, hzS⟩
  rw [hp] at hm
  exact hm

end InteractingSLE.Theorem14.SB.Retain
