/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513TargetCones
import InteractingSLE.Spec.Sec5.Prop59TipsRoot

/-! # Concrete Q prefixes and the remaining Lemma 5.7 input

The geometric input is stated in the actual Q-prefix clock, followed by
inversion into the counterflow capacity chart. It includes the positive-time
visit, so neither original marked endpoint is counted as a node. No covariance
of curve clocks is inferred from covariance of the field alone.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal
universe u

namespace InteractingSLE.Sec5.Prop513Target
open QuantumZipper Sec4 Prop513Schedule Prop513TreeExtract Restart
open LQGMetric Exist Exist.Staged Exist.StagedLaw

/-- The deterministic finite word realizing the canonical Q datum. -/
def sourceWord {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hb : IsFig51Bounds κ a b a' b') :
    BoundaryWord := (exists_extremeWord_fig51 (x₀ := x₀) hκ hb).choose

theorem sourceWord_extreme {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ)
    (hb : IsFig51Bounds κ a b a' b') : ExtremeHeights κ (sourceWord (x₀ := x₀) hκ hb) :=
  (exists_extremeWord_fig51 (x₀ := x₀) hκ hb).choose_spec.2.2

theorem sourceWord_gff {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ)
    (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀}) :
    IsGFFWithBoundaryData P
      (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω))
      (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps := by
  have hw := (exists_extremeWord_fig51 (x₀ := x₀) hκ hb).choose_spec
  change IsGFFWithBoundaryData P _
    (exists_extremeWord_fig51 (x₀ := x₀) hκ hb).choose.fn (exists_extremeWord_fig51 (x₀ := x₀) hκ hb).choose.jumps
  rw [hw.1]
  apply (Restart.isGFFWithBoundaryData_congr P _
    (S := (stripQHJumps (Real.exp (π * x₀)) {0} {x₀} : Set ℝ))
    (fun y hy => hw.2.1 y (by rwa [hw.1]))).2
  exact gff (Real.exp_pos _) (isPiecewiseConstantBoundaryData_fig51Lower a b)
    (isPiecewiseConstantBoundaryData_fig51Upper x₀ a' b') hG

/-- The actual canonical trace reconstruction of every staged Q prefix. -/
def driverTree {Ω : Type*} (E : Schedule → ℕ → Ω → Driver) : ℕ → Ω → ℝ → ℂ :=
  fun n => prefixTrace (prefixDriver E) (scheduleAt n)

/-- Positive deterministic Q terminal times. -/
def treeTime (n : ℕ) : ℝ := terminal (scheduleAt n)

theorem treeTime_pos (n : ℕ) : 0 < treeTime n := by
  exact_mod_cast terminal_pos (scheduleAt n)

theorem treeTime_mono (n m : ℕ) : treeTime n ≤ treeTime (descendantIndex n m) := by
  exact_mod_cast terminal_descendant_le n m

/-- Lemma 5.7 in the Q-prefix clock, transported to the capacity chart `R`.
This is the precise remaining geometric input, distinct from field covariance. -/
def TargetLemma57Statement {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : Schedule → ℕ → Ω → Driver) (γ : Ω → ℝ≥0 → ℂ) : Prop :=
  ∀ᵐ ω ∂P, ∀ n, ∀ s t : ℝ, 0 < s → s < t → t ≤ treeTime n →
    ∃ v : ℝ≥0, 0 < v ∧ γ ω v = capacityTree (driverTree E) n ω t ∧
      ∀ w ≤ v, γ ω w ≠ capacityTree (driverTree E) n ω s

/-- The measurable tree version agrees through every closed terminal time
with the actual driver reconstruction used in the geometric and tip inputs. -/
theorem ae_driverTree_eq {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {E : Schedule → ℕ → Ω → Driver} {ξ : ℕ → Ω → ℝ → ℂ}
    (hR : PrefixTraceRegularity P (fun _ => univ) E)
    (he : ∀ᵐ ω ∂P, ∀ n, ∀ η : ℝ≥0 → ℂ,
      IsGeneratingTrace (prefixDriver E (scheduleAt n) ω) (terminal (scheduleAt n)) η →
      EqOn (ξ n ω) (fun t : ℝ => η t.toNNReal) (Icc 0 (treeTime n))) :
    ∀ᵐ ω ∂P, ∀ n, EqOn (ξ n ω) (driverTree E n ω) (Icc 0 (treeTime n)) := by
  have hr : ∀ᵐ ω ∂P, ∀ n, ContinuousOn (prefixDriver E (scheduleAt n) ω)
      {t | (t : ℝ≥0∞) < terminal (scheduleAt n)} ∧
      prefixDriver E (scheduleAt n) ω 0 = 0 ∧
      ∃ η, IsGeneratingTrace (prefixDriver E (scheduleAt n) ω) (terminal (scheduleAt n)) η :=
    ae_all_iff.2 fun n => (hR (scheduleAt n)).mono fun _ hω => hω (mem_univ _)
  filter_upwards [hr, he] with ω hω heω n t ht
  obtain ⟨hw, hw0, η, hη⟩ := hω n
  exact (heω n η hη ht).trans
    (prefixTrace_eq hw hw0 (D := prefixDriver E) (fun _ _ => rfl) hη ht).symm

/-- Agreement of all prefixes transfers both endpoints and whole rooted cones. -/
theorem node_cone_eq {Ω : Type*} {E : Schedule → ℕ → Ω → Driver}
    {ξ : ℕ → Ω → ℝ → ℂ} {ω : Ω}
    (he : ∀ n, EqOn (ξ n ω) (driverTree E n ω) (Icc 0 (treeTime n))) :
    (∀ n, extremeAngleTreeNode (capacityTree ξ) treeTime n ω =
      extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n ω) ∧
    ∀ n, extremeAngleTreeCone (capacityTree ξ) treeTime descendantIndex n ω =
      extremeAngleTreeCone (capacityTree (driverTree E)) treeTime descendantIndex n ω := by
  have hn : ∀ n, extremeAngleTreeNode (capacityTree ξ) treeTime n ω =
      extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n ω :=
    fun n => congrArg infinitySourceChart.1 (he n ⟨(treeTime_pos n).le, le_rfl⟩)
  refine ⟨hn, fun n => ?_⟩
  have hd : extremeAngleTreeDescendants (capacityTree ξ) treeTime descendantIndex n ω =
      extremeAngleTreeDescendants (capacityTree (driverTree E)) treeTime descendantIndex n ω := by
    apply iUnion_congr
    intro m
    apply Set.image_congr
    intro t ht
    exact congrArg infinitySourceChart.1 (he _ ⟨(treeTime_pos n).le.trans ht.1.le, ht.2⟩)
  exact congrArg closure (congrArg₂ insert (hn n) hd)

end InteractingSLE.Sec5.Prop513Target
