/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntChronoHistory

/-!
# The parameter of a point on a proper walk

The inverse parameter is continuous on every arc contained in the walk.
An arc appended beyond an initial segment has increasing parameter: its
start is the last old point, and it never returns to the old segment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal

namespace InteractingSLE.Theorem14.WalkIntOrient

/-- The unique full-walk parameter on the range of an injective walk. -/
def curveTime (α : ℝ≥0 → ℂ) (z : ℂ) : ℝ≥0 := Function.invFun α z

theorem curveTime_apply {α : ℝ≥0 → ℂ} (hα : Function.Injective α) (t : ℝ≥0) :
    curveTime α (α t) = t := Function.leftInverse_invFun hα t

theorem apply_curveTime {α : ℝ≥0 → ℂ} {z : ℂ} (hz : z ∈ range α) :
    α (curveTime α z) = z := Function.invFun_eq hz

/-- The proper walk's inducing map transports continuity of an arc to
continuity of its full-walk parameter. -/
theorem continuousOn_curveTime {ι : Type*} [TopologicalSpace ι]
    {α : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α)
    {γ : ι → ℂ} {S : Set ι} (hγ : ContinuousOn γ S) (hrange : γ '' S ⊆ range α) :
    ContinuousOn (fun t => curveTime α (γ t)) S := by
  rw [(WalkCont.isClosedEmbedding_of_isProperCurve hα).isInducing.continuousOn_iff]
  exact hγ.congr (fun t ht => apply_curveTime (hrange ⟨t, ht, rfl⟩))

/-- An injective arc leaving an old initial segment at its endpoint has
strictly increasing own time in the full-walk parameter. -/
theorem strictMonoOn_curveTime_of_initial_segment
    {ι : Type*} [TopologicalSpace ι] [ConditionallyCompleteLinearOrder ι]
    [OrderTopology ι] [DenselyOrdered ι]
    {α : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α)
    {γ : ι → ℂ} {a b : ι} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Icc a b))
    (hrange : γ '' Icc a b ⊆ range α) {c : ℝ≥0}
    (hstart : γ a = α c)
    (hmeet : ∀ t ∈ Icc a b, γ t ∈ α '' Icc 0 c → t = a) :
    StrictMonoOn (fun t => curveTime α (γ t)) (Icc a b) := by
  have htime : curveTime α (γ a) = c := by
    rw [hstart, curveTime_apply hα.2.1]
  have hends : curveTime α (γ a) ≤ curveTime α (γ b) := by
    rw [htime]
    by_contra h
    have hb : γ b ∈ α '' Icc 0 c :=
      ⟨curveTime α (γ b), ⟨zero_le, (lt_of_not_ge h).le⟩,
        apply_curveTime (hrange ⟨b, right_mem_Icc.2 hab, rfl⟩)⟩
    have hba := hmeet b (right_mem_Icc.2 hab) hb
    exact h (hba ▸ htime.ge)
  apply ContinuousOn.strictMonoOn_of_injOn_Icc hab hends
    (continuousOn_curveTime hα hγ hrange)
  intro s hs t ht heq
  change curveTime α (γ s) = curveTime α (γ t) at heq
  apply hinj hs ht
  rw [← apply_curveTime (hrange ⟨s, hs, rfl⟩),
    ← apply_curveTime (hrange ⟨t, ht, rfl⟩), heq]

end InteractingSLE.Theorem14.WalkIntOrient
