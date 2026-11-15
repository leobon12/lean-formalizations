/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchExplicitTail

/-!
# A finite raw announcing sequence from raw approximations

Take attained tail minima, cap the nth one by n, and take running maxima.
This produces finite raw stopping times, monotone on every sample. Strictness
and cofinality hold almost surely from convergence of the tail minima.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.RetMatchExplicit

/-- Raw stopping times converging to a limit and eventually below it yield
an explicit finite raw announcing sequence of that limit. -/
theorem exists_raw_announcingSeq_of_approximation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {V : Ω → ℝ≥0∞} {R : ℕ → Ω → WithTop ℝ≥0}
    (hR : ∀ n, IsStoppingTime 𝓕 (R n))
    (hgood : ∀ᵐ ω ∂P, (∀ᶠ n in atTop, (R n ω : ℝ≥0∞) < V ω) ∧
      Tendsto (fun n => (R n ω : ℝ≥0∞)) atTop (𝓝 (V ω))) :
    ∃ B : ℕ → Ω → ℝ≥0, Coupling.IsAnnouncingSeq 𝓕 P V B := by
  let U : ℕ → Ω → ℝ≥0 := fun n ω => ENNReal.toNNReal
    (min (tailMinimum (fun k => R k ω) n : ℝ≥0∞) ((n : ℝ≥0) : ℝ≥0∞))
  have hUc : ∀ n ω, (U n ω : ℝ≥0∞) =
      min (tailMinimum (fun k => R k ω) n : ℝ≥0∞) ((n : ℝ≥0) : ℝ≥0∞) := by
    intro n ω
    exact ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))
  have hUs : ∀ n, IsStoppingTime 𝓕 (fun ω => (U n ω : WithTop ℝ≥0)) := by
    intro n
    have heq : (fun ω => (U n ω : WithTop ℝ≥0)) = fun ω =>
        min (tailMinimum (fun k => R k ω) n) ((n : ℝ≥0) : WithTop ℝ≥0) :=
      funext fun ω => congrArg (fun x : ℝ≥0∞ => (x : WithTop ℝ≥0)) (hUc n ω)
    exact heq.symm ▸ (isStoppingTime_tailMinimum hR n).min_const (n : ℝ≥0)
  let B : ℕ → Ω → ℝ≥0 := fun n ω => partialSups (fun k => U k ω) n
  have hBsucc : ∀ n ω, B (n + 1) ω = max (B n ω) (U (n + 1) ω) :=
    fun n ω => partialSups_succ (fun k => U k ω) n
  have hBs : ∀ n, IsStoppingTime 𝓕 (fun ω => (B n ω : WithTop ℝ≥0)) := by
    intro n
    induction n with
    | zero => simpa only [B, partialSups_zero] using hUs 0
    | succ n ih =>
      have heq : (fun ω => (B (n + 1) ω : WithTop ℝ≥0)) =
          fun ω => max (B n ω : WithTop ℝ≥0) (U (n + 1) ω : WithTop ℝ≥0) := by
        funext ω
        exact (congrArg (fun x : ℝ≥0 => (x : WithTop ℝ≥0)) (hBsucc n ω)).trans
          (WithTop.coe_max _ _)
      exact heq.symm ▸ ih.max (hUs (n + 1))
  have hstrict : ∀ᵐ ω ∂P, ∀ n, (B n ω : ℝ≥0∞) < V ω := by
    filter_upwards [hgood] with ω hω
    have htail := tailMinimum_lt_and_tendsto hω.2 hω.1
    have hUb : ∀ n, (U n ω : ℝ≥0∞) < V ω := fun n =>
      (hUc n ω).trans_lt ((min_le_left _ _).trans_lt (htail.1 n))
    intro n
    induction n with
    | zero => simpa only [B, partialSups_zero] using hUb 0
    | succ n ih =>
      have heq : (B (n + 1) ω : ℝ≥0∞) =
          max (B n ω : ℝ≥0∞) (U (n + 1) ω : ℝ≥0∞) :=
        (congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) (hBsucc n ω)).trans (ENNReal.coe_max _ _)
      exact heq.symm ▸ max_lt ih (hUb (n + 1))
  refine ⟨B, hBs, fun ω => (partialSups (fun k => U k ω)).monotone,
    fun n => hstrict.mono (fun _ h => h n), ?_⟩
  filter_upwards [hgood] with ω hω
  have htail := tailMinimum_lt_and_tendsto hω.2 hω.1
  have hcap : Tendsto (fun n : ℕ => ((n : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 ⊤) := by
    simpa only [ENNReal.coe_natCast] using ENNReal.tendsto_nat_nhds_top
  have hUL : Tendsto (fun n => (U n ω : ℝ≥0∞)) atTop (𝓝 (V ω)) := by
    have hmin : min (V ω) (⊤ : ℝ≥0∞) = V ω := min_eq_left le_top
    exact hmin ▸ (htail.2.min hcap).congr (fun n => (hUc n ω).symm)
  intro t ht
  obtain ⟨n, hn⟩ := (hUL.eventually (Ioi_mem_nhds ht)).exists
  exact ⟨n, (ENNReal.coe_lt_coe.1 hn).le.trans (le_partialSups (fun k => U k ω) n)⟩

end InteractingSLE.Wire.RetMatchExplicit
