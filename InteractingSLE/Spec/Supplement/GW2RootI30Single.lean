/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootU19Shift
import InteractingSLE.Spec.Supplement.GW2RootE13Single

/-!
# The first physical carrier at an arbitrary real root

Packet PROVE-T14-GW2ROOT2. Reuse the exact root-translation identity
and the existing zero-root single-piece carrier. Freezing at a live
cutoff avoids any continuity premise at the original lifetime.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootI30

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric CounterflowRange

/-- The physical carrier of a live first piece is its translated trace prefix. -/
theorem physSet_single_of_live (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (x θ : ℝ)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (he : IsRegularDriver (D 0))
    {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace (D 0).1 (D 0).2 γ)
    {v : ℝ≥0} (hv : (v : ℝ≥0∞) < (D 0).2) :
    ExplState.physSet κ b jumps (x, true, [Sum.inl (θ, (v : ℝ≥0∞))]) D =
      (fun t => γ t + x) '' Icc 0 v := by
  let D₀ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun _ => ((D 0).1, (v : ℝ≥0∞))
  have hmodel := RootE13.physSet_single_eq_prefix κ b jumps true θ D₀
    (hγ.mono_horizon hv.le) (he.1.mono fun _ ht => ht.trans_lt hv) he.2.1 le_rfl
  have hactual : ExplState.physSet κ b jumps (0, true, [Sum.inl (θ, (v : ℝ≥0∞))]) D =
      γ '' Icc 0 v := by
    rw [physSet_single, min_eq_left hv.le]
    rw [physSet_single, min_self] at hmodel
    exact hmodel
  have htrans := RootU19.physSet_sched_root_image (κ := κ) (b := b) (jumps := jumps)
    x [(θ, v)] D
  have hspec : ∀ y : ℝ, schedSpec y [(θ, v)] =
      (y, true, [Sum.inl (θ, (v : ℝ≥0∞))]) := by
    intro y
    simp only [schedSpec, scheduleProgram, tsub_zero]
  rw [hspec x, hspec 0, hactual, image_image] at htrans
  exact htrans

/-- The actual canonical first schedule has the translated trace carrier. -/
theorem prefixSet_single_of_live {κ : ℝ} (hκ : 0 < κ)
    (h12p : Theorem12ParamStatement.{u})
    (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (b : ℝ → ℝ)
    (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u}
    (h : Ω → DistOn upperHalfPlaneOpens) (x θ : ℝ) (v : ℝ≥0) (ω : Ω) :
    let E := canonSpecFam hκ h12p βA c₀ h (schedSpec x [(θ, v)]) 0 ω
    ∀ {γ : ℝ≥0 → ℂ}, IsGeneratingTrace E.1 E.2 γ → (v : ℝ≥0∞) < E.2 →
      prefixSet hκ h12p βA b jumps c₀ h x [(θ, v)] ω =
        (fun t => γ t + x) '' Icc 0 v := by
  dsimp only
  intro γ hγ hv
  have he : IsRegularDriver (canonSpecFam hκ h12p βA c₀ h (schedSpec x [(θ, v)]) 0 ω) :=
    isRegularDriver_canonDrive hκ h12p βA c₀ x _ _ (h ω) 0
  have hmodel := physSet_single_of_live κ b jumps x θ
    (fun j => canonSpecFam hκ h12p βA c₀ h (schedSpec x [(θ, v)]) j ω) he hγ hv
  simpa only [prefixSet, schedSpec, scheduleProgram, tsub_zero] using hmodel

end InteractingSLE.Theorem14.GW2TipSystem.RootI30
