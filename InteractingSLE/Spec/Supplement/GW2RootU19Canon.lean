/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootU19Observe

/-!
# The source canonical pieces supply their stopped tip observations

Packet PROVE-T14-GW2ROOT2. Theorem 1.3 and the actual staged GFF law
discharge all regularity requirements of the record readers. This applies
to every launched piece of every finite schedule at any real root.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootU19

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric

/-- Every actual instruction of a finite GW2 schedule has finite own time. -/
theorem instrTime_sched_ne_top (x : ℝ) (l : List (ℝ × ℝ≥0)) {k : ℕ} (hk : k < l.length) :
    instrTime (schedSpec x l) k ≠ ⊤ := by
  rw [instrTime_eq (schedAngle l) (schedDelta 0 l) (isFlowProg_scheduleProgram 0 l)
    (hk.trans_eq (length_scheduleProgram 0 l).symm)]
  exact schedDelta_ne_top 0 l k

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (b : ℝ → ℝ)
  (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (h : Ω → DistOn upperHalfPlaneOpens)

/-- On one conull source event, each launched canonical piece has its
original generating trace and the record observation returns its actual
driver and tip at every available own time. No measurable trace witness
or stopped-record identification is assumed. -/
theorem ae_canonical_recordObservation (h13 : Theorem13Statement.{u})
    (hβA : IsStopLaw.{u} κ βA) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hh : IsGFFWithBoundaryData P h b jumps) (x : ℝ) (l : List (ℝ × ℝ≥0)) :
    ∀ᵐ ω ∂P, ∀ k c θ,
      (ExplState.run κ b jumps (schedSpec x l)
        (fun j => canonSpecFam hκ h12p βA c₀ h (schedSpec x l) j ω) (k + 1)).2.2.2.1 k =
          some (c, θ) →
      let E := canonSpecFam hκ h12p βA c₀ h (schedSpec x l) k ω
      ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace E.1 (min (instrTime (schedSpec x l) k) E.2) γ ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ instrTime (schedSpec x l) k → (t : ℝ≥0∞) < E.2 →
          recordObservation t (stopRec hκ h12p βA c₀ h (schedSpec x l) k ω) = (E.1 t, γ t) := by
  have hS := isStagedHistory_canonFam hκ h12p βA c₀
    (specAngle (schedSpec x l)) (specDelta (schedSpec x l))
    h13 hβA hb hc₀J hc₀ hh (spec := schedSpec x l) rfl
    (isFlowProg_spec x true l) (specDelta_ne_top _)
  have hR := stagedPiecesRegular_of_regular h13 hκ hb hS
    (fun k ω => isRegularDriver_canonDrive hκ h12p βA c₀ x
      (specAngle (schedSpec x l)) (specDelta (schedSpec x l)) (h ω) k)
  filter_upwards [hR.ae_pieceRegular] with ω hω k c θ hl
  obtain ⟨_, hW, γ, hγ, _⟩ := hω k c θ hl
  dsimp only
  refine ⟨γ, hγ, ?_⟩
  intro t ht hte
  have hins := (eq_launch_of_launches (schedSpec x l) _ hl).1
  have hk : k < l.length := by
    by_contra hk
    have hn : (schedSpec x l).2.2[k]? = none := List.getElem?_eq_none (by
      simpa only [schedSpec, length_scheduleProgram] using not_lt.mp hk)
    rw [hn] at hins
    cases hins
  have hT := instrTime_sched_ne_top x l hk
  have hd : specDelta (schedSpec x l) k = instrTime (schedSpec x l) k := by
    simp only [specDelta, hT, ↓reduceIte]
  change recordObservation t
    (recOf (specDelta (schedSpec x l) k)
      (canonSpecFam hκ h12p βA c₀ h (schedSpec x l) k ω)) = _
  rw [hd]
  exact recordObservation_recOf_eq
    (isRegularDriver_canonDrive hκ h12p βA c₀ x _ _ (h ω) k)
    (ne_top_of_le_ne_top hT (min_le_left _ _)) hW hγ ht hte

end InteractingSLE.Theorem14.GW2TipSystem.RootU19
