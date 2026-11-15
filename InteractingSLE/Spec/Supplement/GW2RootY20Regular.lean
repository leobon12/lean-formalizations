/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootU19Canon
import InteractingSLE.Spec.Supplement.GW2ScheduleL25
import InteractingSLE.Spec.Restart.FlowCodeMain

/-!
# Regularity of the actual stopped trace reader

Packet PROVE-T14-GW2ROOT2. The source staged law and Theorem 1.3
identify the fixed Borel trace reader, including killed endpoints.
Lemma 2.5 supplies its zero boundary occupation before the stop.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootY20

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric RootU19

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (b : ℝ → ℝ)
  (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (h : Ω → DistOn upperHalfPlaneOpens)

/-- At every launched stage, the actual stopped record's Borel trace
reader is a generating trace through the finite endpoint and spends zero
own capacity time on the real boundary. No trace witness is selected. -/
theorem ae_canonical_recordTrace_regular (h13 : Theorem13Statement.{u})
    (hβA : IsStopLaw.{u} κ βA) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hh : IsGFFWithBoundaryData P h b jumps) (x : ℝ) (l : List (ℝ × ℝ≥0)) :
    ∀ᵐ ω ∂P, ∀ k c θ,
      (ExplState.run κ b jumps (schedSpec x l)
        (fun j => canonSpecFam hκ h12p βA c₀ h (schedSpec x l) j ω) (k + 1)).2.2.2.1 k =
          some (c, θ) →
      let E := canonSpecFam hκ h12p βA c₀ h (schedSpec x l) k ω
      let T := min (instrTime (schedSpec x l) k) E.2
      let γ := recordTrace (stopRec hκ h12p βA c₀ h (schedSpec x l) k ω)
      IsGeneratingTrace E.1 T γ ∧
        ContinuousOn γ {t | (t : ℝ≥0∞) ≤ T} ∧
        volume {t : ℝ | 0 ≤ t ∧ (t.toNNReal : ℝ≥0∞) < T ∧ γ t.toNNReal ∉ H} = 0 := by
  have hS := isStagedHistory_canonFam hκ h12p βA c₀
    (specAngle (schedSpec x l)) (specDelta (schedSpec x l))
    h13 hβA hb hc₀J hc₀ hh (spec := schedSpec x l) rfl
    (isFlowProg_spec x true l) (specDelta_ne_top _)
  have hR := stagedPiecesRegular_of_regular h13 hκ hb hS
    (fun k ω => isRegularDriver_canonDrive hκ h12p βA c₀ x
      (specAngle (schedSpec x l)) (specDelta (schedSpec x l)) (h ω) k)
  filter_upwards [hR.ae_pieceRegular] with ω hω k c θ hl
  obtain ⟨hW0, hW, η, hη, _⟩ := hω k c θ hl
  dsimp only
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
  have heq : ∀ t : ℝ≥0,
      (t : ℝ≥0∞) ≤ min (instrTime (schedSpec x l) k)
        (canonSpecFam hκ h12p βA c₀ h (schedSpec x l) k ω).2 →
      recordTrace (stopRec hκ h12p βA c₀ h (schedSpec x l) k ω) t = η t := by
    intro t ht
    change recordTrace (recOf (specDelta (schedSpec x l) k)
      (canonSpecFam hκ h12p βA c₀ h (schedSpec x l) k ω)) t = _
    rw [hd]
    exact recordTrace_recOf_eq
      (isRegularDriver_canonDrive hκ h12p βA c₀ x _ _ (h ω) k)
      (ne_top_of_le_ne_top hT (min_le_left _ _)) hW hη ht
  have hgen := isGeneratingTrace_congr_le hη heq
  exact ⟨hgen, hgen.2.1,
    hgen.volume_setOf_notMem_H (hW.mono fun t
      (ht : (t : ℝ≥0∞) < min (instrTime (schedSpec x l) k)
        (canonSpecFam hκ h12p βA c₀ h (schedSpec x l) k ω).2) => ht.le) hW0⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootY20
