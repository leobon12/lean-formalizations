import SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusResidual.TargetRegularity
import SupercriticalLQGUniqueness.Uniqueness.Objects.CentreEvent.NineClauseBudget




 


set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusResidual
open LQGMetric (DistC)

 
def clauseSet (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData)
    (F : ℂ → DistC → Prop) (D : DistC → LSCMetric) : Fin 9 → Set DistC :=
  fun i =>
    if i = 0 then {g | Objects.CorrectedEvent.S1 C (D g) g}
    else if i = 1 then {g | Objects.CorrectedEvent.S2 C (D g) g}
    else if i = 2 then {g | Objects.CorrectedEvent.S3 C (D g)}
    else if i = 3 then {g | Objects.CorrectedEvent.S4 C T (fun z => F z g)}
    else if i = 4 then {g | Objects.CorrectedEvent.S5 C (D g)}
    else if i = 5 then {g | Objects.CorrectedEvent.S6 C (D g) g}
    else if i = 6 then {g | Objects.CorrectedEvent.S7 C T (D g) g}
    else if i = 7 then {g | Objects.CorrectedEvent.S8 C T (D g)}
    else {g | Objects.CorrectedEvent.S9 C T g}

 

theorem correctedEvent_iff_clauseSet (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData)
    (hData : Objects.CorrectedEvent.DataMatch C T) (F : ℂ → DistC → Prop)
    (D D' : DistC → LSCMetric) (g : DistC) :
    Objects.CorrectedEvent.correctedEvent C T hData F D D' g ↔
      ∀ i : Fin 9, g ∈ clauseSet C T F D i := by
  constructor
  · intro h i
    fin_cases i <;> simp_all [clauseSet, Objects.CorrectedEvent.correctedEvent]
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    have h6 := h 6
    have h7 := h 7
    have h8 := h 8
    simpa only [Objects.CorrectedEvent.correctedEvent, clauseSet, ite_true, ite_false,
      reduceCtorEq, Set.mem_ofPred_eq] using
      (show Objects.CorrectedEvent.S1 C (D g) g ∧ Objects.CorrectedEvent.S2 C (D g) g ∧
        Objects.CorrectedEvent.S3 C (D g) ∧ Objects.CorrectedEvent.S4 C T (fun z => F z g) ∧
        Objects.CorrectedEvent.S5 C (D g) ∧ Objects.CorrectedEvent.S6 C (D g) g ∧
        Objects.CorrectedEvent.S7 C T (D g) g ∧ Objects.CorrectedEvent.S8 C T (D g) ∧ Objects.CorrectedEvent.S9 C T g from by
          simp only [clauseSet] at h0 h1 h2 h3 h4 h5 h6 h7 h8
          exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩)

 
theorem correctedEvent_probability_of_clause_budgets
    (P : Measure DistC) [IsProbabilityMeasure P]
    (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (hData : Objects.CorrectedEvent.DataMatch C T)
    (F : ℂ → DistC → Prop) (D D' : DistC → LSCMetric)
    (pbar : Set.Ioo (0 : ℝ) 1)
    (hfail : ∀ i : Fin 9, P (clauseSet C T F D i)ᶜ ≤
      ENNReal.ofReal ((1 - (pbar : ℝ)) / 10)) :
    ENNReal.ofReal ((pbar : ℝ) + (1 - (pbar : ℝ)) / 10) ≤
      P {g | Objects.CorrectedEvent.correctedEvent C T hData F D D' g} := by
  have heq : {g | Objects.CorrectedEvent.correctedEvent C T hData F D D' g} =
      ⋂ i, clauseSet C T F D i := by
    ext g
    simpa only [Set.mem_ofPred_eq, Set.mem_iInter] using
      correctedEvent_iff_clauseSet C T hData F D D' g
  rw [heq]
  exact Objects.CentreEvent.nine_clause_budget P (clauseSet C T F D) pbar hfail

end SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusResidual
