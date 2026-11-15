/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchGalTest

/-!
# A Galmarino rule constructed from a raw stopping time

Use the entire reconstructed state, retaining its initial force positions.
A raw stopping time read from that path gives a history rule whenever its
value is positive and within the record. Otherwise the history rule is
infinite. This guard handles records of lifetime zero and raw stopping times
which vanish outside the image law, without asking for mixed-zero Galmarino
rules. The construction satisfies the test on all histories.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.RetMatchGal

open LawUnique Restart.StoppedExtendWF

variable {nL nR : ℕ}

/-- The positive, attained-in-the-record version of a raw path stopping time. -/
def ruleOfRawStop (τ : (ℝ≥0 → DrivingValue nL nR) → ℝ≥0∞)
    (γ : HistorySpace nL nR) : ℝ≥0∞ :=
  if 0 < τ (readState γ) ∧ τ (readState γ) ≤ γ.1 then τ (readState γ) else ⊤

theorem measurable_ruleOfRawStop {τ : (ℝ≥0 → DrivingValue nL nR) → ℝ≥0∞}
    (hm : Measurable τ) : Measurable (ruleOfRawStop τ) := by
  have h := hm.comp measurable_readPath
  exact Measurable.ite
    ((measurableSet_lt measurable_const h).inter (measurableSet_le h measurable_fst))
    h measurable_const

/-- The raw Galmarino test and strict-past reconstruction give a history rule
valid on every continuous history, including records ending at the rule value. -/
theorem isHistGalmarino_ruleOfRawStop {τ : (ℝ≥0 → DrivingValue nL nR) → ℝ≥0∞}
    (hτ : IsStoppingTime statePathFiltration (fun w => (τ w : WithTop ℝ≥0))) :
    IsHistGalmarino (ruleOfRawStop τ) := by
  intro γ δ _ _ hγ hδ hag
  by_cases hgood : 0 < τ (readState γ) ∧ τ (readState γ) ≤ γ.1
  · have he : ruleOfRawStop τ γ = τ (readState γ) := ite_eq_left hgood
    have hδ' : τ (readState γ) ≤ δ.1 := he ▸ hδ
    have hag' : ∀ p, (dyadicTime p : ℝ≥0∞) < τ (readState γ) → γ.2 p = δ.2 p :=
      he ▸ hag
    have hval : τ (readState δ) = τ (readState γ) := by
      have ht := eq_of_isStoppingTime_prefix hτ (readState γ) (readState δ)
        (fun u hu => readState_congr hgood.1 hag' hu)
      exact congrArg (fun t : WithTop ℝ≥0 => (t : ℝ≥0∞)) ht
    have hgoodδ : 0 < τ (readState δ) ∧ τ (readState δ) ≤ δ.1 :=
      hval.symm ▸ ⟨hgood.1, hδ'⟩
    exact (ite_eq_left hgoodδ).trans (hval.trans he.symm)
  · have he : ruleOfRawStop τ γ = ⊤ := ite_eq_right hgood
    have hγtop : γ.1 = ⊤ := top_le_iff.1 (he ▸ hγ)
    have hδtop : δ.1 = ⊤ := top_le_iff.1 (he ▸ hδ)
    have hag' : ∀ p, (dyadicTime p : ℝ≥0∞) < ⊤ → γ.2 p = δ.2 p := he ▸ hag
    have hread : readState γ = readState δ :=
      funext fun t => readState_congr (by exact ENNReal.zero_lt_top) hag' le_top
    unfold ruleOfRawStop
    rw [hγtop, hδtop, hread]

/-- If the original continuous path lives beyond the positive raw stopping
value, the constructed history rule reads precisely that value. -/
theorem ruleOfRawStop_killedHistory {τ : (ℝ≥0 → DrivingValue nL nR) → ℝ≥0∞}
    (hτ : IsStoppingTime statePathFiltration (fun w => (τ w : WithTop ℝ≥0)))
    {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {ω : Ω}
    (hc : Continuous (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)))
    (hpos : 0 < τ (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)))
    (hle : τ (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) ≤ V ω) :
    ruleOfRawStop τ (killedHistory W VL VR V ω) =
      τ (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) := by
  have hread := eq_of_isStoppingTime_prefix hτ
    (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω))
    (readState (killedHistory W VL VR V ω))
    (fun t ht => (readState_killedHistory (hpos.trans_le hle) hc (ht.trans hle)).symm)
  have hval : τ (readState (killedHistory W VL VR V ω)) =
      τ (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) :=
    congrArg (fun t : WithTop ℝ≥0 => (t : ℝ≥0∞)) hread
  have hgood : 0 < τ (readState (killedHistory W VL VR V ω)) ∧
      τ (readState (killedHistory W VL VR V ω)) ≤ (killedHistory W VL VR V ω).1 :=
    hval.symm ▸ ⟨hpos, hle⟩
  exact (ite_eq_left hgood).trans hval

end InteractingSLE.Wire.RetMatchGal
