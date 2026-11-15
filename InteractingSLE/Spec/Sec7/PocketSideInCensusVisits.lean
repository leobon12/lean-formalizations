/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInCensusUniform

/-!
# Actual common rational visits for bounded and seed-opening candidates

PROVE-POCKET-SIDEIN. Ready supplies an actual rational interior visit in
either pocket shape. Under initial nesting it is a common visit with both
relative capacities positive and live. Selecting a geometrically suitable
nested pair, and its shared current face, remain separate source steps.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open Sec6 PocketTraversal Lemma71C PocketStopMarked

/-- The seed-opening counterpart of the landed bounded-pocket rational
visit theorem, with its actual relative capacity positive and live. -/
theorem exists_rat_live_pocket_visit_inf {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ}
    {α₁ α₂ : ℝ → ℂ} {τ : ℝ} {ψ : ℂ → ℂ}
    (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ)
    (hψ : IsJordanCoordInf C (α₁ 0) ψ) :
    ∃ r : ℚ, (r : ℝ) ∈ visitSetInf η C τ ∧
      0 < (relCapInf η C τ ψ r).toNNReal ∧
      ((relCapInf η C τ ψ r).toNNReal : ℝ≥0∞) < capLife (travInf η C τ ψ) := by
  obtain ⟨T, hτT, hT⟩ := hP.exists_clock_gt (hP.clockEnd_pos hAC)
  have hτT' : τ < T := lt_of_le_of_ne hτT (by
    rintro rfl
    rw [IsReversePocketInf.clock_τ] at hT
    exact lt_irrefl _ hT)
  have hClock : pocketClockInf η C τ τ ≠ pocketClockInf η C τ T := by
    rw [IsReversePocketInf.clock_τ]
    exact hT.ne
  obtain ⟨t, -, ht⟩ := hP.exists_mem_of_clock_lt hτT' hClock
  obtain ⟨r, hr⟩ := Rat.denseRange_cast.exists_mem_open hP.isOpen_visitSet ⟨t, ht⟩
  obtain ⟨hpos, hlive⟩ := relCapInf_pos_lt_of_visit hP hAC hψ hr
  exact ⟨r, hr, Real.toNNReal_pos.2 hpos, hlive⟩

end InteractingSLE.Sec7.PocketStopSide

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec6 Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketWordAssembly
  Sec7.PocketSeedOpen Sec7.PocketStopSide Sec7.PocketTraversal Sec7.Lemma71C Sec7.PocketMarks

variable {Ω : Type} [MeasurableSpace Ω]

/-- Each actual Ready candidate is visited at a positive rational original
time, with its actual own capacity positive and strictly before its lifetime. -/
theorem exists_rat_live_visit_of_ready {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) {ω : Ω} (hω : ω ∈ (j.target i d).event) :
    ∃ r : ℚ, 0 < (r : ℝ) ∧ d.curve ω r ∈ (j.target i d).domain ω ∧
      0 < (j.visitCapacity d ω r).toNNReal ∧
      ((j.visitCapacity d ω r).toNNReal : ℝ≥0∞) < capLife ((j.target i d).curve ω) := by
  have hEvent : ω ∈ j.event := by rwa [target_event] at hω
  have hExists : ∃ r : ℚ, 0 < (r : ℝ) ∧ d.curve ω r ∈ (j.target i d).domain ω := by
    rw [target_domain]
    rcases hj with ⟨-, -, -, hG, -, hcfg, hcfgI, -, hAG, -, hJ, -⟩
    cases hI : j.infinite
    · simp only [hI, Bool.false_eq_true, ↓reduceIte] at hAG hJ
      have hc := hcfg ω (hAG hEvent).1 (hAG hEvent).2
      have hP := hc.conf.isReversePocket_of_counterflow
        (zero_notMem_closure_of_rightLo_pos hc.conf hc.bounded)
        hc.trace hc.continuous_W hc.W_zero hc.revR hc.revL hc.visR
      have hψ : IsJordanCoord
          (cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))
          (cfArcR (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) 0)
          (cfArcR (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) 1) (j.chart ω) := by
        rw [PocketCoord.IsChangeConfigInc.cfArcR_zero, PocketCoord.IsChangeConfigInc.cfArcR_one]
        exact hJ ω hEvent
      obtain ⟨r, hr, -, -⟩ := exists_rat_live_pocket_visit hP hc.attach hψ
      exact ⟨r, hP.nonneg.trans_lt hr.1.1, hr.2⟩
    · simp only [hI, ↓reduceIte] at hAG hJ
      have hzero := le_antisymm (le_of_not_gt (hAG hEvent).2)
        (hG ω (hAG hEvent).1).1.changeCorner_props.1.1
      have hc := hcfgI ω (hAG hEvent).1 hzero
      have hψ : IsJordanCoordInf
          (cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))
          (cfArcRInf (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) 0) (j.chart ω) := by
        rw [PocketCoord.IsChangeConfigInc.cfArcRInf_zero]
        exact hJ ω hEvent
      obtain ⟨r, hr, -, -⟩ := exists_rat_live_pocket_visit_inf hc.isReversePocketInf hc.attach hψ
      exact ⟨r, hc.isReversePocketInf.nonneg.trans_lt hr.1, hr.2⟩
  obtain ⟨r, hr, hVisit⟩ := hExists
  obtain ⟨hpos, hlive, -⟩ := visitCapacity_spec hj hω hr.le hVisit
  exact ⟨r, hr, hVisit, Real.toNNReal_pos.2 hpos, hlive⟩

/-- Initial nesting turns an actual inner rational visit into a common
original visit. Both own capacities and both lifetime bounds are derived. -/
theorem exists_rat_common_live_visit {outer inner : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hO : outer.Ready d) (hI : inner.Ready d) {ω : Ω}
    (hωO : ω ∈ (outer.target i d).event) (hωI : ω ∈ (inner.target i d).event)
    (hUC : (inner.target i d).domain ω ⊆ (outer.target i d).domain ω) :
    ∃ r : ℚ, 0 < (r : ℝ) ∧ d.curve ω r ∈ (inner.target i d).domain ω ∧
      d.curve ω r ∈ (outer.target i d).domain ω ∧
      0 < (inner.visitCapacity d ω r).toNNReal ∧
      ((inner.visitCapacity d ω r).toNNReal : ℝ≥0∞) < capLife ((inner.target i d).curve ω) ∧
      0 < (outer.visitCapacity d ω r).toNNReal ∧
      ((outer.visitCapacity d ω r).toNNReal : ℝ≥0∞) < capLife ((outer.target i d).curve ω) := by
  obtain ⟨r, hr, hVisit, hposI, hliveI⟩ := exists_rat_live_visit_of_ready hI hωI
  have hVisitO := hUC hVisit
  obtain ⟨hposO, hliveO, -⟩ := visitCapacity_spec hO hωO hr.le hVisitO
  exact ⟨r, hr, hVisit, hVisitO, hposI, hliveI, Real.toNNReal_pos.2 hposO, hliveO⟩

end InteractingSLE.Wire.Current.SideTest
