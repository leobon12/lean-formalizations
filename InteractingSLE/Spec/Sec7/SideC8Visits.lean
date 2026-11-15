/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC8Height
import InteractingSLE.Spec.Sec7.SideC9VisitCore

/-!
# A fixed rational original reference before every positive live capacity

PROVE-SIDE-COLLAR2. Specialize the local copies of R5-REFCHART's interior
visit accumulation proofs to both actual Ready pocket shapes. The canonical fixed
rational family supplies an earlier positive-capacity reference at any
positive live current capacity. No probability law is evaluated at the
selected reference index.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec6 Sec7 Sec7.PocketStopSide Sec7.PocketStopMarked Sec7.PocketCoord Sec7.PocketJordan
  Sec7.PocketWordAssembly Sec7.PocketSeedOpen Sec7.PocketMarks Sec7.Lemma71C

variable {Ω : Type} [MeasurableSpace Ω]

/-- The fixed rational family has an actual interior visit of strictly
positive relative capacity strictly before every positive live `q`. -/
theorem exists_rational_reference_before_capacity {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) {ω : Ω} (hω : ω ∈ (j.target i d).event)
    {q : ℝ≥0} (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife ((j.target i d).curve ω)) :
    ∃ r : ℕ, d.curve ω (rationalOriginalTime r) ∈ (j.target i d).domain ω ∧
      0 < (j.visitCapacity d ω (rationalOriginalTime r)).toNNReal ∧
      (j.visitCapacity d ω (rationalOriginalTime r)).toNNReal < q := by
  have hqR : ENNReal.ofReal (q : ℝ) < capLife ((j.target i d).curve ω) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using hq
  rw [target_event] at hω
  rw [target_curve] at hqR
  rcases hj with ⟨-, -, -, hG, -, hcfg, hcfgI, -, hAG, -, hJ, -⟩
  cases hI : j.infinite
  · simp only [hI, Bool.false_eq_true, ↓reduceIte] at hAG hJ hqR
    have hc := hcfg ω (hAG hω).1 (hAG hω).2
    have hP := hc.conf.isReversePocket_of_counterflow
      (zero_notMem_closure_of_rightLo_pos hc.conf hc.bounded)
      hc.trace hc.continuous_W hc.W_zero hc.revR hc.revL hc.visR
    have hψ : IsJordanCoord
        (cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))
        (cfArcR (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) 0)
        (cfArcR (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) 1) (j.chart ω) := by
      rw [PocketCoord.IsChangeConfigInc.cfArcR_zero, PocketCoord.IsChangeConfigInc.cfArcR_one]
      exact hJ ω hω
    obtain ⟨s, hs0, hsT, hsVisit⟩ := SideCollarVisit.exists_rat_visit_lt_ambTime0 hP hc.attach hψ
      (show (0 : ℝ) < q from hq0) hqR (SideCollarVisit.lt_ambTime0 hP hc.attach hψ hq0 hqR)
    have hs := hP.nonneg.trans hs0.le
    have hp := (relCap_pos_lt_of_visit hP hc.attach hψ hsVisit).1
    have hpq := SideCollarVisit.relCap_lt_of_lt_ambTime0 hP hc.attach hψ q.coe_nonneg hqR
      ⟨hsVisit.1.1.le, hsVisit.1.2⟩ hsT
    refine ⟨Denumerable.eqv ℚ s, ?_, ?_, ?_⟩
    all_goals rw [rationalOriginalTime_eqv, Real.coe_toNNReal _ hs]
    · rw [target_domain]
      exact hsVisit.2
    · simpa only [visitCapacity, hI, Bool.false_eq_true, ↓reduceIte] using Real.toNNReal_pos.2 hp
    · simp only [visitCapacity, hI, Bool.false_eq_true, ↓reduceIte]
      exact (Real.toNNReal_lt_iff_lt_coe hp.le).2 hpq
  · simp only [hI, ↓reduceIte] at hAG hJ hqR
    have hzero := le_antisymm (le_of_not_gt (hAG hω).2)
      (hG ω (hAG hω).1).1.changeCorner_props.1.1
    have hc := hcfgI ω (hAG hω).1 hzero
    have hψ : IsJordanCoordInf
        (cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))
        (cfArcRInf (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) 0) (j.chart ω) := by
      rw [PocketCoord.IsChangeConfigInc.cfArcRInf_zero]
      exact hJ ω hω
    obtain ⟨s, hs0, hsT, hsVisit⟩ := SideCollarVisit.exists_rat_visitInf_lt_ambTime0Inf
      hc.isReversePocketInf hc.attach hψ (show (0 : ℝ) < q from hq0) hqR
      (SideCollarVisit.lt_ambTime0Inf hc.isReversePocketInf hc.attach hψ hq0 hqR)
    have hs := hc.isReversePocketInf.nonneg.trans hs0.le
    have hp := (relCapInf_pos_lt_of_visit hc.isReversePocketInf hc.attach hψ hsVisit).1
    have hpq := SideCollarVisit.relCapInf_lt_of_lt_ambTime0Inf hc.isReversePocketInf hc.attach hψ
      q.coe_nonneg hqR hsVisit.1.le hsT
    refine ⟨Denumerable.eqv ℚ s, ?_, ?_, ?_⟩
    all_goals rw [rationalOriginalTime_eqv, Real.coe_toNNReal _ hs]
    · rw [target_domain]
      exact hsVisit.2
    · simpa only [visitCapacity, hI, ↓reduceIte] using Real.toNNReal_pos.2 hp
    · simp only [visitCapacity, hI, ↓reduceIte]
      exact (Real.toNNReal_lt_iff_lt_coe hp.le).2 hpq

end InteractingSLE.Wire.Current.SideTest
