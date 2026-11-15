/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12CurrentPocket
import InteractingSLE.Spec.Sec7.Lemma725RefMarksWord

/-!
# Geometric side inputs of the current pocket-word wiring

PROVE-POCKET-SIDEIN. The existing `SideTest.Ready` preconditions already give
the canonical chart, pocket openness, Jordan data, closure and active-domain
identity. These adapters retain the original right stop and both pocket shapes.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric Bornology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketWordAssembly
  Sec7.PocketSeedOpen Sec7.PocketMarks Sec7.PocketCoupling Sec7.PocketWordPerQ Sec7.PocketStopField
  Sec7.PocketStopSide Sec7.PocketUnionPt Sec7.Lemma71C

variable {Ω : Type} [mΩ : MeasurableSpace Ω] (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω)

theorem target_walls : (j.target i d).walls = wallsSigma d.measure d.rightWall (d.leftWall j.seed)
  := by
  cases h : j.twoLeft <;> simp only [target, h, Bool.false_eq_true, ↓reduceIte]

theorem target_event : (j.target i d).event = j.event := by
  cases h : j.twoLeft <;> simp only [target, h, Bool.false_eq_true, ↓reduceIte]

theorem target_domain : (j.target i d).domain =
    fun ω => cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) := by
  cases h : j.twoLeft <;> simp only [target, h, Bool.false_eq_true, ↓reduceIte]

theorem target_chart : (j.target i d).chart = j.chart := by
  cases h : j.twoLeft <;> simp only [target, h, Bool.false_eq_true, ↓reduceIte]

theorem target_curve : (j.target i d).curve =
    if j.infinite then travAllInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve
      j.chart
      else travAll d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart := by
  cases h : j.twoLeft <;> simp only [target, h, Bool.false_eq_true, ↓reduceIte]

/-- Both pocket shapes have the same incoming physical corner. -/
def incomingSeed : Ω → ℂ :=
  fun ω => cfPt (closePt (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))

variable {j i d}

theorem isOpen_domain (hj : j.Ready d) :
    ∀ ω ∈ (j.target i d).event, IsOpen ((j.target i d).domain ω) := by
  rcases hj with ⟨-, -, -, hG, -, -, -, -, hAG, -⟩
  rw [target_event, target_domain]
  intro ω hω
  have hωG : ω ∈ j.outerEvent := by
    cases hI : j.infinite <;> simp only [hI, Bool.false_eq_true, ↓reduceIte] at hAG <;>
      exact (hAG hω).1
  have hcfg := (hG ω hωG).1
  exact isOpen_image_negInv' hcfg.isOpen_changePocket hcfg.changePocket_subset_H

theorem isPocketChartOn (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) :
    IsPocketChartOn (j.target i d).walls (j.target i d).event (j.target i d).domain
      (j.target i d).chart (j.target i d).baseChart := by
  rcases hj with ⟨-, hGm, -, hG, -, -, -, hAm, hAG, -, hJ, hJm, -⟩
  have hRm := measurable_right_wallsSigma (P := d.measure) hRc hLc
  have hLm := measurable_left_wallsSigma (P := d.measure) hRc hLc
  have hGp := (measurableSet_rightLo_pos_and
    (mΩ := wallsSigma d.measure d.rightWall (d.leftWall j.seed)) hRm hLm hGm (fun ω hω => (hG ω
      hω).1)).1
  have hG0 : MeasurableSet[wallsSigma d.measure d.rightWall (d.leftWall j.seed)]
      {ω | ω ∈ j.outerEvent ∧ ¬ 0 < rightLo (d.rightWall ω) (d.leftWall j.seed ω)
        (StripSys.rt j.seed)} := by
    convert hGm.diff hGp using 1
    ext ω
    simp only [mem_ofPred_eq, Set.mem_sdiff]
    tauto
  simp only [SideTarget.baseChart, target_walls, target_event, target_domain, target_chart]
  cases hI : j.infinite
  · simp only [hI, Bool.false_eq_true, ↓reduceIte] at hAG hJ hJm
    exact (isPocketChartOn_cfPocket hRm hLm hGp (fun ω hω => (hG ω hω.1).1)
      hAm hAG hJ hJm).1
  · simp only [hI, ↓reduceIte] at hAG hJ hJm
    exact (isPocketChartOn_cfPocketInf hRm hLm hG0 (fun ω hω => (hG ω hω.1).1)
      hAm hAG hJ hJm).1

/-- The canonical incoming corner supplies the original Jordan alternative. -/
theorem jordan_cases (hj : j.Ready d) :
    ∀ ω ∈ (j.target i d).event,
      (∃ pole : ℂ, IsBounded ((j.target i d).domain ω) ∧ pole ∉ (j.target i d).domain ω ∧
        Sec6.IsJordanCoord ((j.target i d).domain ω) pole (j.incomingSeed d ω) ((j.target i
          d).chart ω)) ∨
      Sec6.IsJordanCoordInf ((j.target i d).domain ω) (j.incomingSeed d ω) ((j.target i d).chart ω)
        := by
  rcases hj with ⟨-, -, -, hG, -, hcfg, -, -, hAG, -, hJ, -⟩
  simp only [target_event, target_domain, target_chart, incomingSeed]
  intro ω hω
  cases hI : j.infinite
  · simp only [hI, Bool.false_eq_true, ↓reduceIte] at hAG hJ
    have hc := hcfg ω (hAG hω).1 (hAG hω).2
    have hp := hc.conf.isCfPocket (zero_notMem_closure_of_rightLo_pos hc.conf hc.bounded)
    exact Or.inl ⟨cfPt (openPt (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed)),
      hp.isBounded, hc.conf.cfPt_openPt_notMem, hJ ω hω⟩
  · simp only [hI, ↓reduceIte] at hJ
    exact Or.inr (hJ ω hω)

theorem closure_domain (hj : j.Ready d) :
    ∀ ω ∈ (j.target i d).event,
      closure ((j.target i d).domain ω) ⊆ H ∪ {j.incomingSeed d ω} := by
  rcases hj with ⟨-, -, -, hG, -, hcfg, hcfgI, -, hAG, -⟩
  simp only [target_event, target_domain, incomingSeed]
  intro ω hω
  cases hI : j.infinite
  · simp only [hI, Bool.false_eq_true, ↓reduceIte] at hAG
    have hc := hcfg ω (hAG hω).1 (hAG hω).2
    have hp := hc.conf.isCfPocket (zero_notMem_closure_of_rightLo_pos hc.conf hc.bounded)
    have he := closure_cfPocket_subset_H_union_seed hp
      (WangWu.image_negInv_subset_H hc.conf.changePocket_subset_H)
    rwa [PocketCoord.IsChangeConfigInc.cfArcR_one] at he
  · simp only [hI, ↓reduceIte] at hAG
    have hg := (hG ω (hAG hω).1).1
    have hzero := le_antisymm (le_of_not_gt (hAG hω).2) hg.changeCorner_props.1.1
    have he := closure_cfPocketInf_subset_H_union_seed (hg.isCfPocketInf hzero)
    rwa [PocketCoord.IsChangeConfigInc.cfArcRInf_zero] at he

/-- Domain point measurability is already supplied by the continuous walls. -/
theorem measurableSet_domain (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) :
    ∀ z, MeasurableSet[(j.target i d).walls]
      {ω | ω ∈ (j.target i d).event ∧ z ∈ (j.target i d).domain ω} := by
  rcases hj with ⟨-, hGm, -, hG, -, -, -, hAm, hAG, -⟩
  have hAG' : j.event ⊆ j.outerEvent := by
    intro ω hω
    cases hI : j.infinite <;> simp only [hI, Bool.false_eq_true, ↓reduceIte] at hAG <;>
      exact (hAG hω).1
  rw [target_walls]
  simp only [target_event, target_domain]
  exact measurableSet_mem_cfPocket_of_subset
    (measurable_right_wallsSigma (P := d.measure) hRc hLc)
    (measurable_left_wallsSigma (P := d.measure) hRc hLc)
    hGm (fun ω hω => (hG ω hω).1) hAm hAG'

/-- The open-set inclusion events in the exterior-germ construction are walls'
events by the existing two-wall criterion. -/
theorem measurableSet_domainIn (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) :
    ∀ U : Set ℂ, IsOpen U → U ⊆ H →
      MeasurableSet[(j.target i d).walls]
        {ω | ω ∈ (j.target i d).event ∧ U ⊆ (j.target i d).domain ω} := by
  rcases hj with ⟨-, hGm, -, hG, -, -, -, hAm, hAG, -⟩
  have hAG' : j.event ⊆ j.outerEvent := by
    intro ω hω
    cases hI : j.infinite <;> simp only [hI, Bool.false_eq_true, ↓reduceIte] at hAG <;>
      exact (hAG hω).1
  rw [target_walls]
  simp only [target_event, target_domain]
  intro U hUo hUH
  exact Lemma725RefMarks.measurableSet_subset_cfPocket
    (measurable_right_wallsSigma (P := d.measure) hRc hLc)
    (measurable_left_wallsSigma (P := d.measure) hRc hLc)
    hGm (fun ω hω => (hG ω hω).1) hAm hAG' hUo hUH

/-- The actual right-stop identity follows from the constructed erasure. -/
theorem activeDom_eq (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) :
    ∀ (q : ℝ≥0) ω, ω ∈ (j.target i d).event →
      (q : ℝ≥0∞) < capLife ((j.target i d).curve ω) →
      activeDom (j.target i d).event (j.target i d).curve (j.target i d).baseChart q ω =
        (j.target i d).domain ω ∩ (H \ j.hull d q ω) := by
  have hc := isPocketChartOn (i := i) hj hRc hLc
  rcases hj with ⟨-, -, -, hG, -, hcfg, hcfgI, -, hAG, -, hJ, -⟩
  simp only [SideTarget.baseChart, target_event, target_domain, target_chart, target_curve] at hc ⊢
  intro q ω hω hq
  cases hI : j.infinite
  · simp only [hI, Bool.false_eq_true, ↓reduceIte, hull] at hAG hJ hq ⊢
    have h := hc.1 ω hω
    exact activeDom_cfPocket_eq_stopHull hω (hcfg ω (hAG hω).1 (hAG hω).2)
      (hJ ω hω) h.1 h.2.1 h.2.2.1 hq
  · simp only [hI, ↓reduceIte, hull] at hAG hJ hq ⊢
    have hg := (hG ω (hAG hω).1).1
    have hzero := le_antisymm (le_of_not_gt (hAG hω).2) hg.changeCorner_props.1.1
    have h := hc.1 ω hω
    exact activeDom_cfPocketInf_eq_stopHull hω (hcfgI ω (hAG hω).1 hzero)
      (hJ ω hω) h.1 h.2.1 h.2.2.1 hq

/-- The ambient complement at the unchanged right stop is open in both shapes. -/
theorem isOpen_hull_compl (hj : j.Ready d) :
    ∀ (q : ℝ≥0) ω, ω ∈ (j.target i d).event → IsOpen (H \ j.hull d q ω) := by
  rcases hj with ⟨-, -, -, hG, -, hcfg, hcfgI, -, hAG, -⟩
  rw [target_event]
  intro q ω hω
  cases hI : j.infinite
  · simp only [hI, Bool.false_eq_true, ↓reduceIte, hull, stopHull] at hAG ⊢
    have hc := hcfg ω (hAG hω).1 (hAG hω).2
    have hP := hc.conf.isReversePocket_of_counterflow
      (zero_notMem_closure_of_rightLo_pos hc.conf hc.bounded)
      hc.trace hc.continuous_W hc.W_zero hc.revR hc.revL hc.visR
    exact isOpen_H_diff_fwdHull_ambTime hP (j.chart ω) q
  · simp only [hI, ↓reduceIte, hull, stopHullInf] at hAG ⊢
    have hg := (hG ω (hAG hω).1).1
    have hzero := le_antisymm (le_of_not_gt (hAG hω).2) hg.changeCorner_props.1.1
    have hc := hcfgI ω (hAG hω).1 hzero
    exact isOpen_H_diff_fwdHull_ambTimeInf hc.isReversePocketInf hc.attach (j.chart ω) q

end InteractingSLE.Wire.Current.SideTest
