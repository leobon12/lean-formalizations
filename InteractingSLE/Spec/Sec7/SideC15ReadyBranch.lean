/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC15Branch
import InteractingSLE.Spec.Sec7.SideC15Tests

/-!
# R90a's measurable branch for the actual ready-test charts

PROVE-SIDE-COLLAR2. Readiness supplies the source geometry in both
pocket shapes. Aux. lemma 119 therefore supplies a walls-measurable
branch for the actual principal-logarithm chart, without an extra
branch-selection or orientation hypothesis.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.SideC13 Sec7.SideC15 Sec7.PocketCoord Sec7.PocketJordan
  Sec7.PocketMarks Sec7.SideAnc Sec7.PocketStopField Sec7.PocketWordPerQ

variable {Ω : Type} [MeasurableSpace Ω]

/-- The original conjugate chart of each ready sample is a source flow
chart; both orientation and the source uniformizer are produced. -/
theorem isFlowChart_conjugate_of_ready {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) :
    Aux119Bdry.IsFlowChart (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed)
      (jordanUnif (openPt (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed)) (j.chart ω))
      (conjugateFlowChart ((j.target i d).baseChart ω)) := by
  have hD := j.isDomainChart_baseChart hj hRc hLc hω
  have hf : EqOn ((j.target i d).baseChart ω).1 (j.chart ω) ((j.target i d).domain ω) := by
    intro z _
    change pFwd (j.target i d).event (j.target i d).chart ω z = _
    rw [pFwd_of_mem hω, target_chart]
  rw [target_domain] at hD hf
  have hω' := hω
  rw [target_event] at hω'
  rcases hj with ⟨_, _, _, hG, _, hcfg, hcfgI, _, hAG, _, hJ, _, _⟩
  cases hI : j.infinite
  · simp only [hI, Bool.false_eq_true, ↓reduceIte] at hAG hJ
    have hc := hcfg ω (hAG hω').1 (hAG hω').2
    exact isFlowChart_conjugate hc.conf
      (zero_notMem_closure_of_rightLo_pos hc.conf hc.bounded) hc.oriented (hJ ω hω') hD hf
  · simp only [hI, ↓reduceIte] at hAG hJ
    have h0 : rightLo (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) = 0 :=
      le_antisymm (le_of_not_gt (hAG hω').2) (hG ω (hAG hω').1).1.changeCorner_props.1.1
    have hc := hcfgI ω (hAG hω').1 h0
    exact isFlowChart_conjugate_inf hc.conf h0 hc.oriented (hJ ω hω') hD hf

/-- The actual source branch is measurable from the completed incoming
walls, so its fibres really are admissible ready-test events. -/
theorem exists_measurable_branch_of_ready {j : SideTest Ω} (i : BothLow) {d : WordObjects Ω}
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω))
    (hL0 : ∀ ω, d.leftWall j.seed ω 0 = 0) :
    ∃ n : Ω → ℤ, Measurable[(j.target i d).walls] n ∧
      ∀ ω ∈ j.event, Lemma71N.IsPocketBranch (d.leftWall j.seed ω) (d.rightWall ω)
        (conjugateFlowChart ((j.target i d).baseChart ω)) (n ω) := by
  have hA : MeasurableSet[(j.target i d).walls] (j.target i d).event := by
    rw [target_walls, target_event]
    exact hj.2.2.2.2.2.2.2.1
  have hLm : ∀ t, Measurable[(j.target i d).walls] fun ω => d.leftWall j.seed ω t := by
    rw [target_walls]
    exact measurable_left_wallsSigma hRc hLc
  have h := exists_measurable_branch_conjugate_pChart (mΩ := (j.target i d).walls)
    hLc hL0 hLm hA (j.isOpen_domain hj) (j.domain_subset_H_of_ready hj)
    (j.isConformalBijection_chart_of_ready hj)
    (j.measurableSet_domain hj hRc hLc) (j.measurable_chart_on_domain_of_ready hj hRc hLc)
    (fun ω _ => congrFun (j.target_domain i d) ω)
    (fun ω hω => j.isFlowChart_conjugate_of_ready hj hRc hLc hω)
  simpa only [SideTarget.baseChart, target_event] using h

end InteractingSLE.Wire.Current.SideTest
