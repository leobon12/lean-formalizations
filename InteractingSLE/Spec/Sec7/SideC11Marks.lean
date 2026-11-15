/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC10Angles
import InteractingSLE.Spec.Sec7.SideAncOrient

/-!
# The actual initial marks have their required signs

PROVE-SIDE-COLLAR2. Both Jordan alternatives in `Ready` retain the
flow-chart orientation. Their side theorems put the left wall's change
mark on the positive real line, and the selected right-wall change mark
on the negative real line. No mark-sign input remains.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open WangWu Sec7 Sec7.PocketCoord Sec7.PocketMarks Sec7.PocketJordan Sec7.PocketCoupling
  Sec7.PocketWordAssembly Sec7.PocketSeedOpen Sec7.SideAnc Sec7.PocketStopSide Sec7.Lemma71I

variable {Ω : Type} [MeasurableSpace Ω]

/-- Both actual initial force families have the correct signs on every
ready side test, including the pocket opening at the flow seed. -/
theorem initial_marks_signed_of_ready {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) {ω : Ω} (hω : ω ∈ (j.target i d).event) :
    (∀ a, (j.target i d).marksL ω a ≤ 0) ∧
      (∀ a, 0 ≤ (j.target i d).marksR ω a) := by
  have hω' := hω
  rw [target_event] at hω'
  rcases hj with ⟨-, -, -, hG, -, hcfg, hcfgI, -, hAG, -, hJ, -, hShape⟩
  have hSides :
      (∀ s ∈ Ioo (rightLo (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))
          (rightHi (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed)),
        (j.chart ω (cfPt (toDisc (Lemma71I.realPath (d.rightWall ω)) s))).re < 0) ∧
      ∀ t ∈ Ioo (leftLo (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))
          (leftHi (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed)),
        0 < (j.chart ω (cfPt (toDisc (Lemma71I.realPath (d.leftWall j.seed ω)) t))).re := by
    cases hI : j.infinite
    · simp only [hI, Bool.false_eq_true, ↓reduceIte] at hAG hJ
      have hc := hcfg ω (hAG hω').1 (hAG hω').2
      exact jordan_sides hc.conf (zero_notMem_closure_of_rightLo_pos hc.conf hc.bounded)
        hc.oriented (hJ ω hω')
    · simp only [hI, ↓reduceIte] at hAG hJ
      have h0 : rightLo (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) = 0 :=
        le_antisymm (le_of_not_gt (hAG hω').2) (hG ω (hAG hω').1).1.changeCorner_props.1.1
      have hc := hcfgI ω (hAG hω').1 h0
      exact jordanInf_sides hc.conf h0 hc.oriented (hJ ω hω')
  have hωG : ω ∈ j.outerEvent := by
    cases hI : j.infinite <;> simp only [hI, Bool.false_eq_true, ↓reduceIte] at hAG <;>
      exact (hAG hω').1
  have hPos := hSides.2 _ (hG ω hωG).1.changeCorners.2.2.2.2.1
  rcases j with ⟨seed, outerEvent, event, chart, infinite, twoLeft⟩
  cases twoLeft
  · constructor
    · change ∀ a : Fin 1, (![0] : Fin 1 → ℝ) a ≤ 0
      intro a
      fin_cases a
      exact le_rfl
    · change ∀ a : Fin 2, (![0, _] : Fin 2 → ℝ) a ≥ 0
      intro a
      fin_cases a
      · exact le_rfl
      · exact hPos.le
  · have hNeg := hSides.1 _ (hShape ω hω')
    constructor
    · change ∀ a : Fin 2, (![0, _] : Fin 2 → ℝ) a ≤ 0
      intro a
      fin_cases a
      · exact le_rfl
      · exact hNeg.le
    · change ∀ a : Fin 2, (![0, _] : Fin 2 → ℝ) a ≥ 0
      intro a
      fin_cases a
      · exact le_rfl
      · exact hPos.le

end InteractingSLE.Wire.Current.SideTest
