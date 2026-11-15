/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInGaugeData
import InteractingSLE.Spec.Sec7.PocketSideInInstGerm

/-!
# The probe leaf for all four actual side-pocket shapes

PROVE-POCKET-SIDEIN. Use the target's own weights, marks, curve, event and
measure. The one-left and two-left cases have their native Fin carriers,
so no permutation, coordinate cast or change of boundary word is needed.
The infinite flag is unrestricted.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketTraversal Sec7.PhaseSel Sec7.Lemma71C

/-- Install the selected lattice phase and literal probes for an actual
native side target, before asserting its other source laws. -/
def capacitySideData {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (j : SideTest Ω) (e : Late.SideData Ω) (m : Ω → ℤ) : Late.SideData Ω := by
  rcases j with ⟨seed, outerEvent, event, chart, infinite, twoLeft⟩
  cases twoLeft
  · let target := (SideTest.mk seed outerEvent event chart infinite false).target i d
    exact Late.capacityProbeSideData (nL := 0) (nR := 1) e target.kappa
      target.rhoL target.rhoR target.curve target.marksL target.marksR m
  · let target := (SideTest.mk seed outerEvent event chart infinite true).target i d
    exact Late.capacityProbeSideData (nL := 1) (nR := 1) e target.kappa
      target.rhoL target.rhoR target.curve target.marksL target.marksR m

/-- The exact `hSideProbes` conclusion for the constructed side data of
every Ready native pocket shape, with no further field or geometry premise. -/
theorem capacitySideData_probes {Ω : Type} [MeasurableSpace Ω] {i : BothLow}
    {d : WordObjects Ω} {j : SideTest Ω} (hj : j.Ready d)
    (e : Late.SideData Ω) (m : Ω → ℤ) :
    let target := j.target i d
    let refs := capacitySideData i d j e m
    ∀ N : ℕ, ∀ᵐ ω ∂target.measure, ω ∈ target.event →
      let S := {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (target.curve ω) ∧ t < (N : ℝ≥0) + 1}
      ContinuousOn (refs.probe N ω) S ∧ ContinuousOn (refs.baseProbe N ω) S ∧
        ContinuousOn (refs.weight N ω) S ∧
        ∀ t ∈ S, 0 < refs.weight N ω t ∧
          refs.probe N ω t - refs.baseProbe N ω t = refs.phase t ω * refs.weight N ω t := by
  have hk : 0 < 16 / (16 / i.kappa) := div_pos (by norm_num)
    (div_pos (by norm_num) (lt_trans (by norm_num) i.kappa_gt_four))
  have hκ : 0 < (j.target i d).kappa := by
    cases h : j.twoLeft <;> simpa only [target, h, Bool.false_eq_true, ↓reduceIte] using hk
  have hDriven := isDrivenCurve_target (i := i) hj
  rcases j with ⟨seed, outerEvent, event, chart, infinite, twoLeft⟩
  cases twoLeft
  · exact Late.capacityProbeSideData_probes hκ e _ _ hDriven _ _ m
  · exact Late.capacityProbeSideData_probes hκ e _ _ hDriven _ _ m

end InteractingSLE.Wire.Current.SideTest
