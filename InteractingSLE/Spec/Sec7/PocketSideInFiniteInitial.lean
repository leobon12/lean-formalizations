/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRealCurrent
import InteractingSLE.Spec.Sec7.PocketSideInFiniteBound

/-!
# The actual initial chart is finite away from its outgoing corner

PROVE-POCKET-SIDEIN. Ready already contains the Jordan coordinate for both
pocket shapes. The bounded pocket has its named outgoing physical corner
as its only pole; the seed-opening pocket is finite at every finite access.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketStopSide

variable {Ω : Type} [MeasurableSpace Ω]

/-- Ready supplies the finite initial Jordan-coordinate limit at every
finite closure point except the bounded pocket's actual outgoing corner. -/
theorem continuousWithinAt_initial_chart_of_ready {j : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hj : j.Ready d) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) {p : ℂ}
    (hp : p ∈ closure ((j.target i d).domain ω))
    (hNotExit : j.infinite = false →
      p ≠ cfPt (openPt (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))) :
    ContinuousWithinAt ((j.target i d).chart ω) ((j.target i d).domain ω) p := by
  have hω' := hω
  rw [target_event] at hω'
  have hJ := hj.2.2.2.2.2.2.2.2.2.2.1
  cases hI : j.infinite
  · simp only [hI, Bool.false_eq_true, ↓reduceIte] at hJ
    have hJω := hJ ω hω'
    rw [target_domain] at hp
    rw [target_domain, target_chart]
    have hc := hJω.1 p ⟨hp, hNotExit hI⟩
    apply hc.mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds (hNotExit hI))] with z hz hz'
    exact ⟨subset_closure hz, hz'⟩
  · simp only [hI, ↓reduceIte] at hJ
    have hJω := hJ ω hω'
    rw [target_domain] at hp
    rw [target_domain, target_chart]
    exact (hJω.1 p hp).mono subset_closure

/-- The initial finite extension is the actual Jordan coordinate selected
by Ready; it agrees with the canonical base chart on its domain. -/
theorem exists_initial_finite_extension_of_ready {j : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) {p : ℂ}
    (hp : p ∈ closure ((j.target i d).domain ω))
    (hNotExit : j.infinite = false →
      p ≠ cfPt (openPt (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))) :
    ∃ E : ℂ → ℂ, EqOn E ((j.target i d).baseChart ω).1 ((j.target i d).baseChart ω).dom ∧
      ContinuousWithinAt E ((j.target i d).baseChart ω).dom p := by
  have hc := (isPocketChartOn hj hRc hLc (i := i)).1 ω hω
  refine ⟨(j.target i d).chart ω, ?_, ?_⟩
  · intro z hz
    exact (hc.2.2.1 (hc.2.1 ▸ hz)).symm
  · rw [hc.2.1]
    exact continuousWithinAt_initial_chart_of_ready hj hω hp hNotExit

end InteractingSLE.Wire.Current.SideTest
