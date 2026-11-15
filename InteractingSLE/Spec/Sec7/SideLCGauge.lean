/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideLCLattice
import InteractingSLE.Spec.Sec7.PocketSideInGaugeShapes
import InteractingSLE.Spec.Sec7.SideAncZero

/-!
# The late lattice leaf for the constructed probe data and for the zeroed data

PROVE-SIDE-LATCOL. Two existing constructions of late side data already have an integer phase at every
positive time: POCKET-SIDEIN's probe data `SideTest.capacitySideData i d j e m` (phase
`positiveLatticePhase (e.phase 0) m (phaseStep κ)`) and PROVE-SIDE-ANCHOR's zeroed data
`Late.SideData.zeroed e` (phase `0` at positive times). For both, the lattice leaf `hSideLattice`
(`LateSideLattice`) holds as soon as the initial phase `e.phase 0` is an integer multiple of `phaseStep κ`
at every sample — for instance when `e` is integer-indexed (`Late.SideData.intPhase`).
-/

set_option autoImplicit false
noncomputable section

open scoped NNReal

namespace InteractingSLE.Wire

open Current Sec7 Sec7.PocketStopSide Sec7.PhaseSel

/-- The phase of POCKET-SIDEIN's constructed probe data, for both native shapes. -/
theorem SideTest.capacitySideData_phase {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (j : SideTest Ω) (e : Late.SideData Ω) (m : Ω → ℤ) :
    (SideTest.capacitySideData i d j e m).phase =
      positiveLatticePhase (e.phase 0) m (phaseStep (16 / (16 / i.kappa))) := by
  rcases j with ⟨seed, outerEvent, event, chart, infinite, twoLeft⟩
  cases twoLeft <;> rfl

/-- The constructed probe data have an integer phase when the initial phase is an integer one. -/
theorem SideTest.isIntPhase_capacitySideData {Ω : Type} [MeasurableSpace Ω] (i : BothLow)
    (d : WordObjects Ω) (j : SideTest Ω) (e : Late.SideData Ω) (m : Ω → ℤ)
    (he : ∀ ω, ∃ k : ℤ, e.phase 0 ω = k * phaseStep (16 / (16 / i.kappa))) :
    (SideTest.capacitySideData i d j e m).IsIntPhase (16 / (16 / i.kappa)) := by
  intro q ω
  rw [SideTest.capacitySideData_phase]
  by_cases hq : q = 0
  · simp only [positiveLatticePhase, hq, ↓reduceIte]
    exact he ω
  · simp only [positiveLatticePhase, hq, ↓reduceIte]
    exact ⟨m ω, rfl⟩

/-- **The lattice leaf for POCKET-SIDEIN's constructed probe data** (with an integer initial phase). -/
theorem lateSideLattice_capacitySideData {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (e : SideTest Ω → Late.SideData Ω) (m : SideTest Ω → Ω → ℤ)
    (he : ∀ j ω, ∃ k : ℤ, (e j).phase 0 ω = k * phaseStep (16 / (16 / i.kappa))) :
    LateSideLattice i d (fun j => SideTest.capacitySideData i d j (e j) (m j)) :=
  lateSideLattice_of_isIntPhase i d _ fun j =>
    SideTest.isIntPhase_capacitySideData i d j (e j) (m j) (he j)

/-- The zeroed data have an integer phase when the initial phase is an integer one. -/
theorem Late.SideData.isIntPhase_zeroed {Ω : Type} (e : Late.SideData Ω) (κ : ℝ)
    (he : ∀ ω, ∃ k : ℤ, e.phase 0 ω = k * phaseStep κ) : e.zeroed.IsIntPhase κ := by
  intro q ω
  rw [Late.SideData.zeroed_phase]
  by_cases hq : q = 0
  · simp only [hq, ↓reduceIte]
    exact he ω
  · simp only [hq, ↓reduceIte]
    exact ⟨0, by rw [Int.cast_zero, zero_mul]⟩

/-- **The lattice leaf for PROVE-SIDE-ANCHOR's zeroed data** (with an integer initial phase). -/
theorem lateSideLattice_zeroed {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (e : SideTest Ω → Late.SideData Ω)
    (he : ∀ j ω, ∃ k : ℤ, (e j).phase 0 ω = k * phaseStep (16 / (16 / i.kappa))) :
    LateSideLattice i d (fun j => (e j).zeroed) :=
  lateSideLattice_of_isIntPhase i d _ fun j => (e j).isIntPhase_zeroed _ (he j)

end InteractingSLE.Wire
