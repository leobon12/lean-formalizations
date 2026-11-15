/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootC24Gaps
import InteractingSLE.Spec.Supplement.GW2JDetR10ReferenceLaw

/-!
# Shared physical data for the two GW2 comparison properties

The local processes contain no SDE proof. The two separate properties in
`GW2JDetR11Facts` refer to this same data, so their existential witnesses
cannot silently choose different words, candidates or physical stops.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2JDetR11

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootN4
  GW2TipSystem.RootL6 Sec5

/-- Actual local coordinates and the physical recording stop. -/
structure LocalDynamics (Ω : Type u) [mΩ : MeasurableSpace Ω] (nL nR : ℕ) where
  filtration : Filtration ℝ≥0 mΩ
  W : ℝ≥0 → Ω → ℝ
  VL : Fin nL → ℝ≥0 → Ω → ℝ
  VR : Fin nR → ℝ≥0 → Ω → ℝ
  B : ℝ≥0 → Ω → ℝ
  stop : Ω → ℝ≥0∞

/-- The precise stopped SDE, including continuity through a finite stop.
There is no continuation or conditional driving-law identity in this fact. -/
def LocalDynamics.IsStopped {Ω : Type u} [MeasurableSpace Ω] {nL nR : ℕ}
    (d : LocalDynamics Ω nL nR) (μ : Measure Ω) (κ : ℝ)
    (xL ρL : Fin nL → ℝ) (xR ρR : Fin nR → ℝ) : Prop :=
  Sec2.IsSLEEvolutionUpTo κ xL xR ρL ρR μ d.filtration d.W d.VL d.VR d.B d.stop ∧
    ∀ᵐ ξ ∂μ, ∀ t : ℝ≥0, (t : ℝ≥0∞) = d.stop ξ →
      ContinuousOn (fun v => Coupling.stateAt d.W d.VL d.VR v ξ) (Iic t)

/-- The two exact target orientations of the landed near family. -/
def nearTarget {κ : ℝ} (f : NearCrossingFamily.{u} κ) :
    Set (ℝ × (Fin f.nL → ℝ) × (Fin f.nR → ℝ)) :=
  if f.goLeft then CS3Cross.leftTarget else CS3Cross.rightTarget

def nearBuffer {κ : ℝ} (f : NearCrossingFamily.{u} κ) (n : ℕ) :
    Set (ℝ × (Fin f.nL → ℝ) × (Fin f.nR → ℝ)) :=
  if f.goLeft then CS3Cross.leftBuf f.mL f.nR n else CS3Cross.rightBuf f.nL f.mR n

/-- A fixed near family, with its actual candidate and local dynamics for
each buffer and word. No measurability of this pointwise choice is required. -/
structure NearData (Ω : Type u) [MeasurableSpace Ω] (κ : ℝ) where
  family : NearCrossingFamily.{u} κ
  candidate : ℕ → ℕ → ℕ
  dynamics : ℕ → ℕ → LocalDynamics Ω family.nL family.nR

/-- Word and process data for a required even-stage comparison. Geometric
start conditions and the actual SDE are stated separately. -/
structure SlowData (Ω : Type u) [MeasurableSpace Ω] (κ : ℝ) where
  nL₀ : ℕ
  nR₀ : ℕ
  ρL₀ : Fin nL₀ → ℝ
  ρR₀ : Fin nR₀ → ℝ
  mL : ℕ
  mR : ℕ
  φ : ℕ → ℝ
  xL : Fin (mL + nL₀) → ℝ
  xR : Fin (mR + nR₀ + 1) → ℝ
  start : ℝ
  dynamics : LocalDynamics Ω (mL + nL₀) (mR + nR₀ + 1)

/-- Comparison choices on each complete retained history. They carry no
assertion about the supplied construction's conditional law or buffers. -/
structure ComparisonData {Ω : Type u} [MeasurableSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) where
  near : List (EntryIdx c.Θ c.Q) → Ω → NearData Ω c.κ
  slow : List (EntryIdx c.Θ c.Q) → ℕ → Ω → SlowData Ω c.κ

abbrev ComparisonFamily :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q), ComparisonData c r

end InteractingSLE.Theorem14.GW2JDetR11
