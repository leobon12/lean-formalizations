/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR11Data

/-!
# The two exact construction properties for GW2 near and slow comparisons

These properties are internal inputs authorized by the orchestrator.
They contain actual local SDEs and deterministic buffer/observation facts,
and contain no model probability, numerical estimate or full-law identity.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2JDetR11

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootL6 Sec5

/-- Local stopped dynamics under exactly the full retained-history kernel.
Near words may omit a buffer-dependent finite initial segment. -/
structure RetainedStoppedSDEStatement (D : ConstructionFamily.{u})
    (C : ComparisonFamily.{u}) : Prop where
  near : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
    ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l →
      ∀ n, ∀ᶠ m in atTop,
        let z := (C Ω c r).near l ω
        (z.dynamics n m).IsStopped (condExpKernel c.P (c.sigma r l) ω) c.κ
          z.family.xL (z.family.ρLs m) z.family.xR (z.family.ρRs m)
  slow : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (k : ℕ)
    (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a,
    ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l →
      let z := (C Ω c r).slow l a ω
      z.dynamics.IsStopped (condExpKernel c.P (c.sigma r l) ω) c.κ
        z.xL (angleWordL c.κ z.φ z.mL z.ρL₀)
        z.xR (angleWordR c.κ z.φ z.mR z.ρR₀)

/-- The near buffer fact at one retained state: positive stop, exit from
the reference buffer at that stop, and interpretation of a physical target
visit as the supplied experiment's reach event. All assertions are pathwise. -/
def NearBufferFact {Ω : Type u} [MeasurableSpace Ω] {κ : ℝ}
    (z : NearData Ω κ) (μ : Measure Ω) (sample : ℕ → Ω → RootV7.DriverRecord)
    (reach : ℕ → Set RootV7.DriverRecord) (n m : ℕ) : Prop :=
  MeasurableSet (reach (z.candidate n m)) ∧
    ∀ᵐ ξ ∂μ, 0 < (z.dynamics n m).stop ξ ∧
      (∀ v : ℝ≥0, (v : ℝ≥0∞) = (z.dynamics n m).stop ξ → v < (n : ℝ≥0) →
        Coupling.stateAt (z.dynamics n m).W (z.dynamics n m).VL
          (z.dynamics n m).VR v ξ ∉ nearBuffer z.family n) ∧
      ∀ t : ℝ≥0, t < (n : ℝ≥0) → (t : ℝ≥0∞) < (z.dynamics n m).stop ξ →
        Coupling.stateAt (z.dynamics n m).W (z.dynamics n m).VL
          (z.dynamics n m).VR t ξ ∈ nearTarget z.family →
        sample (z.candidate n m) ξ ∈ reach (z.candidate n m)

/-- The slow buffer fact: the literal separated starting word, its common
drift constant and the physical sample's live readings before its stop. -/
def SlowBufferFact {Ω : Type u} [MeasurableSpace Ω] {κ : ℝ}
    (z : SlowData Ω κ) (μ : Measure Ω) (driftBound : ℝ)
    (sample : Ω → RootV7.DriverRecord) : Prop :=
  (∀ i, z.φ i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) ∧
    (z.start, z.xL, z.xR) ∈ Prop59Stage.startsU ∧
    driftBound = Prop59Stage.stageDriftBound κ z.ρL₀ z.ρR₀ ∧
    (∀ᵐ ξ ∂μ, (sample ξ).1 ≤ z.dynamics.stop ξ) ∧
    ∀ᵐ ξ ∂μ, ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < (sample ξ).1 →
      (sample ξ).2 q = z.start + z.dynamics.W q ξ

/-- Buffer and observation geometry for the same choices as the SDE fact.
The near and SDE tails may be different; the proof intersects them. -/
structure RetainedBufferStatement (D : ConstructionFamily.{u})
    (C : ComparisonFamily.{u}) : Prop where
  near : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
    ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l →
      ∀ n, ∀ᶠ m in atTop, NearBufferFact ((C Ω c r).near l ω)
        (condExpKernel c.P (c.sigma r l) ω) (((D Ω c).experiment r).data.sample l)
        (((D Ω c).experiment r).data.reach l) n m
  slow : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (k : ℕ)
    (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a,
    ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l →
      SlowBufferFact ((C Ω c r).slow l a ω) (condExpKernel c.P (c.sigma r l) ω)
        ((D Ω c).experiment r).driftBound (((D Ω c).experiment r).data.sample l a)

end InteractingSLE.Theorem14.GW2JDetR11
