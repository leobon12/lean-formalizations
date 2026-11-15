/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TwoSelect

/-!
# R.6: the two-outer faces reduced to the positional face near the tip

PROVE-R6-TWO. The common point, ordered stops and current-domain
inclusion have been proved for all three shapes. These conditional
adapters isolate the remaining `R6FaceR` obligation; they do not assert
that the required interval and force-mark landings have been supplied.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.R6Two

open Sec6 PocketTraversal Lemma71C PocketJordan PocketCoord PocketCoupling PocketStop PocketStopField
open HOuter PocketWordAssembly PocketSeedOpen R6Safe
open R6Fin WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert PocketMarks PocketStopWallsFin PocketStopSide

universe u

/-- The remaining positional face for `Two` at all rational inner
levels in some right neighbourhood of the visited inner capacity. This
is an internal conditional input, distinct from the source theorem. -/
def R6FaceSTwoRemaining (k rL rR c c' : ℝ) : Prop :=
  k / 2 - 4 < rL → k / 2 - 4 < rR →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsOuterCfg (R ω) (ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (R ω) (ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEvent R L r η ψ MR ML R ML s q →
        ∃ ε > 0, ∀ q' : ℚ, innerRelCap R ML (StripSys.rt s) η ψ' (outerFibreEnd R L r η ψ (StripSys.rt q) ω) ω < q' →
          (q' : ℝ) < innerRelCap R ML (StripSys.rt s) η ψ' (outerFibreEnd R L r η ψ (StripSys.rt q) ω) ω + ε →
          ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAll R ML (StripSys.rt s) η ψ' ω) →
          pocketFibre (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
              (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))
              (clockOf (pocketClock (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
                (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)))
                (capInv (travAll R L r η ψ ω) (StripSys.rt q))) <
            PocketStopWallsFin.ambTime0 (η ω) (cfPocket (R ω) (ML ω) (StripSys.rt s))
              (firstHit (η ω) (cfArcR (R ω) (ML ω) (StripSys.rt s) 1))
              (firstHit (η ω) (cfArcR (R ω) (ML ω) (StripSys.rt s) 0)) (ψ' ω) (StripSys.rt q') →
          ((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R ω)
                (ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAll R ML (StripSys.rt s) η ψ') (StripSys.rt q') ω).dom : Set ℂ) ⊆
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAll R L r η ψ) (StripSys.rt q) ω).dom →
          R6FaceR (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL)
            (fun _ : Fin 1 => k / 2 - 4)
            (fun i => geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
              (StripSys.rt q) ω - segDriver (travAll R L r η ψ ω) (StripSys.rt q))
            (fun j => geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
              (StripSys.rt q) ω - segDriver (travAll R L r η ψ ω) (StripSys.rt q))
            (fun i => geomLW (fun t ω => segDriver (travAll R ML
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
              segDriver (travAll R ML (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (fun j => geomRW (fun t ω => segDriver (travAll R ML
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
              segDriver (travAll R ML (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAll R L r η ψ) (StripSys.rt q) ω)
            (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R ω)
                (ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAll R ML (StripSys.rt s) η ψ') (StripSys.rt q') ω)
            (pocketSet A R L r η ψ n (StripSys.rt q) ω)
            (pocketSet A' R ML (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)

/-- The common-point and time-order clauses for `Two` are discharged;
only the positional face remains in this conditional adapter. -/
theorem r6FaceQTwoRemaining_of_faceS {k rL rR c c' : ℝ}
    (hS : R6FaceSTwoRemaining.{u} k rL rR c c') :
    R6FaceQTwoRemaining.{u} k rL rR c c' := by
  intro hL hR Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA hA'
  filter_upwards [hS hL hR P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML
    r A A' ψ ψ' n n' s q hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨ε, hε, hFace⟩ := hω hωA hωA' hωN
  obtain ⟨hq0, hqlive, -, hsub, u, hu0, hcap, hrel, -⟩ := hωN
  have hγ : IsDrivenCurve (travAll R L r η ψ ω) := (((hA ω hωA).1).props (hA ω hωA).2).1
  have hrtq : ((StripSys.rt q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ (by exact_mod_cast hq0.le)
  have hinv : capInv (travAll R L r η ψ ω) ((StripSys.rt q : ℝ≥0) : ℝ) = u := by
    rw [hrtq, ← hcap]
    exact hγ.capInv_eq hu0
  have htip : η ω (outerFibreEnd R L r η ψ (StripSys.rt q) ω) ∈ cfPocket (R ω) (ML ω) (StripSys.rt s) := by
    unfold outerFibreEnd
    rw [hinv]
    exact hrel
  obtain ⟨q', hlo, hhi, hlive, htime, hmeet, hincl⟩ := exists_rat_meet_near_tip_two
    (n := n) (n' := n') (fun ω hω => (hA ω hω).1) (fun ω hω => (hA ω hω).2) hωA hqlive
    (fun ω hω => (hA' ω hω).1) (fun ω hω => (hA' ω hω).2) hωA' hsub htip hε
  exact ⟨q', hlive, htime.le, hmeet, hFace q' hlo hhi hlive htime hincl⟩

/-- The remaining positional face for `TwoInf` at all rational inner
levels in some right neighbourhood of the visited inner capacity. This
is an internal conditional input, distinct from the source theorem. -/
def R6FaceSTwoInfRemaining (k rL rR c c' : ℝ) : Prop :=
  k / 2 - 4 < rL → k / 2 - 4 < rR →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsOuterCfg (R ω) (ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (R ω) (ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEventInf R L r η ψ MR ML R ML s q →
        ∃ ε > 0, ∀ q' : ℚ, innerRelCap R ML (StripSys.rt s) η ψ' (outerFibreEndInf R L r η ψ (StripSys.rt q) ω) ω < q' →
          (q' : ℝ) < innerRelCap R ML (StripSys.rt s) η ψ' (outerFibreEndInf R L r η ψ (StripSys.rt q) ω) ω + ε →
          ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAll R ML (StripSys.rt s) η ψ' ω) →
          pocketFibreInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))
              (clockOf (clockEnd (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)))
                (capInv (travAllInf R L r η ψ ω) (StripSys.rt q))) <
            PocketStopWallsFin.ambTime0 (η ω) (cfPocket (R ω) (ML ω) (StripSys.rt s))
              (firstHit (η ω) (cfArcR (R ω) (ML ω) (StripSys.rt s) 1))
              (firstHit (η ω) (cfArcR (R ω) (ML ω) (StripSys.rt s) 0)) (ψ' ω) (StripSys.rt q') →
          ((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R ω)
                (ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAll R ML (StripSys.rt s) η ψ') (StripSys.rt q') ω).dom : Set ℂ) ⊆
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAllInf R L r η ψ) (StripSys.rt q) ω).dom →
          R6FaceR (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL)
            (fun _ : Fin 1 => k / 2 - 4)
            (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun i => geomLW (fun t ω => segDriver (travAll R ML
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
              segDriver (travAll R ML (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (fun j => geomRW (fun t ω => segDriver (travAll R ML
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
              segDriver (travAll R ML (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAllInf R L r η ψ) (StripSys.rt q) ω)
            (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R ω)
                (ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAll R ML (StripSys.rt s) η ψ') (StripSys.rt q') ω)
            (pocketSetInf A R L r η ψ n (StripSys.rt q) ω)
            (pocketSet A' R ML (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)

/-- The common-point and time-order clauses for `TwoInf` are discharged;
only the positional face remains in this conditional adapter. -/
theorem r6FaceQTwoInfRemaining_of_faceS {k rL rR c c' : ℝ}
    (hS : R6FaceSTwoInfRemaining.{u} k rL rR c c') :
    R6FaceQTwoInfRemaining.{u} k rL rR c c' := by
  intro hL hR Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA hA'
  filter_upwards [hS hL hR P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML
    r A A' ψ ψ' n n' s q hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨ε, hε, hFace⟩ := hω hωA hωA' hωN
  obtain ⟨hq0, hqlive, -, hsub, u, hu0, hcap, hrel, -⟩ := hωN
  have hγ : IsDrivenCurve (travAllInf R L r η ψ ω) := (((hA ω hωA).1).props (hA ω hωA).2).1
  have hrtq : ((StripSys.rt q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ (by exact_mod_cast hq0.le)
  have hinv : capInv (travAllInf R L r η ψ ω) ((StripSys.rt q : ℝ≥0) : ℝ) = u := by
    rw [hrtq, ← hcap]
    exact hγ.capInv_eq hu0
  have htip : η ω (outerFibreEndInf R L r η ψ (StripSys.rt q) ω) ∈ cfPocket (R ω) (ML ω) (StripSys.rt s) := by
    unfold outerFibreEndInf
    rw [hinv]
    exact hrel
  obtain ⟨q', hlo, hhi, hlive, htime, hmeet, hincl⟩ := exists_rat_meet_near_tip_twoInf
    (n := n) (n' := n') (fun ω hω => (hA ω hω).1) (fun ω hω => (hA ω hω).2) hωA hqlive
    (fun ω hω => (hA' ω hω).1) (fun ω hω => (hA' ω hω).2) hωA' hsub htip hε
  exact ⟨q', hlive, htime.le, hmeet, hFace q' hlo hhi hlive htime hincl⟩

/-- The remaining positional face for `TwoInfInf` at all rational inner
levels in some right neighbourhood of the visited inner capacity. This
is an internal conditional input, distinct from the source theorem. -/
def R6FaceSTwoInfInfRemaining (k rL rR c c' : ℝ) : Prop :=
  k / 2 - 4 < rL → k / 2 - 4 < rR →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsOuterCfgInf (R ω) (ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (R ω) (ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEventInf R L r η ψ MR ML R ML s q →
        ∃ ε > 0, ∀ q' : ℚ, innerRelCapInf R ML (StripSys.rt s) η ψ'
          (outerFibreEndInf R L r η ψ (StripSys.rt q) ω) ω < q' →
          (q' : ℝ) < innerRelCapInf R ML (StripSys.rt s) η ψ' (outerFibreEndInf R L r η ψ (StripSys.rt q) ω) ω + ε →
          ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAllInf R ML (StripSys.rt s) η ψ' ω) →
          pocketFibreInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))
              (clockOf (clockEnd (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)))
                (capInv (travAllInf R L r η ψ ω) (StripSys.rt q))) <
            PocketStopWallsFin.ambTime0Inf (η ω) (cfPocket (R ω) (ML ω) (StripSys.rt s))
              (firstHit (η ω) (cfArcRInf (R ω) (ML ω) (StripSys.rt s) 0)) (ψ' ω) (StripSys.rt q') →
          ((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R ω)
                (ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAllInf R ML (StripSys.rt s) η ψ') (StripSys.rt q') ω).dom : Set ℂ) ⊆
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAllInf R L r η ψ) (StripSys.rt q) ω).dom →
          R6FaceR (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL)
            (fun _ : Fin 1 => k / 2 - 4)
            (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun i => geomLW (fun t ω => segDriver (travAllInf R ML
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
              segDriver (travAllInf R ML (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (fun j => geomRW (fun t ω => segDriver (travAllInf R ML
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
              segDriver (travAllInf R ML (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAllInf R L r η ψ) (StripSys.rt q) ω)
            (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R ω)
                (ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAllInf R ML (StripSys.rt s) η ψ') (StripSys.rt q') ω)
            (pocketSetInf A R L r η ψ n (StripSys.rt q) ω)
            (pocketSetInf A' R ML (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)

/-- The common-point and time-order clauses for `TwoInfInf` are discharged;
only the positional face remains in this conditional adapter. -/
theorem r6FaceQTwoInfInfRemaining_of_faceS {k rL rR c c' : ℝ}
    (hS : R6FaceSTwoInfInfRemaining.{u} k rL rR c c') :
    R6FaceQTwoInfInfRemaining.{u} k rL rR c c' := by
  intro hL hR Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA hA'
  filter_upwards [hS hL hR P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML
    r A A' ψ ψ' n n' s q hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨ε, hε, hFace⟩ := hω hωA hωA' hωN
  obtain ⟨hq0, hqlive, -, hsub, u, hu0, hcap, hrel, -⟩ := hωN
  have hγ : IsDrivenCurve (travAllInf R L r η ψ ω) := (((hA ω hωA).1).props (hA ω hωA).2).1
  have hrtq : ((StripSys.rt q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ (by exact_mod_cast hq0.le)
  have hinv : capInv (travAllInf R L r η ψ ω) ((StripSys.rt q : ℝ≥0) : ℝ) = u := by
    rw [hrtq, ← hcap]
    exact hγ.capInv_eq hu0
  have htip : η ω (outerFibreEndInf R L r η ψ (StripSys.rt q) ω) ∈ cfPocket (R ω) (ML ω) (StripSys.rt s) := by
    unfold outerFibreEndInf
    rw [hinv]
    exact hrel
  obtain ⟨q', hlo, hhi, hlive, htime, hmeet, hincl⟩ := exists_rat_meet_near_tip_twoInfInf
    (n := n) (n' := n') (fun ω hω => (hA ω hω).1) (fun ω hω => (hA ω hω).2) hωA hqlive
    (fun ω hω => (hA' ω hω).1) (fun ω hω => (hA' ω hω).2) hωA' hsub htip hε
  exact ⟨q', hlive, htime.le, hmeet, hFace q' hlo hhi hlive htime hincl⟩

end InteractingSLE.Sec7.R6Two
