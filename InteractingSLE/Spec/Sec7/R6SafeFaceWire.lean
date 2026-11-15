/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6SafeFace
import InteractingSLE.Spec.Sec7.R6SafeTwoGeom

/-!
# R.6's face descriptions on R.7 configurations, and the geometry cores from them

PROVE-R6-SAFE. The six named geometry cores of R.6 (`R6Fin.R6GeomCoreMixed{,Inf,InfInf}Remaining`, PROVE-R6-CERT2, and
`R6GeomCoreTwo{,Inf,InfInf}Remaining`, the two-outer-arm transfer from `C` to the intermediate pocket `V`) are reduced
to the corresponding **face descriptions** `R6FaceMixed{,Inf,InfInf}Remaining`, `R6FaceTwo{,Inf,InfInf}Remaining`
(the same quantifiers with `R6Face` in place of `R6Fin.R6GeomCore`): the reflection across `J`, the inherited
logarithm, the collars and the landings are constructed (`r6GeomCore_of_r6Face`), and the generic facts of the two
live current charts (conformality, continuous inverse extension, landings, derivative logarithms) are proved
(`relChart_generic`). What remains is exactly the source's face description (supplement p. 476).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.R6Safe

open R6Fin WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert HOuter PocketCoord PocketJordan PocketMarks
  PocketWordAssembly PocketCoupling PocketStopField Lemma71C Lemma71I PocketTraversal PocketStop PocketSeedOpen

/-! ### The face descriptions -/

/-- **Named, unproved: R.6's face description, shape `Mixed`**:
`R6Fin.R6GeomCoreMixedRemaining` with `R6Face` in place of `R6Fin.R6GeomCore` (the reflection, logarithm,
collars and landings are then constructed, `r6GeomCoreMixedRemaining_of_face`). -/
def R6FaceMixedRemaining (k rL rR c c' : ℝ) : Prop :=
  (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR) →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsCfPocketConfig (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEvent R L r η ψ MR ML (innerRight k rL R MR) (innerLeft k rR L ML) s q →
        ∃ q' : ℚ, ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω) ∧
          R6Face k (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => innerRight k rL rL (k / 2 - 4))
            (fun _ : Fin 1 => innerLeft k rR rR (k / 2 - 4))
            (fun i => geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
              (StripSys.rt q) ω - segDriver (travAll R L r η ψ ω) (StripSys.rt q))
            (fun j => geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
              (StripSys.rt q) ω - segDriver (travAll R L r η ψ ω) (StripSys.rt q))
            (fun i => geomLW (fun t ω => segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
              segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (fun j => geomRW (fun t ω => segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
              segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAll R L r η ψ) (StripSys.rt q) ω)
            (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (innerRight k rL R MR ω)
                (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') (StripSys.rt q') ω)
            (pocketSet A R L r η ψ n (StripSys.rt q) ω)
            (pocketSet A' (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)

/-- **Named, unproved: R.6's face description, shape `MixedInf`**:
`R6Fin.R6GeomCoreMixedInfRemaining` with `R6Face` in place of `R6Fin.R6GeomCore` (the reflection, logarithm,
collars and landings are then constructed, `r6GeomCoreMixedInfRemaining_of_face`). -/
def R6FaceMixedInfRemaining (k rL rR c c' : ℝ) : Prop :=
  (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR) →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsCfPocketConfig (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEventInf R L r η ψ MR ML (innerRight k rL R MR) (innerLeft k rR L ML) s q →
        ∃ q' : ℚ, ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω) ∧
          R6Face k (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => innerRight k rL rL (k / 2 - 4))
            (fun _ : Fin 1 => innerLeft k rR rR (k / 2 - 4))
            (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun i => geomLW (fun t ω => segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
              segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (fun j => geomRW (fun t ω => segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
              segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAllInf R L r η ψ) (StripSys.rt q) ω)
            (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (innerRight k rL R MR ω)
                (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') (StripSys.rt q') ω)
            (pocketSetInf A R L r η ψ n (StripSys.rt q) ω)
            (pocketSet A' (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)

/-- **Named, unproved: R.6's face description, shape `MixedInfInf`**:
`R6Fin.R6GeomCoreMixedInfInfRemaining` with `R6Face` in place of `R6Fin.R6GeomCore` (the reflection, logarithm,
collars and landings are then constructed, `r6GeomCoreMixedInfInfRemaining_of_face`). -/
def R6FaceMixedInfInfRemaining (k rL rR c c' : ℝ) : Prop :=
  (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR) →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsCfPocketConfigInf (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEventInf R L r η ψ MR ML (innerRight k rL R MR) (innerLeft k rR L ML) s q →
        ∃ q' : ℚ, ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω) ∧
          R6Face k (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => innerRight k rL rL (k / 2 - 4))
            (fun _ : Fin 1 => innerLeft k rR rR (k / 2 - 4))
            (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun i => geomLW (fun t ω => segDriver (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
              segDriver (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (fun j => geomRW (fun t ω => segDriver (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
              segDriver (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAllInf R L r η ψ) (StripSys.rt q) ω)
            (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (innerRight k rL R MR ω)
                (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') (StripSys.rt q') ω)
            (pocketSetInf A R L r η ψ n (StripSys.rt q) ω)
            (pocketSetInf A' (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)

/-- **Named, unproved: R.6's face description, shape `Two`**:
`R6GeomCoreTwoRemaining` with `R6Face` in place of `R6Fin.R6GeomCore` (the reflection, logarithm,
collars and landings are then constructed, `r6GeomCoreTwoRemaining_of_face`). -/
def R6FaceTwoRemaining (k rL rR c c' : ℝ) : Prop :=
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
        ∃ q' : ℚ, ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAll R ML (StripSys.rt s) η ψ' ω) ∧
          R6Face k (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL)
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

/-- **Named, unproved: R.6's face description, shape `TwoInf`**:
`R6GeomCoreTwoInfRemaining` with `R6Face` in place of `R6Fin.R6GeomCore` (the reflection, logarithm,
collars and landings are then constructed, `r6GeomCoreTwoInfRemaining_of_face`). -/
def R6FaceTwoInfRemaining (k rL rR c c' : ℝ) : Prop :=
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
        ∃ q' : ℚ, ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAll R ML (StripSys.rt s) η ψ' ω) ∧
          R6Face k (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL)
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

/-- **Named, unproved: R.6's face description, shape `TwoInfInf`**:
`R6GeomCoreTwoInfInfRemaining` with `R6Face` in place of `R6Fin.R6GeomCore` (the reflection, logarithm,
collars and landings are then constructed, `r6GeomCoreTwoInfInfRemaining_of_face`). -/
def R6FaceTwoInfInfRemaining (k rL rR c c' : ℝ) : Prop :=
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
        ∃ q' : ℚ, ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAllInf R ML (StripSys.rt s) η ψ' ω) ∧
          R6Face k (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL)
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

/-! ### The cores from the face descriptions -/

/-- **`R6Fin.R6GeomCoreMixedRemaining` from the face description**
(`r6GeomCore_of_r6Face` with `relChart_generic` for the two live current charts). -/
theorem r6GeomCoreMixedRemaining_of_face {k rL rR c c' : ℝ}
    (hface : R6FaceMixedRemaining.{u} k rL rR c c') : R6Fin.R6GeomCoreMixedRemaining.{u} k rL rR c c' := by
  intro hmix Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [hface hmix P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s
    q hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨q', hq', hf⟩ := hω hωA hωA' hωN
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hA ω hω).1.conf
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) :=
    fun ω hω => (hA' ω hω).1.conf
  obtain ⟨hOc, -, hOland, LO, hLO, hOl⟩ := relChart_generic (n := n)
    (fun ω hω => isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H)
    (fun ω hω => (hA ω hω).2.2.2.2.1) hωA ((hA ω hωA).1.props (hA ω hωA).2).1 hωN.2.1
    (Or.inl ⟨_, ((hA ω hωA).1.conf.isCfPocket (zero_notMem_closure_of_rightLo_pos (hA ω hωA).1.conf
        (hA ω hωA).1.bounded)).isBounded, (hA ω hωA).1.conf.cfPt_openPt_notMem, (hA ω hωA).2⟩)
  obtain ⟨hIc, ⟨E, hE, hEc⟩, -, LI, hLI, hIl⟩ := relChart_generic (n := n')
    (fun ω hω => isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H)
    (fun ω hω => (hA' ω hω).2.2.2.2.1) hωA' ((hA' ω hωA').1.isDrivenCurve (hA' ω hωA').2).1 hq'
    (Or.inl ⟨_, ((hA' ω hωA').1.conf.isCfPocket (zero_notMem_closure_of_rightLo_pos (hA' ω hωA').1.conf
        (hA' ω hωA').1.bounded)).isBounded, (hA' ω hωA').1.conf.cfPt_openPt_notMem, (hA' ω hωA').2⟩)
  exact ⟨q', hq', r6GeomCore_of_r6Face hOc hIc hE hEc hOland hLO hLI hOl hIl hf⟩

/-- **`R6Fin.R6GeomCoreMixedInfRemaining` from the face description**
(`r6GeomCore_of_r6Face` with `relChart_generic` for the two live current charts). -/
theorem r6GeomCoreMixedInfRemaining_of_face {k rL rR c c' : ℝ}
    (hface : R6FaceMixedInfRemaining.{u} k rL rR c c') : R6Fin.R6GeomCoreMixedInfRemaining.{u} k rL rR c c' := by
  intro hmix Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [hface hmix P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s
    q hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨q', hq', hf⟩ := hω hωA hωA' hωN
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hA ω hω).1.conf
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) :=
    fun ω hω => (hA' ω hω).1.conf
  obtain ⟨hOc, -, hOland, LO, hLO, hOl⟩ := relChart_generic (n := n)
    (fun ω hω => isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H)
    (fun ω hω => (hA ω hω).2.2.2.2.1) hωA ((hA ω hωA).1.props (hA ω hωA).2).1 hωN.2.1
    (Or.inr (hA ω hωA).2)
  obtain ⟨hIc, ⟨E, hE, hEc⟩, -, LI, hLI, hIl⟩ := relChart_generic (n := n')
    (fun ω hω => isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H)
    (fun ω hω => (hA' ω hω).2.2.2.2.1) hωA' ((hA' ω hωA').1.isDrivenCurve (hA' ω hωA').2).1 hq'
    (Or.inl ⟨_, ((hA' ω hωA').1.conf.isCfPocket (zero_notMem_closure_of_rightLo_pos (hA' ω hωA').1.conf
        (hA' ω hωA').1.bounded)).isBounded, (hA' ω hωA').1.conf.cfPt_openPt_notMem, (hA' ω hωA').2⟩)
  exact ⟨q', hq', r6GeomCore_of_r6Face hOc hIc hE hEc hOland hLO hLI hOl hIl hf⟩

/-- **`R6Fin.R6GeomCoreMixedInfInfRemaining` from the face description**
(`r6GeomCore_of_r6Face` with `relChart_generic` for the two live current charts). -/
theorem r6GeomCoreMixedInfInfRemaining_of_face {k rL rR c c' : ℝ}
    (hface : R6FaceMixedInfInfRemaining.{u} k rL rR c c') : R6Fin.R6GeomCoreMixedInfInfRemaining.{u} k rL rR c c' := by
  intro hmix Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [hface hmix P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s
    q hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨q', hq', hf⟩ := hω hωA hωA' hωN
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hA ω hω).1.conf
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) :=
    fun ω hω => (hA' ω hω).1.conf
  obtain ⟨hOc, -, hOland, LO, hLO, hOl⟩ := relChart_generic (n := n)
    (fun ω hω => isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H)
    (fun ω hω => (hA ω hω).2.2.2.2.1) hωA ((hA ω hωA).1.props (hA ω hωA).2).1 hωN.2.1
    (Or.inr (hA ω hωA).2)
  obtain ⟨hIc, ⟨E, hE, hEc⟩, -, LI, hLI, hIl⟩ := relChart_generic (n := n')
    (fun ω hω => isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H)
    (fun ω hω => (hA' ω hω).2.2.2.2.1) hωA' ((hA' ω hωA').1.isDrivenCurve (hA' ω hωA').2).1 hq'
    (Or.inr (hA' ω hωA').2)
  exact ⟨q', hq', r6GeomCore_of_r6Face hOc hIc hE hEc hOland hLO hLI hOl hIl hf⟩

/-- **`R6GeomCoreTwoRemaining` from the face description**
(`r6GeomCore_of_r6Face` with `relChart_generic` for the two live current charts). -/
theorem r6GeomCoreTwoRemaining_of_face {k rL rR c c' : ℝ}
    (hface : R6FaceTwoRemaining.{u} k rL rR c c') : R6GeomCoreTwoRemaining.{u} k rL rR c c' := by
  intro hdL hdR Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [hface hdL hdR P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s
    q hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨q', hq', hf⟩ := hω hωA hωA' hωN
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hA ω hω).1.conf
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (R ω) (ML ω) (StripSys.rt s) :=
    fun ω hω => (hA' ω hω).1.conf
  obtain ⟨hOc, -, hOland, LO, hLO, hOl⟩ := relChart_generic (n := n)
    (fun ω hω => isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H)
    (fun ω hω => (hA ω hω).2.2.2.2.1) hωA ((hA ω hωA).1.props (hA ω hωA).2).1 hωN.2.1
    (Or.inl ⟨_, ((hA ω hωA).1.conf.isCfPocket (zero_notMem_closure_of_rightLo_pos (hA ω hωA).1.conf
        (hA ω hωA).1.bounded)).isBounded, (hA ω hωA).1.conf.cfPt_openPt_notMem, (hA ω hωA).2⟩)
  obtain ⟨hIc, ⟨E, hE, hEc⟩, -, LI, hLI, hIl⟩ := relChart_generic (n := n')
    (fun ω hω => isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H)
    (fun ω hω => (hA' ω hω).2.2.2.2.1) hωA' ((hA' ω hωA').1.props (hA' ω hωA').2).1 hq'
    (Or.inl ⟨_, ((hA' ω hωA').1.conf.isCfPocket (zero_notMem_closure_of_rightLo_pos (hA' ω hωA').1.conf
        (hA' ω hωA').1.bounded)).isBounded, (hA' ω hωA').1.conf.cfPt_openPt_notMem, (hA' ω hωA').2⟩)
  exact ⟨q', hq', r6GeomCore_of_r6Face hOc hIc hE hEc hOland hLO hLI hOl hIl hf⟩

/-- **`R6GeomCoreTwoInfRemaining` from the face description**
(`r6GeomCore_of_r6Face` with `relChart_generic` for the two live current charts). -/
theorem r6GeomCoreTwoInfRemaining_of_face {k rL rR c c' : ℝ}
    (hface : R6FaceTwoInfRemaining.{u} k rL rR c c') : R6GeomCoreTwoInfRemaining.{u} k rL rR c c' := by
  intro hdL hdR Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [hface hdL hdR P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s
    q hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨q', hq', hf⟩ := hω hωA hωA' hωN
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hA ω hω).1.conf
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (R ω) (ML ω) (StripSys.rt s) :=
    fun ω hω => (hA' ω hω).1.conf
  obtain ⟨hOc, -, hOland, LO, hLO, hOl⟩ := relChart_generic (n := n)
    (fun ω hω => isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H)
    (fun ω hω => (hA ω hω).2.2.2.2.1) hωA ((hA ω hωA).1.props (hA ω hωA).2).1 hωN.2.1
    (Or.inr (hA ω hωA).2)
  obtain ⟨hIc, ⟨E, hE, hEc⟩, -, LI, hLI, hIl⟩ := relChart_generic (n := n')
    (fun ω hω => isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H)
    (fun ω hω => (hA' ω hω).2.2.2.2.1) hωA' ((hA' ω hωA').1.props (hA' ω hωA').2).1 hq'
    (Or.inl ⟨_, ((hA' ω hωA').1.conf.isCfPocket (zero_notMem_closure_of_rightLo_pos (hA' ω hωA').1.conf
        (hA' ω hωA').1.bounded)).isBounded, (hA' ω hωA').1.conf.cfPt_openPt_notMem, (hA' ω hωA').2⟩)
  exact ⟨q', hq', r6GeomCore_of_r6Face hOc hIc hE hEc hOland hLO hLI hOl hIl hf⟩

/-- **`R6GeomCoreTwoInfInfRemaining` from the face description**
(`r6GeomCore_of_r6Face` with `relChart_generic` for the two live current charts). -/
theorem r6GeomCoreTwoInfInfRemaining_of_face {k rL rR c c' : ℝ}
    (hface : R6FaceTwoInfInfRemaining.{u} k rL rR c c') : R6GeomCoreTwoInfInfRemaining.{u} k rL rR c c' := by
  intro hdL hdR Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [hface hdL hdR P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s
    q hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨q', hq', hf⟩ := hω hωA hωA' hωN
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hA ω hω).1.conf
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (R ω) (ML ω) (StripSys.rt s) :=
    fun ω hω => (hA' ω hω).1.conf
  obtain ⟨hOc, -, hOland, LO, hLO, hOl⟩ := relChart_generic (n := n)
    (fun ω hω => isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H)
    (fun ω hω => (hA ω hω).2.2.2.2.1) hωA ((hA ω hωA).1.props (hA ω hωA).2).1 hωN.2.1
    (Or.inr (hA ω hωA).2)
  obtain ⟨hIc, ⟨E, hE, hEc⟩, -, LI, hLI, hIl⟩ := relChart_generic (n := n')
    (fun ω hω => isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H)
    (fun ω hω => (hA' ω hω).2.2.2.2.1) hωA' ((hA' ω hωA').1.props (hA' ω hωA').2).1 hq'
    (Or.inr (hA' ω hωA').2)
  exact ⟨q', hq', r6GeomCore_of_r6Face hOc hIc hE hEc hOland hLO hLI hOl hIl hf⟩

end InteractingSLE.Sec7.R6Safe
