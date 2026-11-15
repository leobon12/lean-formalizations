/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootJ31Readout
import InteractingSLE.Spec.Supplement.GW2CvStatement

/-!
# Concrete construction data for the C24 / assembled6 interface

Packet PROVE-T14-GW2ROOT2. This supplies D as actual data, using source
programs, old death flags, a future buffer, relative-capacity samples,
and the full retained conditional pushforward. It does not assert
RootGeometryStatement D or either JOINTDET comparison property. In
particular the all-outcome causal gate, literal capacity measurability,
and the source identification of the restarted reader remain to prove.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootJ31

open Exist Staged StagedLaw Restart RootC24 RootK3

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- Concrete future experiments. The kernel is already the full retained
conditional pushforward. The legacy p₀ field is unused by C24, whose
assembly obtains the actual positive constant from Lemma 5.10. -/
def experimentData (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    StageModelData Ω c.Θ c.Q RootV7.DriverRecord (c.sigma r) where
  ang := candidateAngle c r
  X := sourceX c r
  γ := sourceTip c r
  S := sourceEntry c r
  F := sourceFailure c r
  I := fun _ _ => Ioo (7 / 4) (9 / 4)
  sample := sourceSample c r
  kernel := fun l a => Kernel.mapOfMeasurable (condExpKernel c.P (c.sigma r l))
    (sourceSample c r l a) (measurable_sourceSample c r l a)
  reach := fun _ _ => RootD25.reachSet
  slow := fun _ _ => RootV7.slowSet
  p₀ := 1

/-- The source's original finite force weights give one fixed drift parameter.
Its compatibility with the actual joint-chart comparison word is not asserted here. -/
def sourceDriftBound (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) : ℝ :=
  Sec5.Prop59Stage.stageDriftBound c.κ
    (flowLineRhoL c.κ c.b c.jumps (rootPt r.1) 0)
    (flowLineRhoR c.κ c.b c.jumps (rootPt r.1) 0)

def experiment (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) : Experiment c r where
  data := experimentData c r
  sampleMeas := measurable_sourceSample c r
  driftBound := sourceDriftBound c r
  Y := sourceDriver c r
  clock := fun l a q => sourceClock c r l a q

/-- Explicit construction data with the already proved physical root cover. -/
def construction (c : SourceData Ω) : Construction c where
  G := RootCv.coverEvent c
  experiment := experiment c

/-- The data argument D of the unchanged C24 / assembled6 statements. -/
def constructionFamily : ConstructionFamily.{u} := fun _ _ _ c => construction c

/-- Applying COVER's wrapper makes no change to this construction. -/
theorem withCover_constructionFamily :
    RootCv.withCover constructionFamily.{u} = constructionFamily.{u} := rfl

/-- The complete cover input is proved for this concrete D. -/
theorem rootCoverStatement (h13 : Theorem13Statement.{u})
    (h13₀ : Theorem13Statement.{0}) : RootCoverStatement constructionFamily.{u} :=
  RootCv.rootCoverStatement_of_G_eq h13 h13₀ constructionFamily fun _ _ _ _ => rfl

theorem experiment_band_open (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) : IsOpen ((experiment c r).data.I l a) :=
  isOpen_Ioo

theorem experiment_reach_measurable (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    MeasurableSet ((experiment c r).data.reach l a) := RootD25.measurableSet_reachSet

/-- The exact C24 record-reading field is proved for every root and history. -/
theorem experiment_record_read (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    ∀ᵐ ω ∂c.P, ω ∈ (experiment c r).data.alive ((construction c).G r) l →
      ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < ((experiment c r).data.sample l a ω).1 →
        ((experiment c r).data.sample l a ω).2 q = (experiment c r).Y l a ω q := by
  exact Eventually.of_forall fun ω _ q hq => sourceSample_read c r l a ω hq

/-- The stored conditional kernel is exactly the retained kernel used by C24. -/
theorem experiment_kernel_eq_retained (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    (experiment c r).data.kernel l a ω = (experiment c r).retained.kernel l a ω := rfl

end InteractingSLE.Theorem14.GW2TipSystem.RootJ31
