/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC7Seeds

/-!
# The explicit initial word extension and the remaining mean formula

PROVE-SIDE-COLLAR2. Construct the canonical bounded harmonic extension
at the exact native zero-time coordinates. The remaining named input is
an interior mean identity for one chosen initial local mean per side test.
It has no phase, boundary limit, reference collar or residual-law clause.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketAdapt Sec7.PocketTraversal Sec7.Lemma71C Sec7.Aux117 MartChar

variable {Ω : Type} [MeasurableSpace Ω]

/-- The canonical bounded extension at the literal initial native positions. -/
def initialWordExtension (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω) (ω : Ω) : ℂ → ℝ :=
  meanExt (j.target i d).kappa (j.target i d).rhoL (j.target i d).rhoR 0
    (fun a => geomLW (fun t ω => segDriver ((j.target i d).curve ω) t)
      (j.target i d).marksL a 0 ω - segDriver ((j.target i d).curve ω) 0)
    (fun a => geomRW (fun t ω => segDriver ((j.target i d).curve ω) t)
      (j.target i d).marksR a 0 ω - segDriver ((j.target i d).curve ω) 0)

/-- The initial extension has the exact native force-boundary data. -/
theorem isBoundedHarmonicExtension_initialWordExtension
    (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω) (ω : Ω) :
    IsBoundedHarmonicExtension
      (forceBoundaryData (j.target i d).kappa (j.target i d).rhoL (j.target i d).rhoR
        (fun a => geomLW (fun t ω => segDriver ((j.target i d).curve ω) t)
          (j.target i d).marksL a 0 ω - segDriver ((j.target i d).curve ω) 0)
        (fun a => geomRW (fun t ω => segDriver ((j.target i d).curve ω) t)
          (j.target i d).marksR a 0 ω - segDriver ((j.target i d).curve ω) 0))
      (forceJumpSet
        (fun a => geomLW (fun t ω => segDriver ((j.target i d).curve ω) t)
          (j.target i d).marksL a 0 ω - segDriver ((j.target i d).curve ω) 0)
        (fun a => geomRW (fun t ω => segDriver ((j.target i d).curve ω) t)
          (j.target i d).marksR a 0 ω - segDriver ((j.target i d).curve ω) 0))
      (j.initialWordExtension i d ω) := by
  simpa only [initialWordExtension, sub_zero] using isBoundedHarmonicExtension_meanExt
    (j.target i d).kappa (j.target i d).rhoL (j.target i d).rhoR 0 _ _

end InteractingSLE.Wire.Current.SideTest

namespace InteractingSLE.Wire

open Current LocalSets Sec7.Aux119Heights

/-- Remaining initial mathematics: one local mean has the canonical
interior formula with the actual inherited base lift and common offset.
This is an unproved input predicate, not an existence theorem. -/
def InitialPocketMeanFormula {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) (side : SideTest Ω → Late.SideData Ω)
    (G : SideTest Ω → Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → let target := j.target i d;
    IsLocalSetMean (j.capacityReference i d 0) target.zeroField d.measure (G j) ∧
      ∀ᵐ ω ∂d.measure, ω ∈ target.event → ∀ z ∈ target.domain ω,
        harmRep (G j ω) (H \ j.capacityReference i d 0 ω) z + target.harmonic z +
          chiC target.kappa * (target.baseChart ω).2.2 z =
          j.initialWordExtension i d ω ((target.baseChart ω).1 z) - (side j).offset

end InteractingSLE.Wire
