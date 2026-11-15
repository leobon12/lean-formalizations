/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TnOuter
import InteractingSLE.Spec.Sec7.R6FcWireInf

/-!
# R.6's Two face from a named physical landing patch

PROVE-R6-TWO. The geometric input below is explicitly conditional.
The common point, rational selection, time order, seed signs and all
transition-chart clauses are proved using the landed deterministic API.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.R6Tn

open Sec6 PocketTraversal Lemma71C PocketJordan PocketCoord PocketCoupling PocketStop PocketStopField
open HOuter PocketWordAssembly PocketSeedOpen R6Safe R6Two
open R6Fin WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert PocketMarks PocketStopWallsFin PocketStopSide

universe u

/-- **Named, unproved geometric input for Two.** On the original
nested event, all sufficiently close rational inner levels, with the
original live-time, stop-order and current-inclusion conditions, admit
the physical local agreement specified by `IsLandingPatch`.
This is distinct from every source-facing face statement. -/
def R6LandingPatchTwoRemaining (k rL rR c c' : ℝ) : Prop :=
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
          IsLandingPatch (cfPocket (R ω) (L ω) r)
            (cfPocket (R ω) (ML ω) (StripSys.rt s))
            (closure (cfPocket (R ω) (ML ω) (StripSys.rt s)) \ {cfPt (openPt (R ω) (ML ω) (StripSys.rt s))})
            (currentChart A R L r η ψ n (StripSys.rt q) ω)
            (currentChart A' R ML (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)
            (leftSeed (travAll R L r η ψ) (StripSys.rt q) ω)

/-- The original positional face at all nearby rational levels follows
from the named physical landing-patch input (Two). -/
theorem r6FaceSTwoRemaining_of_landingPatch {k rL rR c c' : ℝ}
    (hPatch : R6LandingPatchTwoRemaining.{u} k rL rR c c') :
    R6FaceSTwoRemaining.{u} k rL rR c c' := by
  intro hL hR Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML
    r A A' ψ ψ' n n' s q hA hA'
  filter_upwards [hPatch hL hR P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML
    r A A' ψ ψ' n n' s q hA hA'] with ω hPatchω hωA hωA' hωN
  obtain ⟨εP, hεP, hpatch⟩ := hPatchω hωA hωA' hωN
  obtain ⟨hq0, hqlive, -, hsub, u, hu0, hcap, hrel, -⟩ := hωN
  have hγ : IsDrivenCurve (travAll R L r η ψ ω) := ((hA ω hωA).1.props (hA ω hωA).2).1
  have hγV : IsDrivenCurve (travAll R ML (StripSys.rt s) η ψ' ω) :=
    ((hA' ω hωA').1.props (hA' ω hωA').2).1
  have hrtq : ((StripSys.rt q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ (by exact_mod_cast hq0.le)
  have hqpos : 0 < StripSys.rt q := by rw [← NNReal.coe_pos, hrtq]; exact_mod_cast hq0
  have hinv : capInv (travAll R L r η ψ ω) ((StripSys.rt q : ℝ≥0) : ℝ) = u := by
    rw [hrtq, ← hcap]
    exact hγ.capInv_eq hu0
  have htip : η ω (outerFibreEnd R L r η ψ (StripSys.rt q) ω) ∈
      cfPocket (R ω) (ML ω) (StripSys.rt s) := by
    unfold outerFibreEnd
    rw [hinv]
    exact hrel
  have htipC : capTrace (travAll R L r η ψ ω) (StripSys.rt q) ∈ H := by
    change ψ ω (η ω (outerFibreEnd R L r η ψ (StripSys.rt q) ω)) ∈ H
    exact (hA ω hωA).2.2.2.2.1.2.mapsTo (hsub htip)
  obtain ⟨MC, hvL, hvR⟩ := outer_boundaryChart (n := n)
    (fun ω hω => (hA ω hω).1) (fun ω hω => (hA ω hω).2) hωA hqpos hqlive htipC
  have hT0 : 0 ≤ outerFibreEnd R L r η ψ (StripSys.rt q) ω :=
    (hA ω hωA).1.erase.nonneg.trans ((hA ω hωA).1.erase.fibre_mem _).1
  obtain ⟨hc0, εT, hεT, htipV⟩ := tips_after_visit
    ((hA' ω hωA').1.toPocket (hA' ω hωA').2) hT0 htip
  refine ⟨min εP εT, lt_min hεP hεT, fun q' hlo hhi hlive htime hincl => ?_⟩
  have hq'pos : (0 : ℝ) < q' := hc0.trans_lt hlo
  have hrt' : ((StripSys.rt q' : ℝ≥0) : ℝ) = q' := Real.coe_toNNReal _ hq'pos.le
  have htipV' : capTrace (travAll R ML (StripSys.rt s) η ψ' ω) (StripSys.rt q') ∈ H :=
    htipV (StripSys.rt q') (by rwa [hrt'])
      (by rw [hrt']; exact hhi.trans_le (add_le_add le_rfl (min_le_right _ _)))
  obtain ⟨MV, hwL, -⟩ := outer_boundaryChart (n := n')
    (fun ω hω => (hA' ω hω).1) (fun ω hω => (hA' ω hω).2) hωA'
    (by rw [← NNReal.coe_pos, hrt']; exact hq'pos) hlive htipV'
  have hpatch' := hpatch q' hlo (hhi.trans_le (add_le_add le_rfl (min_le_left _ _))) hlive htime hincl
  obtain ⟨hcO, -, -⟩ := R5Phase.shiftChart_dom_facts (n := n)
    (fun ω hω => (hA ω hω).1.erase.isOpen)
    (fun ω hω => ((hA ω hω).1.toPocket (hA ω hω).2).subset_H)
    (fun ω hω => (hA ω hω).2.2.2.2.1) ω hωA
  obtain ⟨hcI, -, -⟩ := R5Phase.shiftChart_dom_facts (n := n')
    (fun ω hω => (hA' ω hω).1.erase.isOpen)
    (fun ω hω => ((hA' ω hω).1.toPocket (hA' ω hω).2).subset_H)
    (fun ω hω => (hA' ω hω).2.2.2.2.1) ω hωA'
  rw [R6Fc.pocketSet_eq hωA hqlive hγ hcO,
    R6Fc.pocketSet_eq hωA' hlive hγV hcI]
  exact r6FaceR_left_of_landingPatch MC MV hsub hincl hvL hvR hwL rfl hpatch'

/-- The original Q face, including its common point and stop order,
from the named physical landing-patch input (Two). -/
theorem r6FaceQTwoRemaining_of_landingPatch {k rL rR c c' : ℝ}
    (hPatch : R6LandingPatchTwoRemaining.{u} k rL rR c c') :
    R6FaceQTwoRemaining.{u} k rL rR c c' :=
  r6FaceQTwoRemaining_of_faceS (r6FaceSTwoRemaining_of_landingPatch hPatch)

end InteractingSLE.Sec7.R6Tn
