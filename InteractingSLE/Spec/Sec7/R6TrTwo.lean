/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TrInputs

/-!
# The original two-outer face from the common-time geometric input

PROVE-R6-TWO, R98. The consumer uses the proved window at every nearby
real time, then specializes to the original rational interface.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.R6Tr

open Sec6 PocketTraversal Lemma71C PocketJordan PocketCoord PocketCoupling PocketStop PocketStopField
open HOuter PocketWordAssembly PocketSeedOpen R6Safe R6Two R6Tn
open R6Fin WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert PocketMarks PocketStopWallsFin PocketStopSide

universe u

/-- Conditional adapter from the true common-time geometry, allowing seed corners. -/
theorem r6FaceSTwoRemaining_of_sameTime {k rL rR c c' : ℝ}
    (hG : R6SameTimeTwoRemaining.{u} k rL rR c c') :
    R6FaceSTwoRemaining.{u} k rL rR c c' := by
  intro hL hR Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML
    r A A' ψ ψ' n n' s q hA hA'
  filter_upwards [hG hL hR P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML
    r A A' ψ ψ' n n' s q hA hA'] with ω hGω hωA hωA' hωN
  have hgeom := hGω hωA hωA' hωN
  obtain ⟨hq0, hqlive, -, hsub, u, hu0, hcap, hrel, -⟩ := hωN
  have hγ : IsDrivenCurve (travAll R L r η ψ ω) := ((hA ω hωA).1.props (hA ω hωA).2).1
  have hrtq : ((StripSys.rt q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ (by exact_mod_cast hq0.le)
  have hqpos : 0 < StripSys.rt q := by rw [← NNReal.coe_pos, hrtq]; exact_mod_cast hq0
  have hinv : capInv (travAll R L r η ψ ω) ((StripSys.rt q : ℝ≥0) : ℝ) = u := by
    rw [hrtq, ← hcap]; exact hγ.capInv_eq hu0
  have htip : η ω (outerFibreEnd R L r η ψ (StripSys.rt q) ω) ∈
      cfPocket (R ω) (ML ω) (StripSys.rt s) := by
    unfold outerFibreEnd; rw [hinv]; exact hrel
  have htipC : capTrace (travAll R L r η ψ ω) (StripSys.rt q) ∈ H := by
    change ψ ω (η ω (outerFibreEnd R L r η ψ (StripSys.rt q) ω)) ∈ H
    exact (hA ω hωA).2.2.2.2.1.2.mapsTo (hsub htip)
  obtain ⟨MC, -, -⟩ := outer_boundaryChart (n := n)
    (fun ω hω => (hA ω hω).1) (fun ω hω => (hA ω hω).2) hωA hqpos hqlive htipC
  have hT0 : 0 ≤ outerFibreEnd R L r η ψ (StripSys.rt q) ω :=
    (hA ω hωA).1.erase.nonneg.trans ((hA ω hωA).1.erase.fibre_mem _).1
  obtain ⟨M, hMt, hmarks⟩ := innerChain_of_visit (n := n')
    (fun ω hω => (hA' ω hω).1) (fun ω hω => (hA' ω hω).2) hωA' hT0 htip
  obtain ⟨θ, hθ, J, y, ξ, hfuture⟩ := faceAt_near_of_sameTime
    (ρL := fun _ : Fin 1 => rL) (ρR := fun _ : Fin 1 => rR)
    (σL := fun _ : Fin 1 => rL) (σR := fun _ : Fin 1 => k / 2 - 4)
    (vL := fun _ : Fin 1 => leftSeed (travAll R L r η ψ) (StripSys.rt q) ω)
    (vR := fun _ : Fin 1 => rightSeed (travAll R L r η ψ) (StripSys.rt q) ω)
    hgeom M hMt hmarks MC.conformal
    (fun q' _ => rightSeed (travAll R ML (StripSys.rt s) η ψ') q'.toNNReal ω) rfl
  have hγV : IsDrivenCurve (travAll R ML (StripSys.rt s) η ψ' ω) :=
    ((hA' ω hωA').1.props (hA' ω hωA').2).1
  refine ⟨θ, hθ, fun q' hlo hhi hlive _htime _hincl => ?_⟩
  have hf := (hfuture (q' : ℝ) hlo hhi).r6FaceR
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
  exact hf

/-- The original Q face, with common point and ordered stops, from the
same-time incident-face geometry. -/
theorem r6FaceQTwoRemaining_of_sameTime {k rL rR c c' : ℝ}
    (hG : R6SameTimeTwoRemaining.{u} k rL rR c c') :
    R6FaceQTwoRemaining.{u} k rL rR c c' :=
  r6FaceQTwoRemaining_of_faceS (r6FaceSTwoRemaining_of_sameTime hG)

end InteractingSLE.Sec7.R6Tr
