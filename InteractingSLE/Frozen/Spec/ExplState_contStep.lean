import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Interval.Finset.Fin
import QuantumZipper.Loewner.Forward
import QuantumZipper.GFF.Kernels
import LQGMetric.Field.ZeroBoundary
import InteractingSLE.Frozen.Spec.PiecewiseConstantBoundaryData_jumpSet
import InteractingSLE.Frozen.Spec.PiecewiseConstantBoundaryData_leftLim
import InteractingSLE.Frozen.Spec.PiecewiseConstantBoundaryData_rightLim
import InteractingSLE.Frozen.Spec.sleLambda
import InteractingSLE.Frozen.Spec.ExplState
import InteractingSLE.Frozen.Spec.ExplState_moveAlong
import InteractingSLE.Frozen.Spec.ExplState_moveToEnd

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

open Classical in
/-- The boundary-continuation step (GW2a, p. 623; BW2 and GW1 for the extreme angles), for boundary data `b`
(locally constant off `jumps`): at a right threshold for the current angle `θ`, move outward through the intervals
with `H + θχ ≤ −λ` and restart at the first later original jump `w` with `H(w⁺) + θχ > −λ` (or follow the boundary to
`∞` if there is none); reflected at a left threshold (`H + θχ ≥ λ`, restart where `H(w⁻) + θχ < λ`). At an
immediately inadmissible seed the bad side gives the direction (`pref` if both are bad). From an interior point of
a recorded connector the same continuation goes on; at a restart mark it is complete (no change).
`vStop = some v` stops at `v` if `v` lies strictly inside the forced arc. At an interior tip or the root no boundary
continuation is available (status *dead*). -/
def ExplState.contStep (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (s : ExplState) (vStop : Option ℝ)
    (pref : Bool) : ExplState :=
  let (pieces, arcs, retained, launches, chart, status, pt, θ, recR, recL) := s
  let χ := QuantumZipper.chiC κ
  let lam := sleLambda κ
  let bR := PiecewiseConstantBoundaryData.rightLim b
  let bL := PiecewiseConstantBoundaryData.leftLim b
  let dir : Option Bool :=
    match status with
    | .inr (.inr (.inl (some r))) => some r  -- thr (some r)
    | .inr (.inr (.inl none)) =>  -- thr none
        if bR pt + θ * χ ≤ -lam ∧ lam ≤ bL pt + θ * χ then some pref
        else if bR pt + θ * χ ≤ -lam then some true
        else if lam ≤ bL pt + θ * χ then some false
        else none
    | .inr (.inr (.inr (.inl (r, false)))) => some r  -- onArc r false
    | _ => none
  match status, dir with
  | .inr (.inr (.inr (.inl (_, true)))), _ => s  -- onArc _ true
  | .inr (.inr (.inr (.inr (.inl ())))), _ => s  -- done
  | _, none =>  -- dead
      (pieces, arcs, retained, launches, chart, .inr (.inr (.inr (.inr (.inr ())))), pt, θ, recR, recL)
  | _, some true =>
      let C := (PiecewiseConstantBoundaryData.jumpSet b jumps).filter
        (fun x => pt < x ∧ -lam < bR x + θ * χ)
      if hC : C.Nonempty then
        (match vStop with
          | some v => if pt < v ∧ v < C.min' hC then ExplState.moveAlong s true v false
                      else ExplState.moveAlong s true (C.min' hC) true
          | none => ExplState.moveAlong s true (C.min' hC) true)
      else
        (match vStop with
          | some v => if pt < v then ExplState.moveAlong s true v false else ExplState.moveToEnd s true
          | none => ExplState.moveToEnd s true)
  | _, some false =>
      let C := (PiecewiseConstantBoundaryData.jumpSet b jumps).filter
        (fun x => x < pt ∧ bL x + θ * χ < lam)
      if hC : C.Nonempty then
        (match vStop with
          | some v => if C.max' hC < v ∧ v < pt then ExplState.moveAlong s false v false
                      else ExplState.moveAlong s false (C.max' hC) true
          | none => ExplState.moveAlong s false (C.max' hC) true)
      else
        (match vStop with
          | some v => if v < pt then ExplState.moveAlong s false v false else ExplState.moveToEnd s false
          | none => ExplState.moveToEnd s false)

end InteractingSLE
