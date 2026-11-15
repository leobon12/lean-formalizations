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
import InteractingSLE.Frozen.Spec.Chart_loewner
import InteractingSLE.Frozen.Spec.ExplStatus
import InteractingSLE.Frozen.Spec.ExplState

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

open Classical in
/-- Run an ordinary piece, launched by instruction `k` in the current chart with driver and lifetime `D = (W, ζ)`,
at angle `θ` for own time `t`; it stops at `min t ζ`. Records the piece and its retained datum, updates the original
real records with the real points it swallowed, and classifies its end: an interior tip (switch at an available own
stop), the target, or a finite continuation threshold at a new right or left original record (zero lifetime: at the
seed). -/
def ExplState.launch (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) : ExplState :=
  let (pieces, arcs, retained, launches, chart, status, pt, _, recR, recL) := s
  let stop := min t D.2
  let Ws : ℝ≥0 → ℝ := fun r => D.1 (min (r : ℝ≥0∞) stop).toNNReal
  let Wr : ℝ → ℝ := fun r => Ws r.toNNReal
  let pieces₁ := pieces ++ [(chart, Ws, stop)]
  let retained₁ := Function.update retained k (Ws, stop, decide (D.2 ≤ t))
  let launches₁ := Function.update launches k (some (chart, θ))
  if stop = ⊤ then  -- done
    (pieces₁, arcs, retained₁, launches₁, chart, .inr (.inr (.inr (.inr (.inl ())))), pt, θ, recR, recL)
  else
  let T : ℝ := (stop.toNNReal : ℝ)
  let alive : ℝ → Prop := fun x => ∃ u, QuantumZipper.IsForwardSol Wr (chart.1 x) T u
  let hit : ℝ → Prop := fun x =>
    (∀ r < T, ∃ u, QuantumZipper.IsForwardSol Wr (chart.1 x) r u) ∧ ¬ alive x
  let recR' := sSup (insert recR {x | recR < x ∧ ¬ alive x})
  let recL' := sInf (insert recL {x | x < recL ∧ ¬ alive x})
  -- the state after the piece, with status `st` and current point `q`
  let s₂ : ExplStatus → ℝ → ExplState := fun st q =>
    (pieces₁, arcs, retained₁, launches₁, chart.loewner Wr T, st, q, θ, recR', recL')
  if t < D.2 then s₂ (.inr (.inl ())) pt  -- tip
  else if D.2 = 0 then
    (match status with
      | .inr (.inl ()) => s₂ (.inr (.inr (.inr (.inr (.inr ()))))) pt  -- from a tip: dead
      | _ => s₂ (.inr (.inr (.inl none))) pt)  -- thr none
  else if ∃ x, recR < x ∧ hit x then s₂ (.inr (.inr (.inl (some true)))) recR'  -- thr (some true)
  else if ∃ x, x < recL ∧ hit x then s₂ (.inr (.inr (.inl (some false)))) recL'  -- thr (some false)
  else s₂ (.inr (.inr (.inr (.inr (.inr ()))))) pt  -- dead

end InteractingSLE
