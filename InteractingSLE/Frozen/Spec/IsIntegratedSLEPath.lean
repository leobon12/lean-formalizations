import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import QuantumZipper.Loewner.Forward
import QuantumZipper.GFF.Kernels
import LQGMetric.Field.ZeroBoundary

import InteractingSLE.Frozen.Spec.ForceWord_ThresholdCondition

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The deterministic (pathwise) part of an integrated `SLE_a(ρ)` driving evolution with
lifetime `ζ`, for the force word with positions `(xL; xR)` and weights `(ρL; ρR)` (Specification p. 3,
(1.10)–(1.11) and the paragraph after them; Definition 2.1, pp. 20; Aux. lemma 3, p. 24 for the reading of the
threshold as a maximal lifetime). Paths are indexed by `ℝ≥0`; time integrals are interval integrals over `ℝ` of
`s ↦ f s.toNNReal`. The conjuncts, in order:

* `w 0 = 0`, `vL i 0 = x_{i,L}`, `vR i 0 = x_{i,R}`;
* `w`, `vL i`, `vR i` are continuous on `[0, ζ)`;
* for `t < ζ`: the side ordering, absolute integrability of every reciprocal gap on `[0, t]`, and
  the integrated equations (1.10)–(1.11) (the value of `x⁻¹` at `0` is Lean's `0`; the source
  allows any value on the Lebesgue-null collision sets);
* every collision set `{s < ζ : w s = v^{i,q} s}` is Lebesgue-null;
* the threshold condition fails at every `t < ζ` (`ζ ≤ T_*`);
* maximality (`ζ = T_*`): if `ζ = 0` the seed `(0, x)` satisfies the threshold condition, and if
  `0 < ζ < ∞` every continuous limit of the state at `ζ⁻` satisfies it. -/
def IsIntegratedSLEPath (a : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (b : ℝ≥0 → ℝ)
    (ζ : ℝ≥0∞) : Prop :=
  -- w_zero
  w 0 = 0 ∧
  -- vL_zero
  (∀ i, vL i 0 = xL i) ∧
  -- vR_zero
  (∀ i, vR i 0 = xR i) ∧
  -- continuousOn_w
  ContinuousOn w {t | (t : ℝ≥0∞) < ζ} ∧
  -- continuousOn_vL
  (∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ}) ∧
  -- continuousOn_vR
  (∀ i, ContinuousOn (vR i) {t | (t : ℝ≥0∞) < ζ}) ∧
  -- antitone_vL
  (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → Antitone fun i => vL i t) ∧
  -- vL_le_w
  (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ i, vL i t ≤ w t) ∧
  -- w_le_vR
  (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ i, w t ≤ vR i t) ∧
  -- monotone_vR
  (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → Monotone fun i => vR i t) ∧
  -- integrable_gapL
  (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ i,
    IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vL i s.toNNReal)⁻¹) volume 0 t) ∧
  -- integrable_gapR
  (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ i,
    IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vR i s.toNNReal)⁻¹) volume 0 t) ∧
  -- w_eq
  (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
    w t = Real.sqrt a * b t
      + (∑ i, ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal))
      + (∑ i, ∫ s in (0 : ℝ)..t, ρR i / (w s.toNNReal - vR i s.toNNReal))) ∧
  -- vL_eq
  (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ i,
    vL i t = xL i + ∫ s in (0 : ℝ)..t, 2 / (vL i s.toNNReal - w s.toNNReal)) ∧
  -- vR_eq
  (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ i,
    vR i t = xR i + ∫ s in (0 : ℝ)..t, 2 / (vR i s.toNNReal - w s.toNNReal)) ∧
  -- volume_collisionL
  (∀ i,
    volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w s.toNNReal = vL i s.toNNReal} = 0) ∧
  -- volume_collisionR
  (∀ i,
    volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w s.toNNReal = vR i s.toNNReal} = 0) ∧
  -- not_threshold
  (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
    ¬ ForceWord.ThresholdCondition ρL ρR (w t) (fun i => vL i t) (fun i => vR i t)) ∧
  -- threshold_of_eq_zero
  (ζ = 0 → ForceWord.ThresholdCondition ρL ρR 0 xL xR) ∧
  -- threshold_of_tendsto
  ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ →
    ∀ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T)
        (𝓝 (w₀, vL₀, vR₀)) →
      ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀

end InteractingSLE
