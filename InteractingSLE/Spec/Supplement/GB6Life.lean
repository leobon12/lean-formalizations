/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6TraceKernel

/-!
# Proposition GB6, step (e): the relative lifetime is infinite

Packet PROVE-GB6D. GB6's proof (p. 520): "There remains a possible extra killing at first contact … Let `ζ` be the
limiting relative capacity as the original time tends to `T` … If `ζ < ∞`, … Its continuous trace has a finite limit at
`ζ`. The continuously extended inverse of the fixed `U` chart therefore identifies the physical endpoint of the original
trace with the inverse image of this finite reference point. If `T < ∞`, that endpoint belongs to the retained flow
prefix by definition. If `T = ∞`, original transience makes the endpoint `x`, which is also on that prefix. Every finite
incident image of either endpoint lies on one of the protected flow-side tails or their protected initial junctions.
GB5 excludes the required finite reference contact. … Hence `ζ = ∞`."

The argument has a deterministic half and a probabilistic half:

* **`GB6EndpointStatement`** (deterministic, one realization; proved: `gb6EndpointStatement` in
  `GB6LawFinal.lean`): if a continuous driver `V` with complete continuous
  generating trace `Γ` generates the chart images `Ψ(K'_t)` of the counterflow hulls in the relative clock before the
  first contact `T_c`, and the relative clock is **bounded** before `T_c`, then `Γ` visits a closed protected tail
  `[junctionR, ∞)` or `(−∞, junctionL]` (at the relative time `ζ = sup relClock`);
* the probabilistic half — under the conditional law the canonical trace never visits the closed tails (GB5 at the
  junctions) — is `gb6_kernel` (`GB6TraceLaw.lean`).

`relClock_unbounded_of_endpoint` combines them pathwise: a chart path avoiding the closed tails at every time forces
an unbounded relative clock before `T_c`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE

namespace Supp8

namespace GB6

/-- **GB6, step (e), deterministic half** (one realization; the endpoint argument "Every finite incident image of either
endpoint lies on one of the protected flow-side tails or their protected initial junctions"). In the original flow
chart, let `α` be the generating trace of the flow driver `wα` with an interior tip `α(s) ∈ ℍ` before its lifetime, `γ`
a complete continuous transient generating trace of the counterflow driver `w` (physical counterflow `η = R̂ ∘ γ`), and
`V` a continuous driver with complete continuous transient generating trace `Γ` that generates the chart images of the
counterflow
hulls in the relative clock at every time before the first contact `T_c`. If the relative clock is bounded before
`T_c`, then `Γ` visits a closed protected tail: `Γ(u) ∈ ℝ` with `Γ(u) ≥ junctionR` or `Γ(u) ≤ junctionL`. -/
def GB6EndpointStatement : Prop :=
  ∀ (wα w V : ℝ≥0 → ℝ) (Tα : ℝ≥0∞) (α γ Γ : ℝ≥0 → ℂ) (s : ℝ≥0),
    IsGeneratingTrace wα Tα α → ContinuousOn wα {t | (t : ℝ≥0∞) < Tα} → wα 0 = 0 → (s : ℝ≥0∞) < Tα →
    α s ∈ H → IsGeneratingTrace w ⊤ γ → Continuous w → w 0 = 0 → Tendsto (fun t => ‖γ t‖) atTop atTop →
    IsGeneratingTrace V ⊤ Γ → Continuous V → V 0 = 0 → Tendsto (fun t => ‖Γ t‖) atTop atTop →
    (∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) →
      QuantumZipper.fwdHull (fun r : ℝ => V r.toNNReal)
          (relClock (fun r : ℝ => wα r.toNNReal) s (fun r : ℝ => w r.toNNReal) t) =
        relMap (fun r : ℝ => wα r.toNNReal) s '' QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) t) →
    (∃ M : ℝ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) →
      relClock (fun r : ℝ => wα r.toNNReal) s (fun r : ℝ => w r.toNNReal) t ≤ M) →
    ∃ u : ℝ≥0, (Γ u).im = 0 ∧
      (junctionR (fun r : ℝ => wα r.toNNReal) s ≤ (Γ u).re ∨ (Γ u).re ≤ junctionL (fun r : ℝ => wα r.toNNReal) s)

/-- **GB6, step (e), pathwise** (conditional on the deterministic half): a chart path that avoids the closed tails at
every time forces the relative clock to be unbounded before the first contact. -/
theorem relClock_unbounded_of_endpoint (hEnd : GB6EndpointStatement) {wα w V : ℝ≥0 → ℝ} {Tα : ℝ≥0∞}
    {α γ Γ : ℝ≥0 → ℂ} {s : ℝ≥0} (hα : IsGeneratingTrace wα Tα α) (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα})
    (hwα0 : wα 0 = 0) (hs : (s : ℝ≥0∞) < Tα) (hsH : α s ∈ H) (hγ : IsGeneratingTrace w ⊤ γ) (hw : Continuous w)
    (hw0 : w 0 = 0) (htr : Tendsto (fun t => ‖γ t‖) atTop atTop) (hΓ : IsGeneratingTrace V ⊤ Γ) (hV : Continuous V)
    (hV0 : V 0 = 0) (hΓtr : Tendsto (fun t => ‖Γ t‖) atTop atTop)
    (hK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) →
      QuantumZipper.fwdHull (fun r : ℝ => V r.toNNReal)
          (relClock (fun r : ℝ => wα r.toNNReal) s (fun r : ℝ => w r.toNNReal) t) =
        relMap (fun r : ℝ => wα r.toNNReal) s '' QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) t)
    (havoid : ∀ u, 0 < tailGap (junctionL (fun r : ℝ => wα r.toNNReal) s) (junctionR (fun r : ℝ => wα r.toNNReal) s)
      (Γ u)) :
    ∀ u : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) ∧
      u ≤ relClock (fun r : ℝ => wα r.toNNReal) s (fun r : ℝ => w r.toNNReal) t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨u₀, hu₀⟩ := hcon
  obtain ⟨u, hu, hre⟩ := hEnd wα w V Tα α γ Γ s hα hwα hwα0 hs hsH hγ hw hw0 htr hΓ hV hV0 hΓtr hK
    ⟨u₀, fun t ht => (hu₀ t ht).le⟩
  exact (tailGap_pos_iff.1 (havoid u)) ⟨hu, hre⟩

end GB6

end Supp8

end InteractingSLE
