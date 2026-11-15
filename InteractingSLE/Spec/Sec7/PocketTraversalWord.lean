/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketTraversalCoords
import InteractingSLE.Spec.Sec7.PocketTraversalMeas

/-!
# Lemma 7.25's pocket-word evolution from a random driven relative curve

Packet PROVE-STRIPSYS10 (specification §7.4.1, proof of Lemma 7.25, p. 414; Aux. lemmas 121–122 and 125).

This file assembles `PocketTraversal.lean`, `PocketTraversalMeas.lean` and `PocketTraversalCoords.lean`: if the
relative traversal is a random driven curve `γ ω` (`IsDrivenCurve`, e.g. the erased traversal of a reverse-contained
pocket in its Jordan coordinate, `isDrivenCurve_relCurve_of_isReversePocket`) with infinite terminal capacity time
(Aux. lemma 125: "Thus `ζ = ∞`") and filled prefixes adapted to the filtration at capacity times, then its canonical
driver `segDriver (γ ω)` is a continuous adapted relative driver from `0` with a generating trace on every finite
interval, and together with the geometric images of random ordered marks it gives `Lemma725Ref.PocketWordEvolution`
from the common phase and the two martingale inputs (R.5 with Aux. lemmas 27–29) alone.

## Main results

* `stronglyAdapted_segDriver_of_capLife_eq_top`;
* **`pocketWordEvolution_of_drivenCurve`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

universe v

namespace InteractingSLE.Sec7.PocketTraversal

open Lemma71C

/-- **The canonical driver of a random driven curve with infinite terminal capacity time is adapted** to every
filtration in which its filled prefixes are adapted at capacity times. -/
theorem stronglyAdapted_segDriver_of_capLife_eq_top {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hL : ∀ ω, capLife (γ ω) = ⊤) (hpre : IsPrefixAdapted 𝓖 γ) :
    StronglyAdapted 𝓖 (fun t ω => segDriver (γ ω) t) := by
  intro t
  have hA := adaptedBefore_segDriver_of_isDrivenCurve hγ hpre
  refine Measurable.stronglyMeasurable fun A hA' => ?_
  have heq : (fun ω => segDriver (γ ω) t) ⁻¹' A =
      {ω | (t : ℝ≥0∞) < capLife (γ ω) ∧ segDriver (γ ω) t ∈ A} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, hL ω, ENNReal.coe_lt_top, true_and]
  rw [heq]
  exact hA t A hA'

open PocketWord MartChar PhaseSel in
/-- **Lemma 7.25's pocket-word evolution from a random driven relative curve** (see the module docstring). On a
standard Borel probability space with a right-continuous filtration `𝓕`: a random curve `γ ω`, driven for every `ω`,
with infinite terminal capacity time and filled prefixes adapted to `𝓕` at capacity times; random `𝓕₀`-measurable
marks with the seeds at `0`, the other left marks negative and the other right marks positive, ordered in the index;
a common phase `d_t ∈ 2πχℤ`; and the two martingale inputs `hmart`, `hcont` for the canonical driver
`W t ω = segDriver (γ ω) t` and the geometric coordinates of the marks. -/
theorem pocketWordEvolution_of_drivenCurve {κ rL rR : ℝ} (hκ : 4 < κ) (hL : -2 < rL) (hLd : rL < κ / 2 - 4)
    (hR : -2 < rR) (hRd : rR < κ / 2 - 4) {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    (hρL : ρL 0 = rL) (hρR : ρR 0 = rR) {Ω : Type v} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous]
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hγL : ∀ ω, capLife (γ ω) = ⊤)
    (hpre : IsPrefixAdapted 𝓕 γ) {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxLm : Measurable[𝓕 0] xL) (hxRm : Measurable[𝓕 0] xR)
    (hseedL : ∀ ω, xL ω 0 = 0) (hseedR : ∀ ω, xR ω 0 = 0)
    (hxLd : ∀ ω (i : Fin nL), xL ω i.succ < 0) (hxRd : ∀ ω (j : Fin nR), 0 < xR ω j.succ)
    (hxLi : ∀ ω, Antitone (xL ω)) (hxRi : ∀ ω, Monotone (xR ω))
    {d : ℝ≥0 → Ω → ℝ} (hd : ∀ (t : ℝ≥0) ω, 0 < t → ∃ n : ℤ, d t ω = n * phaseStep κ)
    (hmart : ∀ U : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω t, IsBoundedHarmonicExtension
        (phaseData κ ρL ρR (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i t ω - segDriver (γ ω) t)
          (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j t ω - segDriver (γ ω) t) (d t ω))
        (forceJumpSet (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i t ω - segDriver (γ ω) t)
          (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j t ω - segDriver (γ ω) t)) (U ω t)) →
      ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
        (fun ω => (QuantumZipper.swallowTime (wpath (fun t ω => segDriver (γ ω) t) ω) z : WithTop ℝ≥0))
        (fun t ω => couplingMean κ (wpath (fun t ω => segDriver (γ ω) t) ω) t (U ω t) z))
    (hcont : ∀ U : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω t, IsBoundedHarmonicExtension
        (phaseData κ ρL ρR (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i t ω - segDriver (γ ω) t)
          (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j t ω - segDriver (γ ω) t) (d t ω))
        (forceJumpSet (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i t ω - segDriver (γ ω) t)
          (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j t ω - segDriver (γ ω) t)) (U ω t)) →
      ∀ ω (z : ℂ) (T' : ℝ), 0 ≤ T' →
        z ∈ H \ QuantumZipper.fwdHull (wpath (fun t ω => segDriver (γ ω) t) ω) T' →
        ContinuousOn (fun t : ℝ => couplingMean κ (wpath (fun t ω => segDriver (γ ω) t) ω) t
          (U ω t.toNNReal) z) (Icc 0 T')) :
    Lemma725Ref.PocketWordEvolution.{v} κ rL rR :=
  pocketWordEvolution_of_geom hκ hL hLd hR hRd hρL hρR (fun ω => (hγ ω).segDriver_spec.1)
    (fun ω => (hγ ω).continuous_segDriver_of_capLife_eq_top (hγL ω))
    (stronglyAdapted_segDriver_of_capLife_eq_top hγ hγL hpre) hxLm hxRm hseedL hseedR hxLd hxRd hxLi hxRi hd
    hmart hcont fun ω T => ⟨capTrace (γ ω), (hγ ω).isGeneratingTrace_of_capLife_eq_top (hγL ω) T⟩

end InteractingSLE.Sec7.PocketTraversal
