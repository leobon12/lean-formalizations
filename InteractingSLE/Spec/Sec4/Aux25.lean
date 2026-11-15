/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Aux25Path
import InteractingSLE.Spec.Sec4.Special3Contact
import InteractingSLE.Spec.Sec4.RepulsionNoncollision

/-!
# Aux. lemma 25: almost-sure injectivity before the lifetime

Packet PROVE-AUX25. Specification, Aux. lemma 25 (`source/spec/p097-144.md`, p. 125): "Let `0 < κ < 4`. An
integrated finite-force `SLE_κ(ρ)` trace which is continuous on an available stopped interval is injective
there, up to and including a continuous finite terminal endpoint."

This file assembles the pathwise argument (`Aux25Path.lean`) on one almost-sure event:

* the path conditions of Definition 2.1;
* the localization of Aux. lemma 24 (`IsIntegratedSLEEvolution.ae_exists_localization`, PROVE-SEC4-B3);
* the exclusion of the endpoint case for the evolution and for its reflection
  (`EndpointExclusionStatement`, below).

## Named input

* `EndpointExclusionStatement`: the probabilistic content of the source's endpoint step ("That event has
  probability zero by the independent one-force first-swallow law (B1) in Aux. lemma 99", p. 127), in the
  pathwise form `Aux25.NoRightEndpoint` at every rational restart time: almost surely the trace does not hit
  a force group's own position at the group's first collision after a restart time, when the other force
  gaps stay bounded below. Its proof (the restart, Girsanov removal of the other marks, and the scale function
  `u ↦ ∫ v^{−2(2+ρ)/κ}(1 − v)^{2(4+ρ−κ)/κ}` of the ratio of the force gap to a passive gap) is the
  remaining step; see the handoff.

## Main results

* `IsIntegratedSLEEvolution.ae_injOn_lt_of_endpointExclusion`: almost surely every continuous generating
  trace on `[0, ζ]` is injective on `{t | t < ζ}`;
* `IsIntegratedSLEEvolution.ae_injOn_of_endpointExclusion_of_lifetime_eq_top`: Aux. lemma 25 on the event
  `ζ = ∞` (there the available interval has no terminal endpoint).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Aux25

/-- **Named input: exclusion of the endpoint case** (Specification, proof of Aux. lemma 25, p. 127: "The
event under consideration is therefore a first-swallow endpoint *at that force point* in the reference
chart. That event has probability zero by the independent one-force first-swallow law (B1) in Aux. lemma
99. In fact, `ρ_* > −2 > κ/2 − 4` implies that the first endpoint is strictly beyond the marked point if a
finite swallow occurs"). For every integrated `SLE_κ(ρ)` evolution with `0 < κ < 4`, almost surely no
rational restart time has the endpoint case (`NoRightEndpoint`). The left-side statement is this one for the
reflected evolution. -/
def EndpointExclusionStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ),
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
      ∀ᵐ ω ∂P, NoRightEndpoint (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω)

end Aux25

namespace IsIntegratedSLEEvolution

open Aux25

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Aux. lemma 25 before the lifetime**, from the endpoint exclusion: almost surely every continuous
generating trace on the available interval is injective on `{t | t < ζ}`. -/
theorem ae_injOn_lt_of_endpointExclusion (hEnd : EndpointExclusionStatement.{u})
    [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
      InjOn η {t | (t : ℝ≥0∞) < ζ ω} := by
  have hR := hEnd κ hκ hκ4 xL xR ρL ρR P 𝓕 W VL VR B ζ hE
  have hL := hEnd κ hκ hκ4 (-xR) (-xL) ρR ρL P 𝓕 (-W) (fun i => -VR i) (fun i => -VL i) (-B) ζ
    hE.reflect
  have hloc := hE.ae_exists_localization hκ hκ4.le
  filter_upwards [hE.2.2.2.2, hloc, hR, hL] with ω hp hlocω hRω hLω η hη
  exact injOn_lt_of_noEndpoint hp hη hlocω hRω hLω

/-- **Aux. lemma 25 when the available lifetime is unbounded** ("It applies to each finite compact portion
when the available lifetime is unbounded"), from the endpoint exclusion: almost surely, on `ζ = ∞`, every
continuous generating trace is injective on `{t | t ≤ ζ}`. -/
theorem ae_injOn_of_endpointExclusion_of_lifetime_eq_top (hEnd : EndpointExclusionStatement.{u})
    [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ → ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
      InjOn η {t | (t : ℝ≥0∞) ≤ ζ ω} := by
  filter_upwards [hE.ae_injOn_lt_of_endpointExclusion hEnd hκ hκ4] with ω hω hζ η hη
  have heq : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ ω} = {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := by
    ext t
    simp [hζ]
  rw [heq]
  exact hω η hη

end IsIntegratedSLEEvolution

end InteractingSLE
