/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessLink
import InteractingSLE.Spec.Sec2.AddMarksGirsanov

/-!
# `b̃` is a Brownian motion: the statement

Packet PROVE-SEC7-C9 (Specification §7.3, (C1)–(C2), pp. 378–379; supplement Lemma LP9, p. 485; Astra §3,
"Time change and Lévy's characterization identify the new martingale with `√κ` times Brownian motion in the
time-changed filtration").

For an integrated `SLE_κ(ρ)` evolution of a distinct-position word whose right list has length `j + 1 + m`
(`j ≥ 1`), retarget at the right mark of Lean index `j` (`LP.retargetIdx j m`, position `x_j > 0`). Up to the
**separation time** `τ_sep` (`sepTime`: the first time before `ζ` at which the new target meets the driver, `ζ` if
there is none) the target stays strictly right of the driver, and the deterministic part (PROVE-SEC7-C8,
`isSLEPathUpTo_retarget`) maps every path to a local integrated path of LP9's transformed word before the new
horizon `T̃ = sup_{S < τ_sep} C(S)` in the new clock, with Brownian path `b̃ = newB`.

`RetargetEvolutionStatement` is the stochastic half: the transformed process is a **local integrated
`SLE_κ(ρ̃)` evolution** (`Sec2.IsSLEEvolutionUpTo`) before `T̃` on the product space `Ω × Ω` (the second factor
carries an independent Brownian motion that continues the noise after `T̃`, which is needed when `T̃ < ∞`), driven
by a Brownian motion `β` with every path continuous (the horizon is `T̃` almost surely). Since the paths satisfy
(N1) of the transformed word, `β = b̃` before `T̃` almost surely.

The statement is fixed here so that consumers can use it before its proof lands; the proof is
`retargetEvolutionStatement` (`TargetChangeProcessBrownian.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Zhan

namespace Retarget

/-- **The separation time**: the first time before `ζ` at which the new target `v_k` meets the driver `w`
(`v_k ≤ w`), and `ζ` if there is none. -/
def sepTime (w vk : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : ℝ≥0∞ :=
  min ζ (⨅ (s : ℝ≥0) (_ : (s : ℝ≥0∞) < ζ ∧ vk s ≤ w s), (s : ℝ≥0∞))

theorem sepTime_le (w vk : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : sepTime w vk ζ ≤ ζ := min_le_left _ _

/-- Before the separation time the target is strictly right of the driver. -/
theorem lt_of_lt_sepTime {w vk : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {t : ℝ≥0} (ht : (t : ℝ≥0∞) < sepTime w vk ζ) :
    w t < vk t := by
  by_contra h
  have hζ : (t : ℝ≥0∞) < ζ := ht.trans_le (sepTime_le w vk ζ)
  have : sepTime w vk ζ ≤ t := (min_le_right _ _).trans (iInf₂_le t ⟨hζ, not_lt.1 h⟩)
  exact absurd ht (not_lt.2 this)

/-- **Named statement: the transformed process is a local evolution of the transformed word, driven by a
Brownian motion** (`b̃` is a Brownian motion; Specification pp. 378–379, supplement p. 485). For `κ > 0`, a
distinct-position word with right list of length `j + 1 + m`, `j ≥ 1`, and an integrated evolution on
`(Ω, P, 𝓕)`, there are a filtration `𝓘` on `Ω × Ω`, a process `β` on `Ω × Ω` with every path continuous, and a
horizon `τ` equal almost surely to the new horizon of the separation time, such that under `P ⊗ P` the images
`(newW, newVL, newVR)` of the evolution (read through the first factor), driven by `β`, form a local integrated
`SLE_κ(ρ̃)` evolution of LP9's transformed word before `τ`. (The horizon is only fixed almost surely: off a null set
the original paths are arbitrary, and adaptedness before the literal new horizon could fail there.) -/
def RetargetEvolutionStatement : Prop :=
  ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
    {κ : ℝ} {nL j m : ℕ} (xL : Fin nL → ℝ) (xR : Fin (j + 1 + m) → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin (j + 1 + m) → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
    0 < κ → LP.IsDistinctForceWord xL xR → 1 ≤ j →
    IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
    ∃ (𝓘 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω))) (β : ℝ≥0 → Ω × Ω → ℝ)
      (τ : Ω → ℝ≥0∞),
      (∀ p, Continuous fun u => β u p) ∧
      (∀ᵐ ω ∂P, τ ω = newHorizon (LP.retargetPos xR) (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω)
        (sepTime (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω) (ζ ω))) ∧
      Sec2.IsSLEEvolutionUpTo κ (LP.retargetXL xL xR) (LP.retargetXR xR) (LP.retargetρL κ ρL ρR)
        (LP.retargetρR ρR) (P.prod P) 𝓘
        (fun u p => newW xR (fun t => W t p.1) (fun i t => VR i t p.1) u)
        (fun i u p => newVL xR (fun t => W t p.1) (fun i t => VL i t p.1) (fun i t => VR i t p.1) i u)
        (fun i u p => newVR xR (fun t => W t p.1) (fun i t => VR i t p.1) i u) β (fun p => τ p.1)

end Retarget

end Zhan

end InteractingSLE
