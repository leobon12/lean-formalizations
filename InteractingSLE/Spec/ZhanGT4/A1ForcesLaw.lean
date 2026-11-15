/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1ForcesCap

/-!
# Zhan's A.1 (R80): the one-sample law from a capacity Brownian motion with arbitrary forces

Packet PROVE-A1-FORCES. A1-FAMILY's `isSeedSampleLaw_of_seed` derives the one-sample image law `IsSeedSampleLaw`
from A22's seeded line, whose image forces are A22's `seedCapacityForce` (own-chart marks and one frozen tip). In the
large-curve direction of A.1 the image word consists of several frozen-chart marks (PROVE-A1-MULTIMARK), whose
capacity coordinates are `capForce d S (frzImg …)`. This file separates the law content from A22's specific
construction:

* **`isSeedSampleLaw_of_capacityBrownian`**: the one-sample law for the cap `m` from **one** stochastic input, a
  capacity Brownian motion `Bh` in the capacity-time filtration `seedFilt` whose residual against the seeded capacity
  driver and the capacity coordinates `capForce d S (XL i)`, `capForce d S (XR j)` of ARBITRARY progressive own-time
  forces agrees with `Bh` up to the capacity horizon (`SeedCapacityBrownian`), plus the identifications of the image
  data with these coordinates up to the cap and the caps at own-time stopping times (as in `isSeedSampleLaw_of_seed`).

In the large-curve direction the stochastic input is exactly the multi-mark (D10)/Girsanov step that PROVE-A1-MULTIMARK
"What remains" 1 names (the seeded density of the large-curve direction, A22's t-view line).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Forces

open A1Family A1MultiMark

section Sample

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR : ℕ}
  {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {N : ℝ≥0 → Ω → ℝ} {Scap : ℕ → Ω → ℝ≥0} {m : ℕ}

/-- **The capacity coordinates of a progressive own-time force are adapted to the capacity-time filtration.** -/
theorem measurable_capForce {𝓕 : Filtration ℝ≥0 mΩ} {n : ℕ} {d : Ω → SeedData n} {S : Ω → ℝ≥0}
    (hCc : ∀ ω, Continuous (seedQuadClock (seedCapacityCoeff d S) ω))
    (hCm : ∀ ω, Monotone (seedQuadClock (seedCapacityCoeff d S) ω))
    (hmeas : ∀ r : ℝ≥0, Measurable[𝓕 r] fun ω => seedQuadClock (seedCapacityCoeff d S) ω r)
    {X : Ω → ℝ → ℝ} (hXp : IsStronglyProgressive 𝓕 fun u ω => X ω ((min u (S ω) : ℝ≥0) : ℝ) - (d ω).A 0 0)
    (u : ℝ≥0) : Measurable[seedFilt 𝓕 d S hCc hCm hmeas u] (capForce d S X u) :=
  A1Frozen.measurable_timeChangeFilt_of_progressive hCc hCm hmeas hXp u

/-- **The one-sample image law from a capacity Brownian motion with arbitrary forces.** Seeded data `d` with own
horizon `S` (an `𝓕`-stopping time) and the clock facts; own-time forces `XL`, `XR` with progressive own-time
coordinates; **a capacity Brownian motion `Bh` of `seedFilt` agreeing with the residual of the seeded capacity driver
and the capacity coordinates `capForce d S (XL i)`, `capForce d S (XR j)` up to the capacity horizon**; image data
equal to these coordinates up to the cap `Scap m`, which is the capacity horizon, before the image lifetime; the other
caps the image capacities at own-time stopping times `T k` (beyond the horizon when `S ≤ T k`). -/
theorem isSeedSampleLaw_of_capacityBrownian {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {n : ℕ}
    {d : Ω → SeedData n} {S : Ω → ℝ≥0} {A : Ω → Set ℂ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hown : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (S ω) (d ω).a (d ω).W')
    (hCc : ∀ ω, Continuous (seedQuadClock (seedCapacityCoeff d S) ω))
    (hCm : ∀ ω, Monotone (seedQuadClock (seedCapacityCoeff d S) ω))
    (hmeas : ∀ r : ℝ≥0, Measurable[𝓕 r] fun ω => seedQuadClock (seedCapacityCoeff d S) ω r)
    (hCs : ∀ ω, StrictMono (seedQuadClock (seedCapacityCoeff d S) ω)) {c : ℝ} (hc : 0 < c)
    (hClb : ∀ ω r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) ω r)
    {XL : Fin nL → Ω → ℝ → ℝ} {XR : Fin nR → Ω → ℝ → ℝ} {Bh : ℝ≥0 → Ω → ℝ}
    (hBh : SeedCapacityBrownian κ ρL ρR Q (seedFilt 𝓕 d S hCc hCm hmeas) (seedCapacityDriver d S)
      (fun i => capForce d S (XL i)) (fun j => capForce d S (XR j)) (seedCapacityHorizon d S) Bh)
    (hBhc : ∀ ω, Continuous (Bh · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hWp : IsStronglyProgressive 𝓕 fun u ω => (d ω).A 0 ((min u (S ω) : ℝ≥0) : ℝ) - (d ω).A 0 0)
    (hVLp : ∀ i, IsStronglyProgressive 𝓕 fun u ω => XL i ω ((min u (S ω) : ℝ≥0) : ℝ) - (d ω).A 0 0)
    (hVRp : ∀ j, IsStronglyProgressive 𝓕 fun u ω => XR j ω ((min u (S ω) : ℝ≥0) : ℝ) - (d ω).A 0 0)
    (hSm : ∀ ω, Scap m ω = seedCapacityHorizon d S ω)
    (hW : ∀ ω t, t ≤ Scap m ω → W t ω = seedCapacityDriver d S t ω)
    (hVL : ∀ ω i t, t ≤ Scap m ω → VL i t ω = capForce d S (XL i) t ω)
    (hVR : ∀ ω j t, t ≤ Scap m ω → VR j t ω = capForce d S (XR j) t ω)
    (hN : ∀ ω t, t ≤ Scap m ω → N t ω = seedCapacityNoise κ ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) t)
    (hζ : ∀ ω, (Scap m ω : ℝ≥0∞) ≤ ζ ω)
    (T : ℕ → Ω → ℝ≥0) (hT : ∀ k, IsStoppingTime 𝓕 fun ω => (T k ω : WithTop ℝ≥0))
    (hcap₁ : ∀ k ω, T k ω ≤ S ω → (Scap k ω : ℝ) = (d ω).a (T k ω))
    (hcap₂ : ∀ k ω, S ω ≤ T k ω → Scap m ω ≤ Scap k ω) :
    IsSeedSampleLaw Q W ζ VL VR N Scap m := by
  set 𝓗 := seedFilt 𝓕 d S hCc hCm hmeas with h𝓗
  have hagree : ∀ ω t, t ≤ Scap m ω → Bh t ω = seedCapacityNoise κ ρL ρR
      (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) t := by
    intro ω t ht
    rw [hBh.2 ω t (hSm ω ▸ ht)]
    exact (seedCapacityNoise_congr (fun u hu => hW ω u (hu.trans ht))
      (fun i u hu => hVL ω i u (hu.trans ht)) (fun j u hu => hVR ω j u (hu.trans ht))).symm
  have hE : ∀ s : ℝ≥0, MeasurableSet[𝓗 s] {ω | s < Scap m ω} := fun s => by
    simp only [hSm]
    exact measurableSet_lt_seedCapacityHorizon hown hCc hCm hmeas hCs hc hClb hS s
  refine ⟨𝓗, Bh, hBh.1, hBhc, hE, fun s => ?_, ae_of_all _ fun ω t ht => by rw [hagree ω t ht, hN ω t ht]⟩
  have hlt : ∀ {r : ℝ≥0}, r ≤ s → ∀ ω ∈ {ω | s < Scap m ω}, r ≤ Scap m ω :=
    fun hr ω hω => hr.trans (le_of_lt hω)
  refine A1Frozen.forall_imageGen (p := fun g => MeasurableSet[𝓗 s] (g ∩ {ω | s < Scap m ω}))
    (fun r hr U hU => ?_) (fun r hr U hU i => ?_) (fun r hr U hU j => ?_)
    (fun r hr U hU => ?_) (fun r hr k => ?_) (fun r hr => ?_)
  · refine measurableSet_preimage_inter_of_eqOn (𝓜 := {E | MeasurableSet[𝓗 s] E})
      (g := seedCapacityDriver d S r) (fun ω hω => hW ω r (hlt hr ω hω)) ?_
    exact (𝓗.mono hr _ (measurable_seedCapacityDriver hCc hCm hmeas hWp r hU)).inter (hE s)
  · refine measurableSet_preimage_inter_of_eqOn (𝓜 := {E | MeasurableSet[𝓗 s] E})
      (g := capForce d S (XL i) r) (fun ω hω => hVL ω i r (hlt hr ω hω)) ?_
    exact (𝓗.mono hr _ (measurable_capForce hCc hCm hmeas (hVLp i) r hU)).inter (hE s)
  · refine measurableSet_preimage_inter_of_eqOn (𝓜 := {E | MeasurableSet[𝓗 s] E})
      (g := capForce d S (XR j) r) (fun ω hω => hVR ω j r (hlt hr ω hω)) ?_
    exact (𝓗.mono hr _ (measurable_capForce hCc hCm hmeas (hVRp j) r hU)).inter (hE s)
  · refine measurableSet_preimage_inter_of_eqOn (𝓜 := {E | MeasurableSet[𝓗 s] E})
      (g := Bh r) (fun ω hω => by rw [hN ω r (hlt hr ω hω), hagree ω r (hlt hr ω hω)]) ?_
    exact (𝓗.mono hr _ (hBh.1.2.1 r hU)).inter (hE s)
  · have h := measurableSet_cap_le_inter hown hCc hCm hmeas hCs hc hClb hS (hT k) (cap := Scap k)
      (hcap₁ k) (fun ω hω => (hSm ω) ▸ hcap₂ k ω hω) hr
    simp only [← hSm] at h
    exact h
  · have e : {ω | (r : ℝ≥0∞) < ζ ω} ∩ {ω | s < Scap m ω} = {ω | s < Scap m ω} := by
      refine inter_eq_right.2 fun ω hω => ?_
      exact lt_of_lt_of_le (by exact_mod_cast hr.trans_lt hω) (hζ ω)
    rw [e]
    exact hE s

end Sample

end InteractingSLE.ZhanGT4.A1Forces
