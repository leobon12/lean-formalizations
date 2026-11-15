/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkNoise10Identify

/-!
# The local first-mark noise and its observable identities

Reuse the existing centered observable `bv0`, whose exceptional samples are
zero, and identify it with canonical transformed noise before the image horizon.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Noise10

open Zhan.Retarget

/-- The existing centered first-mark observable, divided by the Brownian scale. -/
def localNoise {Ω : Type*} (κ a b : ℝ) (xL ρL : Fin 0 → ℝ) (ρR : Fin 2 → ℝ)
    (G : Set Ω) (W B : ℝ≥0 → Ω → ℝ) (VL : Fin 0 → ℝ≥0 → Ω → ℝ)
    (VR : Fin 2 → ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  bv0 (j := 0) (m := 1) κ xL ![a, b] ρL ρR G W VL VR B

variable {Ω : Type*} {κ a b : ℝ} {xL ρL : Fin 0 → ℝ} {ρR : Fin 2 → ℝ}
  {W B : ℝ≥0 → Ω → ℝ} {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 2 → ℝ≥0 → Ω → ℝ}
  {e : Ω → ℝ≥0∞} {S : ℕ → Ω → ℝ≥0} {G : Set Ω} {ω : Ω}

/-- The masked noise is zero outside its good event. -/
theorem localNoise_of_not_mem (hω : ω ∉ G) (u : ℝ≥0) :
    localNoise κ a b xL ρL ρR G W B VL VR u ω = 0 := bv0_of_not_mem hω u

/-- Every path of the masked local noise starts at zero. -/
theorem localNoise_zero (hgood : ∀ ω ∈ G, Mart9.IsGood κ a b xL ρL ρR W B VL VR e S ω) (ω : Ω) :
    localNoise κ a b xL ρL ρR G W B VL VR 0 ω = 0 := by
  by_cases hω : ω ∈ G
  · have hg := hgood ω hω
    have h0 : rCoordAt (LP.retargetPos (j := 0) (m := 1) ![a, b]) (LP.retargetIdx 0 1) (W · ω)
        (fun i t => VL i t ω) (fun i t => VR i t ω) 0 =
        (xL, ![a, b], LP.retargetPos (j := 0) (m := 1) ![a, b], -1, 0) :=
      rCoordAt_zero hg.path.vL_zero hg.path.vR_zero
    simp only [localNoise, bv0, NNReal.coe_zero, invClk_zero_eq, Real.toNNReal_zero,
      rCoord, Sec2.TwoSeed.brownG, hω, ↓reduceIte, h0,
      hg.zeroB, rInit, sub_self, zero_div]
  · exact localNoise_of_not_mem hω 0

/-- The observable at the capped inverse equals the scaled centered noise plus its initial value. -/
theorem obs_cappedPoint (hκ : 0 < κ) (ha : 0 < a) (hab : a < b)
    (hgood : ∀ ω ∈ G, Mart9.IsGood κ a b xL ρL ρR W B VL VR e S ω)
    (n : ℕ) (u : ℝ≥0) (ω : Ω) :
    obs κ xL ![a, b] ρL ρR 0 (cappedPoint xL a b G S W B VL VR e n u ω) =
      Real.sqrt κ * localNoise κ a b xL ρL ρR G W B VL VR
        (min u (imageStops a G S W B VL VR e n ω)) ω + obs κ xL ![a, b] ρL ρR 0 (rInit xL ![a, b] a) := by
  by_cases hω : ω ∈ G
  · rw [cappedPoint_eq ha hab (hgood ω hω) hω]
    simp only [localNoise, bv0, rCoord, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
    rw [mul_div_cancel₀ _ (Real.sqrt_ne_zero'.2 hκ)]
    exact sub_add_cancel _ _ |>.symm
  · rw [localNoise_of_not_mem hω]
    simp only [cappedPoint, Adapt8.stoppedCoords, rCoord, hω, ↓reduceIte,
      mul_zero, zero_add, rInit]

/-- The clock coordinate of the capped tuple is the stopped image time on every sample. -/
theorem clock_cappedPoint_all (ha : 0 < a) (hab : a < b)
    (hgood : ∀ ω ∈ G, Mart9.IsGood κ a b xL ρL ρR W B VL VR e S ω)
    (n : ℕ) (u : ℝ≥0) (ω : Ω) :
    (cappedPoint xL a b G S W B VL VR e n u ω).1.2.2.2.2 =
      (min u (imageStops a G S W B VL VR e n ω) : ℝ≥0) := by
  by_cases hω : ω ∈ G
  · exact clock_cappedPoint ha hab (hgood ω hω) hω n u
  · simp only [cappedPoint, Adapt8.stoppedCoords, rCoord, hω, ↓reduceIte,
      imageStops, Clock7.imageStop, min_zero, NNReal.coe_zero]

/-- The stopped masked noise is the centered optional-time observable. -/
theorem localNoise_min_eq (hκ : 0 < κ) (ha : 0 < a) (hab : a < b)
    (hgood : ∀ ω ∈ G, Mart9.IsGood κ a b xL ρL ρR W B VL VR e S ω)
    (n : ℕ) (u : ℝ≥0) (ω : Ω) :
    localNoise κ a b xL ρL ρR G W B VL VR (min u (imageStops a G S W B VL VR e n ω)) ω =
      (obs κ xL ![a, b] ρL ρR 0 (cappedPoint xL a b G S W B VL VR e n u ω) -
        obs κ xL ![a, b] ρL ρR 0 (rInit xL ![a, b] a)) / Real.sqrt κ := by
  apply (eq_div_iff (Real.sqrt_ne_zero'.2 hκ)).2
  rw [obs_cappedPoint hκ ha hab hgood, add_sub_cancel_right, mul_comm]

/-- Before the image horizon the masked observable is exactly the canonical transformed noise. -/
theorem localNoise_eq_newB (hκ : 0 < κ) (ha : 0 < a) (hab : a < b)
    (hgood : ∀ ω ∈ G, Mart9.IsGood κ a b xL ρL ρR W B VL VR e S ω)
    {ω : Ω} (hω : ω ∈ G) {u : ℝ≥0}
    (hu : (u : ℝ≥0∞) < newHorizon a (W · ω) (VR 0 · ω)
      (sepTime (W · ω) (VR 0 · ω) (e ω))) :
    localNoise κ a b xL ρL ρR G W B VL VR u ω =
      newB (j := 0) (m := 1) κ xL ![a, b] ρL ρR (W · ω)
        (fun i t => VL i t ω) (fun i t => VR i t ω) u := by
  have hg := hgood ω hω
  exact bv0_eq_newB_of_local (hg.path.mono (sepTime_le _ _ _)) (hg.data ha hab)
    (LP.isDistinctForceWord_of_two xL ![a, b] ha.le hab) hg.zeroB hκ hω hu

end InteractingSLE.Sec5.TwoMark.Noise10
