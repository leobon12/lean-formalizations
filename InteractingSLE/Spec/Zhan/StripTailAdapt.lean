/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripTailEscape
import InteractingSLE.Spec.Zhan.StripTimeDriver

/-!
# The strip-time drift error is adapted to the strip-time filtration

Packet PROVE-ZHAN-A4 (the whole-tail Girsanov step needs the drift `θ = e/√κ` progressive in the strip clock).
PROVE-ZHAN-A2 built the strip-time filtration `𝓗_t = 𝓖_{s(t)}` (`stripFilt`, `s(t) = chordS t` the chordal stopping
time of strip time `t`) and the strip Brownian motion `stripBM`. Here:

* the strip state at `s(t)` — the stopped coordinates `coordS` and the Brownian motion `brownG` there — is
  `𝓗_t`-measurable (`measurable_state_chordS`: it is the limit of stopped values of continuous adapted processes
  at the stopping time `s(t)`);
* the drift error `e_t` is a Borel function of that state (`errOfState`, with `W − v = √κ B + ℓ(q) − v`,
  PROVE-ZHAN-A2's `w_eq_driftLin`), so `e` is `𝓗`-adapted (`errOfState_chordS_eq`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

attribute [fun_prop] Sec4.measurable_cothHalf

namespace Zhan

open Strip

variable {nL nR : ℕ}

/-! ### The drift error as a function of the strip state -/

/-- The gap `W − v` in terms of the strip state `(q, b)`: `√κ b + ℓ(q) − v`. -/
def stateGap (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin nR → ℝ)
    (p : SCoord nL nR × ℝ) : ℝ :=
  Real.sqrt κ * p.2 + driftLin xL xR ρL ρR p.1 - p.1.1 (Fin.last nL)

/-- The drift error `e` as a function of the strip state. -/
def errOfState (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin nR → ℝ) (ρl : Fin nL → ℝ) (ρr : Fin nR → ℝ) (p : SCoord nL nR × ℝ) : ℝ :=
  (∑ i : Fin nL, ρl i / 2 * (Sec4.cothHalf (Real.log (stateGap κ xL xR ρL ρR p) -
      Real.log |p.1.1 i.castSucc - p.1.1 (Fin.last nL)|) - 1)) -
    ∑ j, ρr j / 2 * (Sec4.cothHalf (Real.log |p.1.2.1 j - p.1.1 (Fin.last nL)| -
      Real.log (stateGap κ xL xR ρL ρR p)) - 1)

theorem measurable_errOfState (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin nR → ℝ) (ρl : Fin nL → ℝ) (ρr : Fin nR → ℝ) :
    Measurable (errOfState κ xL xR ρL ρR ρl ρr) := by
  unfold errOfState stateGap driftLin
  fun_prop

/-! ### The strip state at the chordal time of a strip time -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {pL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {G : Set Ω}

/-- The strip state `(q, b)` at the chordal time `s(t)` of the strip time `t`. -/
def stateAt (pL : Fin nL → ℝ) (xR : Fin nR → ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    SCoord nL nR × ℝ :=
  (coordS (Strip.wordXL pL) xR G W VL VR (chordS G W VL t ω) ω,
    Sec2.TwoSeed.brownG G B (chordS G W VL t ω) ω)

section State

variable (hE : IsIntegratedSLEEvolution κ (Strip.wordXL pL) xR ρL ρR P 𝓕 W VL VR B ζ)
  (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
  (hgood : ∀ ω ∈ G, IsGoodStrip κ (Strip.wordXL pL) xR ρL ρR W VL VR B ζ ω)

include hE hGm hGc hgood in
/-- **The strip state at `s(t)` is `𝓗_t`-measurable.** -/
theorem measurable_stateAt (t : ℝ≥0) :
    Measurable[stripFilt hE hGm hGc hgood t] (stateAt pL xR G W VL VR B t) := by
  have hmeas : ∀ n : ℕ, Measurable[stripFilt hE hGm hGc hgood t] fun ω =>
      (coordS (Strip.wordXL pL) xR G W VL VR (min (chordS G W VL t ω) (stripLoc G W VL VR B ζ n ω)) ω,
        Sec2.TwoSeed.brownG G B (min (chordS G W VL t ω) (stripLoc G W VL VR B ζ n ω)) ω) := fun n => by
    have hprog : IsStronglyProgressive (usualAugmentation 𝓕 P) (fun s ω =>
        (coordS (Strip.wordXL pL) xR G W VL VR (min s (stripLoc G W VL VR B ζ n ω)) ω,
          Sec2.TwoSeed.brownG G B (min s (stripLoc G W VL VR B ζ n ω)) ω)) :=
      StronglyAdapted.isStronglyProgressive_of_continuous (fun s =>
        ((measurable_coordS_stopped hE hGm hGc hgood n s).prodMk
          (measurable_brownG_stopped_strip hE hGm hGc hgood n s)).stronglyMeasurable)
        (fun ω => (continuous_coordS_stopped hgood n ω).prodMk (continuous_brownG_stopped hgood n ω))
    have h := measurable_stoppedValue hprog (isStoppingTime_chordS hE hGm hGc hgood t)
    have e : stoppedValue (fun s ω =>
        (coordS (Strip.wordXL pL) xR G W VL VR (min s (stripLoc G W VL VR B ζ n ω)) ω,
          Sec2.TwoSeed.brownG G B (min s (stripLoc G W VL VR B ζ n ω)) ω))
        (fun ω => (chordS G W VL t ω : WithTop ℝ≥0)) = fun ω =>
        (coordS (Strip.wordXL pL) xR G W VL VR (min (chordS G W VL t ω) (stripLoc G W VL VR B ζ n ω)) ω,
          Sec2.TwoSeed.brownG G B (min (chordS G W VL t ω) (stripLoc G W VL VR B ζ n ω)) ω) := by
      funext ω; simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe]
    rw [e] at h
    exact h
  refine @measurable_of_tendsto_metrizable Ω (SCoord nL nR × ℝ) (stripFilt hE hGm hGc hgood t) _ _ _ _ _ _
    hmeas (tendsto_pi_nhds.2 fun ω => tendsto_const_nhds.congr' ?_)
  by_cases hω : ω ∈ G
  · have hg := hgood ω hω
    obtain ⟨n, hn⟩ := exists_le_stripLoc hgood (wordXL_last_lt pL) hω (isStripLife_chordT hg.1 hg.2.2.2 t)
    filter_upwards [eventually_ge_atTop n] with m hm
    have : chordS G W VL t ω ≤ stripLoc G W VL VR B ζ m ω := by
      simp only [chordS, hω, ↓reduceIte]
      exact hn.trans (stripLoc_mono hgood ω hm)
    simp only [stateAt, min_eq_left this]
  · refine Eventually.of_forall fun m => ?_
    simp only [stateAt, chordS, hω, ↓reduceIte, zero_le, min_eq_left]

end State

/-- **The drift error is the Borel function `errOfState` of the strip state** on the good event. -/
theorem errOfState_stateAt (hgood : ∀ ω ∈ G, IsGoodStrip κ (Strip.wordXL pL) xR ρL ρR W VL VR B ζ ω)
    {ω : Ω} (hω : ω ∈ G) (ρl : Fin nL → ℝ) (ρr : Fin nR → ℝ) (t : ℝ≥0) :
    errOfState κ (Strip.wordXL pL) xR ρL ρR ρl ρr (stateAt pL xR G W VL VR B t ω) =
      stripErr ρl ρr (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) t := by
  have hg := hgood ω hω
  have hlife := isStripLife_chordT hg.1 hg.2.2.2 t
  set s := chordT (W · ω) (VL (Fin.last nL) · ω) t with hs
  have hw := w_eq_driftLin hg.1 hlife.1
  have hgap : stateGap κ (Strip.wordXL pL) xR ρL ρR (stateAt pL xR G W VL VR B t ω) =
      W s ω - VL (Fin.last nL) s ω := by
    simp only [stateGap, stateAt, chordS, coordS, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
    rw [← hs, hw]
    simp only [stripCoordAt]
  have hcL : ∀ i : Fin nL, (stateAt pL xR G W VL VR B t ω).1.1 i.castSucc = VL i.castSucc s ω := fun i => by
    simp only [stateAt, chordS, coordS, hω, ↓reduceIte, stripCoordAt]; rfl
  have hcR : ∀ j : Fin nR, (stateAt pL xR G W VL VR B t ω).1.2.1 j = VR j s ω := fun j => by
    simp only [stateAt, chordS, coordS, hω, ↓reduceIte, stripCoordAt]; rfl
  have hcv : (stateAt pL xR G W VL VR B t ω).1.1 (Fin.last nL) = VL (Fin.last nL) s ω := by
    simp only [stateAt, chordS, coordS, hω, ↓reduceIte, stripCoordAt]; rfl
  have hgL : ∀ i : Fin nL, gapL (W · ω) (fun i t => VL i t ω) i t =
      Real.log (W s ω - VL (Fin.last nL) s ω) - Real.log |VL i.castSucc s ω - VL (Fin.last nL) s ω| :=
    fun i => by simp only [gapL, stripDriver, stripPoint, extPath, hs, chordT]; ring
  have hgR : ∀ j : Fin nR, gapR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) j t =
      Real.log |VR j s ω - VL (Fin.last nL) s ω| - Real.log (W s ω - VL (Fin.last nL) s ω) :=
    fun j => by simp only [gapR, stripDriver, stripPoint, extPath, hs, chordT]; ring
  unfold errOfState stripErr
  simp only [hgap, hcL, hcR, hcv, hgL, hgR]

end Zhan

end InteractingSLE
