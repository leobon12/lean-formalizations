/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkAdapt8Stopped

/-!
# Local retargeting coordinates at finite source stops

The coordinates and Brownian path, stopped before separation and masked on a
time-zero event, form a continuous adapted process. Optional evaluation at the
minimum of this source stop and an arbitrary stopping time is measurable.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Adapt8

open Zhan.Retarget

/-- The existing retargeting coordinates and Brownian path, stopped at a finite time. -/
def stoppedCoords {Ω : Type*} {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (a : ℝ) (k : Fin nR) (G : Set Ω) (W B : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (σ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) : RCoord nL nR × ℝ :=
  (rCoord xL xR a k G W VL VR (min t (σ ω)) ω,
    if ω ∈ G then B (min t (σ ω)) ω else 0)

/-- A local stopped coordinate process is adapted and continuous on every sample. -/
theorem stopped_coords_regular {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ a : ℝ} {nL nR : ℕ}
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ} {k : Fin nR}
    {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {e U : Ω → ℝ≥0∞} {G : Set Ω} {σ : Ω → ℝ≥0}
    (ha : 0 < a) (hE : Sec2.IsSLEEvolutionUpTo κ xL xR ρL ρR P 𝓕 W VL VR B e)
    (hG : MeasurableSet[𝓕 0] G)
    (hp : ∀ ω ∈ G, Sec2.IsSLEPathUpTo κ xL xR ρL ρR (W · ω)
      (fun i t => VL i t ω) (fun i t => VR i t ω) (B · ω) (e ω))
    (hB : ∀ ω ∈ G, Continuous (B · ω))
    (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0))
    (hσU : ∀ ω ∈ G, (σ ω : ℝ≥0∞) < U ω) (hUe : ∀ ω, U ω ≤ e ω)
    (hs : ∀ ω ∈ G, SepUpTo (W · ω) (VR k · ω) (U ω)) :
    (∀ t, Measurable[𝓕 t] (stoppedCoords xL xR a k G W B VL VR σ t)) ∧
      (∀ ω, Continuous (stoppedCoords xL xR a k G W B VL VR σ · ω)) := by
  have hσe : ∀ ω ∈ G, (σ ω : ℝ≥0∞) < e ω := fun ω hω => (hσU ω hω).trans_le (hUe ω)
  have hsub : ∀ ω ∈ G, Iic (σ ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < e ω} :=
    fun ω hω t ht => (ENNReal.coe_le_coe.2 ht).trans_lt (hσe ω hω)
  have hgap : ∀ ω ∈ G, ContinuousOn (fun t => VR k t ω - W t ω) (Iic (σ ω)) :=
    fun ω hω => (((hp ω hω).continuousOn_vR k).sub (hp ω hω).continuousOn_w).mono (hsub ω hω)
  have hpos : ∀ ω ∈ G, ∀ t ≤ σ ω, 0 < VR k t ω - W t ω := by
    intro ω hω t ht
    have hS := (hs ω hω).isSep_of_lt (hσU ω hω)
    simpa only [gap, Real.toNNReal_coe] using hS.pos t ⟨t.coe_nonneg, by exact_mod_cast ht⟩
  let g := gapStopR (0 : Fin 1) G W (fun _ => VR k) σ
  obtain ⟨hgm, hgc, hg0⟩ := stopped_gap_regular hE.adapted_W (hE.adapted_VR k) hσ hG hσe hgap hpos
  have hRc : ∀ ω ∈ G, ContinuousOn (fun t => rCoordAt a k (W · ω)
      (fun i s => VL i s ω) (fun i s => VR i s ω) t) (Iic (σ ω)) := by
    intro ω hω
    have hS := (hs ω hω).isSep_of_lt (hσU ω hω)
    have hmaps : MapsTo (fun t : ℝ≥0 => (t : ℝ)) (Iic (σ ω)) (Icc 0 (σ ω : ℝ)) :=
      fun t ht => ⟨t.coe_nonneg, by exact_mod_cast ht⟩
    have hα := (hS.continuousOn_alpha (xk := a)).comp NNReal.continuous_coe.continuousOn hmaps
    have hβ := (hS.continuousOn_beta (xk := a)).comp NNReal.continuous_coe.continuousOn hmaps
    have hC := ((hS.isRate ha).continuousOn_clk).comp NNReal.continuous_coe.continuousOn hmaps
    exact (continuousOn_pi.2 fun i => ((hp ω hω).continuousOn_vL i).mono (hsub ω hω)).prodMk
      ((continuousOn_pi.2 fun i => ((hp ω hω).continuousOn_vR i).mono (hsub ω hω)).prodMk
        (hα.prodMk (hβ.prodMk hC)))
  refine ⟨?_, ?_⟩
  · intro t
    let K : ℝ≥0 → Ω → RCoord nL nR := fun s ω =>
      ((fun i => if (s : ℝ≥0∞) < e ω then VL i s ω else 0),
        (fun i => if (s : ℝ≥0∞) < e ω then VR i s ω else 0),
        alphaK a g s ω, betaK a g s ω, clkK a g s ω)
    have hK : ∀ s, Measurable[𝓕 s] (K s) := fun s =>
      (@Measurable.of_eval Ω (Fin nL) (fun _ => ℝ) (𝓕 s) _ _
        fun i => Sec2.TwoSeed.measurable_killed (hE.adapted_VL i) s).prodMk
        ((@Measurable.of_eval Ω (Fin nR) (fun _ => ℝ) (𝓕 s) _ _
          fun i => Sec2.TwoSeed.measurable_killed (hE.adapted_VR i) s).prodMk
          ((measurable_alphaK hgm hgc s).prodMk
            ((measurable_betaK hgm hgc hg0 s).prodMk (Clock7.measurable_clkK hgm hgc hg0 s))))
    have hRm := Ito.measurable_stopped_of_agree hσ hK hG
      ((xL, xR, a, -1, 0) : RCoord nL nR) (X := fun s ω =>
        rCoordAt a k (W · ω) (fun i r => VL i r ω) (fun i r => VR i r ω) s)
      (fun ω hω s hs' => by
        have he := (ENNReal.coe_le_coe.2 hs').trans_lt (hσe ω hω)
        obtain ⟨hα, hβ⟩ := stopped_coefficients_eq (a := a) (W := W) (V := VR k) hω hs'
        have hC := Clock7.clkK_gapStop_eq (a := a) (W := W) (V := VR k) hω hs'
        simp only [K, g, he, ↓reduceIte, rCoordAt, hα, hβ, hC]) hRc t
    have hBm := Ito.measurable_stopped_of_agree hσ hE.brownian.2.1 hG 0
      (fun _ _ _ _ => rfl) (fun ω hω => (hB ω hω).continuousOn) t
    exact hRm.prodMk hBm
  · intro ω
    by_cases hω : ω ∈ G
    · simp only [stoppedCoords, rCoord, hω, ↓reduceIte]
      exact ((hRc ω hω).comp_continuous (continuous_id.min continuous_const)
        (fun t => mem_Iic.2 (min_le_right _ _))).prodMk
        ((hB ω hω).comp (continuous_id.min continuous_const))
    · simp only [stoppedCoords, rCoord, hω, ↓reduceIte]
      exact continuous_const

/-- Optional evaluation of a continuous adapted process, capped by a finite source stop. -/
theorem measurable_cap_stoppedCoords {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ} {Z : ℝ≥0 → Ω → RCoord nL nR × ℝ}
    (hZm : ∀ t, Measurable[𝓕 t] (Z t)) (hZc : ∀ ω, Continuous (Z · ω))
    {σ : Ω → ℝ≥0} {τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)) (hτ : IsStoppingTime 𝓕 τ) :
    Measurable[hτ.measurableSpace] fun ω => Z (Sec2.TwoSeed.capTime σ τ ω) ω := by
  have hprog := StronglyAdapted.isStronglyProgressive_of_continuous
    (fun t => (hZm t).stronglyMeasurable) hZc
  have hcap := Sec2.TwoSeed.isStoppingTime_capTime hσ hτ
  have h := measurable_stoppedValue hprog hcap
  have he : stoppedValue Z (fun ω => (Sec2.TwoSeed.capTime σ τ ω : WithTop ℝ≥0)) =
      fun ω => Z (Sec2.TwoSeed.capTime σ τ ω) ω := by
    funext ω
    simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe]
  rw [he] at h
  exact h.mono (IsStoppingTime.measurableSpace_mono hcap hτ
    (Sec2.TwoSeed.capTime_le_right _ _)) le_rfl

end InteractingSLE.Sec5.TwoMark.Adapt8
