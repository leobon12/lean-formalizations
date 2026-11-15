/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkMart9Bounds

/-!
# Localized first-mark retargeting martingales

The compact ordered box bounds the full coordinate density. The local adapted
coordinate result and the existing localized Itô formula then give drift-free
observable martingales for a local source evolution.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Mart9

open Zhan.Retarget

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {κ a b : ℝ} {xL ρL : Fin 0 → ℝ} {ρR : Fin 2 → ℝ}
  {W B : ℝ≥0 → Ω → ℝ} {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 2 → ℝ≥0 → Ω → ℝ}
  {e : Ω → ℝ≥0∞} {S : ℕ → Ω → ℝ≥0} {G : Set Ω}

variable (ha : 0 < a) (hab : a < b)
  (hE : Sec2.IsSLEEvolutionUpTo κ xL ![a, b] ρL ρR P 𝓕 W VL VR B e)
  (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
  (hgood : ∀ ω ∈ G, IsGood κ a b xL ρL ρR W B VL VR e S ω)
  (hS : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (S n ω : WithTop ℝ≥0))

include ha hab hE hGm hGc hgood hS in
/-- The actual locally stopped retargeting coordinates are adapted and continuous. -/
theorem stopped_coords_regular (n : ℕ) :
    (∀ t, Measurable[usualAugmentation 𝓕 P t]
      (Adapt8.stoppedCoords xL ![a, b] a 0 G W B VL VR (rLoc 0 G S W VL VR B e n) t)) ∧
    (∀ ω, Continuous (Adapt8.stoppedCoords xL ![a, b] a 0 G W B VL VR
      (rLoc 0 G S W VL VR B e n) · ω)) := by
  have hEu : Sec2.IsSLEEvolutionUpTo κ xL ![a, b] ρL ρR P (usualAugmentation 𝓕 P) W VL VR B e :=
    ⟨Ito.isFilteredBrownianReal_usualAugmentation hE.brownian,
      Ito.adaptedBefore_mono (Ito.le_usualAugmentation 𝓕 P) hE.adapted_W,
      fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation 𝓕 P) (hE.adapted_VL i),
      fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation 𝓕 P) (hE.adapted_VR i), hE.ae_path⟩
  have hG0 : MeasurableSet[usualAugmentation 𝓕 P 0] G := by
    simpa only [compl_compl] using
      (Ito.measurableSet_usualAugmentation_of_null (𝓕 := 𝓕) hGm.compl hGc 0).compl
  exact Adapt8.stopped_coords_regular ha hEu hG0 (fun ω hω => (hgood ω hω).path)
    (fun ω hω => (hgood ω hω).contB) (isStoppingTime_rLoc hE hGm hGc hgood hS n)
    (fun ω hω => (hgood ω hω).loc_lt n) (fun _ => sepTime_le _ _ _)
    (fun ω hω => ((hgood ω hω).data ha hab).sep)

include ha hab hE hGm hGc hgood hS in
/-- Any smooth observable with zero coordinate generator is a local source-time martingale. -/
theorem martingale_observable_stopped {F : RCoord 0 2 × ℝ → ℝ}
    (hF : ContDiffOn ℝ 3 F (obsRegion κ xL ![a, b] ρL ρR 0))
    (hgen : ∀ p ∈ obsRegion κ xL ![a, b] ρL ρR 0,
      (∀ i, p.1.1 i ≠ drv κ xL ![a, b] ρL ρR p) →
      (∀ i, p.1.2.1 i ≠ drv κ xL ![a, b] ρL ρR p) →
        Ito.itoGen F p (dens κ xL ![a, b] ρL ρR 0 p) = 0) (n : ℕ) :
    Martingale (fun t ω => F
      (rCoord xL ![a, b] a 0 G W VL VR (min t (rLoc 0 G S W VL VR B e n ω)) ω,
        Sec2.TwoSeed.brownG G B (min t (rLoc 0 G S W VL VR B e n ω)) ω))
      (usualAugmentation 𝓕 P) P := by
  let σ := rLoc 0 G S W VL VR B e n
  have hlam : ∀ ω, IntervalIntegrable
      (rDens κ xL ![a, b] ρL ρR 0 a G W VL VR B · ω) volume 0 (σ ω) := by
    intro ω
    by_cases hω : ω ∈ G
    · have hg := hgood ω hω
      simp only [rDens, hω, ↓reduceIte]
      convert intervalIntegrable_rDensAt (hg.path.mono (sepTime_le _ _ _))
        (hg.data ha hab) (hg.loc_lt (G := G) n) using 1
      rfl
    · simp only [rDens, hω, ↓reduceIte]
      exact intervalIntegrable_const
  have hΛ : ∀ ω (t : ℝ≥0), t ≤ σ ω →
      rCoord xL ![a, b] a 0 G W VL VR t ω = rCoord xL ![a, b] a 0 G W VL VR 0 ω +
        ∫ s in (0 : ℝ)..t, rDens κ xL ![a, b] ρL ρR 0 a G W VL VR B s ω := by
    intro ω t ht
    by_cases hω : ω ∈ G
    · have hg := hgood ω hω
      simp only [rCoord, rDens, hω, ↓reduceIte]
      exact rCoordAt_eq_add_integral (hg.path.mono (sepTime_le _ _ _)) (hg.data ha hab)
        ((ENNReal.coe_le_coe.2 ht).trans_lt (hg.loc_lt n))
    · simp only [rCoord, rDens, hω, ↓reduceIte, intervalIntegral.integral_zero, add_zero]
  obtain ⟨Kb, hKb⟩ := exists_integral_density_bound ha hab hgood n
  have hK : ∀ ω (t : ℝ≥0), t ≤ σ ω →
      (rCoord xL ![a, b] a 0 G W VL VR t ω, Sec2.TwoSeed.brownG G B t ω) ∈
        orderedBox κ xL ρL ρR a b n := by
    intro ω t ht
    by_cases hω : ω ∈ G
    · simpa only [rCoord, Sec2.TwoSeed.brownG, hω, ↓reduceIte] using
        mem_orderedBox ha hab hgood hω ht
    · simp only [rCoord, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
      exact ⟨Or.inl rfl, hab.le⟩
  have hM := Ito.martingale_itoLocalized (isFilteredBrownianReal_brownG hE hGm hGc hgood)
    (continuous_brownG hgood) (isOpen_obsRegion κ xL ![a, b] ρL ρR 0) hF
    (isCompact_orderedBox (κ := κ) (xL := xL) (ρL := ρL) (ρR := ρR) (a := a) (b := b) n)
    (fun _ hp => rKc_subset_obsRegion κ xL ![a, b] ρL ρR 0 a (initial_mem_region ha hab) n hp.1)
    (isStoppingTime_rLoc hE hGm hGc hgood hS n)
    (fun t => ((stopped_coords_regular ha hab hE hGm hGc hgood hS n).1 t).fst)
    hlam hΛ hKb hK
  have hzero : ∀ (t : ℝ≥0) ω, ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0),
      Ito.itoGen F (rCoord xL ![a, b] a 0 G W VL VR s.toNNReal ω,
        Sec2.TwoSeed.brownG G B s.toNNReal ω)
        (rDens κ xL ![a, b] ρL ρR 0 a G W VL VR B s ω) = 0 := by
    intro t ω
    by_cases hω : ω ∈ G
    · have hg := hgood ω hω
      simp only [rCoord, rDens, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
      refine intervalIntegral.integral_zero_ae ?_
      filter_upwards [ae_itoGen_eq_zero (hg.path.mono (sepTime_le _ _ _))
        (hg.data ha hab) hgen (hg.loc_lt (G := G) n)] with s hs hsI
      rw [uIoc_of_le (min t (σ ω)).coe_nonneg] at hsI
      exact hs ⟨hsI.1, hsI.2.trans (by exact_mod_cast min_le_right t (σ ω))⟩
    · have h0 : σ ω = 0 := rLoc_of_not_mem hω n
      rw [h0, min_eq_right (zero_le (a := t)), NNReal.coe_zero, intervalIntegral.integral_same]
  dsimp only [σ] at hzero
  simpa only [hzero, sub_zero] using hM

include ha hab hE hGm hGc hgood hS in
/-- The canonical drift-free first-mark observable, locally stopped, is a martingale. -/
theorem martingale_obs_stopped (hκ : 0 ≤ κ) (n : ℕ) :
    Martingale (fun t ω => obs κ xL ![a, b] ρL ρR 0
      (rCoord xL ![a, b] a 0 G W VL VR (min t (rLoc 0 G S W VL VR B e n ω)) ω,
        Sec2.TwoSeed.brownG G B (min t (rLoc 0 G S W VL VR B e n ω)) ω))
      (usualAugmentation 𝓕 P) P :=
  martingale_observable_stopped ha hab hE hGm hGc hgood hS
    (contDiffOn_obs κ xL ![a, b] ρL ρR 0)
    (fun _ hp hL hR => itoGen_obs_eq_zero hκ hp hL hR) n

include ha hab hE hGm hGc hgood hS in
/-- The quadratic correction of the first-mark observable is a martingale. -/
theorem martingale_obs2_stopped (hκ : 0 ≤ κ) (c : ℝ) (n : ℕ) :
    Martingale (fun t ω => obs2 κ xL ![a, b] ρL ρR 0 c
      (rCoord xL ![a, b] a 0 G W VL VR (min t (rLoc 0 G S W VL VR B e n ω)) ω,
        Sec2.TwoSeed.brownG G B (min t (rLoc 0 G S W VL VR B e n ω)) ω))
      (usualAugmentation 𝓕 P) P :=
  martingale_observable_stopped ha hab hE hGm hGc hgood hS
    (contDiffOn_obs2 κ xL ![a, b] ρL ρR 0 c)
    (fun _ hp hL hR => itoGen_obs2_eq_zero hκ c hp hL hR) n

include ha hab hE hGm hGc hgood hS in
/-- The canonical first-mark exponential observable is a martingale. -/
theorem martingale_expObs_stopped (hκ : 0 < κ) (θ : ℝ) (n : ℕ) :
    Martingale (fun t ω => expObs κ xL ![a, b] ρL ρR 0 θ
      (rCoord xL ![a, b] a 0 G W VL VR (min t (rLoc 0 G S W VL VR B e n ω)) ω,
        Sec2.TwoSeed.brownG G B (min t (rLoc 0 G S W VL VR B e n ω)) ω))
      (usualAugmentation 𝓕 P) P :=
  martingale_observable_stopped ha hab hE hGm hGc hgood hS
    (contDiffOn_expObs (κ := κ) (xL := xL) (xR := ![a, b]) (ρL := ρL) (ρR := ρR) (k := 0) θ)
    (fun _ hp hL hR => itoGen_expObs_eq_zero hκ θ hp hL hR) n

end InteractingSLE.Sec5.TwoMark.Mart9
