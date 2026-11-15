/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.MixtureA33ChordalLoc
import InteractingSLE.Spec.Zhan.StripTimeMart

/-!
# Upper strip marks: the strip martingale and its bracket in chordal time

Packet PROVE-ZHAN-A33. PROVE-ZHAN-A2's `StripTimeMart.lean` with the end mark at index `0`: on a good event `G`
(`IsGoodUp`), the observable `Φ = upObs` and `Φ² − κ t(s)` (`upObs2`) evaluated along the evolution and stopped at the
localizing times `σ_n` (`upLoc`) are martingales of the usual augmentation of the evolution's filtration
(`martingale_upObs`, `martingale_upObs2`), by the localized Itô formula with vanishing generators.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.UpMark

open Zhan

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}


open scoped Classical in
/-- The strip coordinates on the good event (the initial coordinates off it). -/
def upCoordS (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : SCoord nL nR :=
  if ω ∈ G then upCoordAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) t else (xL, xR, 0)

open scoped Classical in
/-- Their density on the good event (`0` off it). -/
def upDensS (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (s : ℝ) (ω : Ω) : SCoord nL nR :=
  if ω ∈ G then upDensAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s else 0

open scoped Classical in
/-- The gap `W − v` stopped at `σ`, on the good event (`1` off it). -/
def upGapStop (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0) (r : ℝ≥0)
    (ω : Ω) : ℝ :=
  if ω ∈ G then W (min r (σ ω)) ω - VL 0 (min r (σ ω)) ω else 1

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω}

section Adapted

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsGoodUp κ xL xR ρL ρR W VL VR B ζ ω)

/-- A killed process (`0` from `ζ` on). -/
def killedAt (ζ : Ω → ℝ≥0∞) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : ℝ≥0∞) < ζ ω then X t ω else 0

include hE hGm hGc hgood in
/-- The stopped gap is adapted. -/
theorem measurable_upGapStop (n : ℕ) (r : ℝ≥0) :
    Measurable[usualAugmentation 𝓕 P r] (upGapStop G W VL (upLoc G W VL VR B ζ n) r) := by
  obtain ⟨-, hWa, hVLa, -, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hG0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) 0
  have hσ := isStoppingTime_upLoc hE hGm hGc hgood n
  have hK : ∀ s, Measurable[usualAugmentation 𝓕 P s] fun ω =>
      killedAt ζ W s ω - killedAt ζ (VL 0) s ω := fun s =>
    (Sec2.TwoSeed.measurable_killed hWa s).sub (Sec2.TwoSeed.measurable_killed (hVLa _) s)
  have h := Ito.measurable_stopped_of_agree (X := fun s ω => W s ω - VL 0 s ω) hσ hK hG0
    (1 : ℝ) (fun ω hω s hs => ?_) (fun ω hω => ?_) r
  · exact h
  · have hlife := (isStripLife_upLoc (hgood ω hω) hω (n := n)).mono hs
    simp only [killedAt, hlife.1, ↓reduceIte]
  · have hF := (hgood ω hω).1.isForcePath
    have hsub : Iic (upLoc G W VL VR B ζ n ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs =>
      ((isStripLife_upLoc (hgood ω hω) hω (n := n)).mono hs).1
    exact (hF.continuousOn_w.sub (hF.continuousOn_vL _)).mono hsub

include hgood in
theorem continuous_upGapStop (n : ℕ) (ω : Ω) :
    Continuous fun r => upGapStop G W VL (upLoc G W VL VR B ζ n) r ω := by
  by_cases hω : ω ∈ G
  · have hF := (hgood ω hω).1.isForcePath
    have hsub : Iic (upLoc G W VL VR B ζ n ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs =>
      ((isStripLife_upLoc (hgood ω hω) hω (n := n)).mono hs).1
    have hc := (hF.continuousOn_w.sub (hF.continuousOn_vL 0)).mono hsub
    simp only [upGapStop, hω, ↓reduceIte]
    exact hc.comp_continuous (continuous_id.min continuous_const) fun r => mem_Iic.2 (min_le_right _ _)
  · simp only [upGapStop, hω, ↓reduceIte]; exact continuous_const

include hE hGm hGc hgood in
/-- **The stopped strip coordinates are adapted.** -/
theorem measurable_upCoordS_stopped (n : ℕ) (t : ℝ≥0) :
    Measurable[usualAugmentation 𝓕 P t] fun ω =>
      upCoordS xL xR G W VL VR (min t (upLoc G W VL VR B ζ n ω)) ω := by
  obtain ⟨-, -, hVLa, hVRa, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  set 𝓖 := usualAugmentation 𝓕 P
  set σ := upLoc G W VL VR B ζ n
  have hG0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) 0
  have hσ := isStoppingTime_upLoc hE hGm hGc hgood n
  have hprog : IsStronglyProgressive 𝓖 (upGapStop G W VL σ) :=
    StronglyAdapted.isStronglyProgressive_of_continuous
      (fun r => (measurable_upGapStop hE hGm hGc hgood n r).stronglyMeasurable)
      (continuous_upGapStop hgood n)
  set K : ℝ≥0 → Ω → SCoord nL nR := fun s ω => ((fun i => killedAt ζ (VL i) s ω),
    (fun j => killedAt ζ (VR j) s ω), ∫ u in (0 : ℝ)..s, ((upGapStop G W VL σ u.toNNReal ω) ^ 2)⁻¹)
    with hKdef
  have hK : ∀ s, Measurable[𝓖 s] (K s) := fun s => by
    refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
    · exact @Measurable.of_eval Ω (Fin (nL + 1)) (fun _ => ℝ) (𝓖 s) _ _ fun i =>
        Sec2.TwoSeed.measurable_killed (hVLa i) s
    · exact @Measurable.of_eval Ω (Fin nR) (fun _ => ℝ) (𝓖 s) _ _ fun j =>
        Sec2.TwoSeed.measurable_killed (hVRa j) s
    · exact (Girsanov.stronglyMeasurable_integral_comp hprog
        (g := fun x : ℝ => (x ^ 2)⁻¹) (by fun_prop) s).measurable
  have h := Ito.measurable_stopped_of_agree
    (X := fun s ω => upCoordAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s) hσ hK hG0
    ((xL, xR, 0) : SCoord nL nR) (fun ω hω s hs => ?_) (fun ω hω => ?_) t
  · exact h
  · have hlife := (isStripLife_upLoc (hgood ω hω) hω (n := n)).mono hs
    refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun j => ?_) ?_)
    · simp only [hKdef, killedAt, hlife.1, ↓reduceIte, upCoordAt]
    · simp only [hKdef, killedAt, hlife.1, ↓reduceIte, upCoordAt]
    · simp only [hKdef, upCoordAt, Strip.stripClock, Strip.extPath]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le s.coe_nonneg] at hu
      have hus : u.toNNReal ≤ σ ω := (Sec2.toNNReal_le_of_mem_Icc hu).trans hs
      simp only [upGapStop, hω, ↓reduceIte, min_eq_left hus]
  · have hF := (hgood ω hω).1.isForcePath
    have hlife := isStripLife_upLoc (hgood ω hω) hω (n := n)
    have hsub : Iic (σ ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs => (hlife.mono hs).1
    have hT : ContinuousOn (fun s : ℝ≥0 => Strip.stripClock (Strip.extPath (W · ω))
        (Strip.extPath (VL 0 · ω)) s) (Iic (σ ω)) := by
      have hc := intervalIntegral.continuousOn_primitive_interval'
        (intervalIntegrable_clockRate hF hlife) (left_mem_uIcc (a := (0 : ℝ)) (b := σ ω))
      refine hc.comp NNReal.continuous_coe.continuousOn fun s hs => ?_
      rw [uIcc_of_le (σ ω).coe_nonneg]
      exact ⟨s.coe_nonneg, by exact_mod_cast hs⟩
    exact (continuousOn_pi.2 fun i => (hF.continuousOn_vL i).mono hsub).prodMk
      ((continuousOn_pi.2 fun j => (hF.continuousOn_vR j).mono hsub).prodMk hT)

include hE hGm hGc hgood in
/-- The modified Brownian motion stopped at `σ_n` is adapted. -/
theorem measurable_brownG_stopped_up (n : ℕ) (t : ℝ≥0) :
    Measurable[usualAugmentation 𝓕 P t] fun ω =>
      Sec2.TwoSeed.brownG G B (min t (upLoc G W VL VR B ζ n ω)) ω := by
  have hG0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) 0
  have hB' := isFilteredBrownianReal_brownG_up hE hGm hGc hgood
  have h := Ito.measurable_stopped_of_agree (X := Sec2.TwoSeed.brownG G B)
    (isStoppingTime_upLoc hE hGm hGc hgood n) hB'.2.1 hG0 (0 : ℝ) (fun ω _ s _ => rfl)
    (fun ω _ => (continuous_brownG_up hgood ω).continuousOn) t
  convert h using 2 with ω
  by_cases hω : ω ∈ G <;> simp [Sec2.TwoSeed.brownG, hω]

include hE hGm hGc hgood in
/-- **A localized observable with vanishing generator is a martingale** (the common step for `Φ` and `Φ² − κ t`). -/
theorem martingale_obs_stopped_up (h0 : stripInit xL xR ∈ upRegion κ xL xR ρL ρR)
    {F : SCoord nL nR × ℝ → ℝ} (hF : ContDiffOn ℝ 3 F (upRegion κ xL xR ρL ρR))
    (hgen : ∀ ω ∈ G, ∀ (n : ℕ), ∀ᵐ s ∂volume, s ∈ Ioc 0 (upLoc G W VL VR B ζ n ω : ℝ) →
      Ito.itoGen F (upCoordAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s.toNNReal,
        B s.toNNReal ω) (upDensAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s) = 0)
    (n : ℕ) :
    Martingale (fun t ω => F (upCoordS xL xR G W VL VR (min t (upLoc G W VL VR B ζ n ω)) ω,
      Sec2.TwoSeed.brownG G B (min t (upLoc G W VL VR B ζ n ω)) ω)) (usualAugmentation 𝓕 P) P := by
  set σ := upLoc G W VL VR B ζ n with hσdef
  have hB' := isFilteredBrownianReal_brownG_up hE hGm hGc hgood
  have hlam : ∀ ω, IntervalIntegrable (upDensS G W VL VR · ω) volume 0 (σ ω) := fun ω => by
    by_cases hω : ω ∈ G
    · simpa only [upDensS, hω, ↓reduceIte] using intervalIntegrable_upDensAt
        (hgood ω hω).1.isForcePath (isStripLife_upLoc (hgood ω hω) hω (n := n))
    · simp only [upDensS, hω, ↓reduceIte]; exact intervalIntegrable_const
  have hΛ : ∀ ω (t : ℝ≥0), t ≤ σ ω → upCoordS xL xR G W VL VR t ω =
      upCoordS xL xR G W VL VR 0 ω + ∫ s in (0 : ℝ)..t, upDensS G W VL VR s ω := by
    intro ω t ht
    by_cases hω : ω ∈ G
    · simp only [upCoordS, upDensS, hω, ↓reduceIte]
      exact upCoordAt_eq_add_integral (hgood ω hω).1.isForcePath
        ((isStripLife_upLoc (hgood ω hω) hω (n := n)).mono ht)
    · simp only [upCoordS, upDensS, hω, ↓reduceIte, intervalIntegral.integral_zero, add_zero]
  have hKb : ∀ ω, ∫ s in (0 : ℝ)..(σ ω), ‖upDensS G W VL VR s ω‖ ≤ stripKb xL xR n := by
    intro ω
    by_cases hω : ω ∈ G
    · simpa only [upDensS, hω, ↓reduceIte] using
        integral_norm_upDensAt_le_stripKb (hgood ω hω) hω hgood (n := n)
    · simp only [upDensS, hω, ↓reduceIte, norm_zero, intervalIntegral.integral_zero]
      exact stripKb_nonneg xL xR n
  have hK : ∀ ω (t : ℝ≥0), t ≤ σ ω →
      (upCoordS xL xR G W VL VR t ω, Sec2.TwoSeed.brownG G B t ω) ∈ upKc κ xL xR ρL ρR n := by
    intro ω t ht
    by_cases hω : ω ∈ G
    · simpa only [upCoordS, Sec2.TwoSeed.brownG, hω, ↓reduceIte] using
        mem_upKc_of_le_upLoc (hgood ω hω) hω hgood ht
    · simp only [upCoordS, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
      exact mem_insert _ _
  have hM := Ito.martingale_itoLocalized hB' (continuous_brownG_up hgood)
    (isOpen_upRegion κ xL xR ρL ρR) hF (isCompact_upKc κ xL xR ρL ρR n)
    (upKc_subset_region κ xL xR ρL ρR h0 n) (isStoppingTime_upLoc hE hGm hGc hgood n)
    (measurable_upCoordS_stopped hE hGm hGc hgood n) hlam hΛ hKb hK
  have hzero : ∀ (t : ℝ≥0) ω, ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0),
      Ito.itoGen F (upCoordS xL xR G W VL VR s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω)
        (upDensS G W VL VR s ω) = 0 := by
    intro t ω
    by_cases hω : ω ∈ G
    · simp only [upCoordS, upDensS, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
      refine intervalIntegral.integral_zero_ae ?_
      filter_upwards [hgen ω hω n] with s hs hsI
      rw [uIoc_of_le (min t (σ ω)).coe_nonneg] at hsI
      exact hs ⟨hsI.1, hsI.2.trans (by exact_mod_cast min_le_right t (σ ω))⟩
    · have h0' : σ ω = 0 := upLoc_of_not_mem hω n
      rw [h0', min_eq_right (zero_le (a := t)), NNReal.coe_zero, intervalIntegral.integral_same]
  have e : (fun t ω => F (upCoordS xL xR G W VL VR (min t (σ ω)) ω,
      Sec2.TwoSeed.brownG G B (min t (σ ω)) ω) -
      ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0), Ito.itoGen F (upCoordS xL xR G W VL VR s.toNNReal ω,
        Sec2.TwoSeed.brownG G B s.toNNReal ω) (upDensS G W VL VR s ω)) =
      fun t ω => F (upCoordS xL xR G W VL VR (min t (σ ω)) ω,
        Sec2.TwoSeed.brownG G B (min t (σ ω)) ω) := by
    funext t ω; rw [hzero t ω, sub_zero]
  rw [e] at hM
  exact hM

include hE hGm hGc hgood in
/-- **The strip martingale** `Φ` stopped at `σ_n` is a martingale of the usual augmentation. -/
theorem martingale_upObs (hκ : 0 ≤ κ) (h0 : stripInit xL xR ∈ upRegion κ xL xR ρL ρR) (n : ℕ) :
    Martingale (fun t ω => upObs κ xL xR ρL ρR
      (upCoordS xL xR G W VL VR (min t (upLoc G W VL VR B ζ n ω)) ω,
        Sec2.TwoSeed.brownG G B (min t (upLoc G W VL VR B ζ n ω)) ω))
      (usualAugmentation 𝓕 P) P := by
  refine martingale_obs_stopped_up hE hGm hGc hgood h0 (contDiffOn_upObs κ xL xR ρL ρR)
    (fun ω hω m => ?_) n
  have hω' := hgood ω hω
  have hlife := isStripLife_upLoc hω' hω (n := m)
  have h := ae_itoGen_upObs_eq_zero hω'.1 hκ hlife.1 fun s hs =>
    upKc_subset_region κ xL xR ρL ρR h0 m (mem_upKc_of_le_upLoc hω' hω hgood hs)
  exact h

include hE hGm hGc hgood in
/-- **Its bracket**: `Φ² − κ t(s)` stopped at `σ_n` is a martingale of the usual augmentation. -/
theorem martingale_upObs2 (hκ : 0 ≤ κ) (h0 : stripInit xL xR ∈ upRegion κ xL xR ρL ρR) (n : ℕ) :
    Martingale (fun t ω => upObs2 κ xL xR ρL ρR
      (upCoordS xL xR G W VL VR (min t (upLoc G W VL VR B ζ n ω)) ω,
        Sec2.TwoSeed.brownG G B (min t (upLoc G W VL VR B ζ n ω)) ω))
      (usualAugmentation 𝓕 P) P := by
  refine martingale_obs_stopped_up hE hGm hGc hgood h0 (contDiffOn_upObs2 κ xL xR ρL ρR)
    (fun ω hω m => ?_) n
  have hω' := hgood ω hω
  have hlife := isStripLife_upLoc hω' hω (n := m)
  have h := ae_itoGen_upObs2_eq_zero hω'.1 hκ hlife.1 fun s hs =>
    upKc_subset_region κ xL xR ρL ρR h0 m (mem_upKc_of_le_upLoc hω' hω hgood hs)
  exact h

end Adapted

end InteractingSLE.ZhanGT4.UpMark
