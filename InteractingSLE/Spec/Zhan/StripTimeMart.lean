/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripTimeLoc
import InteractingSLE.Spec.Sec2.GirsanovDensity

/-!
# The strip martingale and its bracket in chordal time

Packet PROVE-ZHAN-A2 (Astra §3, the target change into the strip, ruling R36). For an integrated chordal evolution
whose outermost left mark `v` is the strip end, on a good event `G` on which the strip clock is unbounded on the strip
life (`IsGoodStrip`), the strip observable `Φ` and `Φ² − κ t(s)` (`StripTimeObs.lean`) evaluated along the evolution
and stopped at the localizing times `σ_n` (`StripTimeLoc.lean`) are martingales of the usual augmentation of the
evolution's filtration (`martingale_stripMartObs`, `martingale_stripMartObs2`). This is the chordal-time form of "the strip
driver is `√κ` times a Brownian motion in the strip clock": `Φ` is a continuous local martingale with
`d⟨Φ⟩ = κ dt(s)`.

Proof: the localized Itô formula (`Ito.martingale_itoLocalized`) in the coordinates `Λ = (V^L, V^R, t(s))` (on `G`;
the initial point off `G`), with the Brownian motion modified off `G` (`Sec2.TwoSeed.brownG`), on the compact set
`stripKc`; the drift integral vanishes because the generators vanish at almost every time
(`ae_itoGen_stripMartObs_eq_zero`). The strip-clock coordinate is adapted because it is the running integral of the
continuous adapted stopped gap `(W − v)_{· ∧ σ_n}` (`Girsanov.stronglyMeasurable_integral_comp`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}

open scoped Classical in
/-- The strip coordinates on the good event (the initial coordinates off it). -/
def coordS (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : SCoord nL nR :=
  if ω ∈ G then stripCoordAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) t else (xL, xR, 0)

open scoped Classical in
/-- Their density on the good event (`0` off it). -/
def densS (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (s : ℝ) (ω : Ω) : SCoord nL nR :=
  if ω ∈ G then stripDensAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s else 0

open scoped Classical in
/-- The gap `W − v` stopped at `σ`, on the good event (`1` off it). -/
def gapStop (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0) (r : ℝ≥0)
    (ω : Ω) : ℝ :=
  if ω ∈ G then W (min r (σ ω)) ω - VL (Fin.last nL) (min r (σ ω)) ω else 1

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω}

section Adapted

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsGoodStrip κ xL xR ρL ρR W VL VR B ζ ω)

/-- A killed process (`0` from `ζ` on). -/
def killedAt (ζ : Ω → ℝ≥0∞) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : ℝ≥0∞) < ζ ω then X t ω else 0

include hE hGm hGc hgood in
/-- The stopped gap is adapted. -/
theorem measurable_gapStop (n : ℕ) (r : ℝ≥0) :
    Measurable[usualAugmentation 𝓕 P r] (gapStop G W VL (stripLoc G W VL VR B ζ n) r) := by
  obtain ⟨-, hWa, hVLa, -, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hG0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) 0
  have hσ := isStoppingTime_stripLoc hE hGm hGc hgood n
  have hK : ∀ s, Measurable[usualAugmentation 𝓕 P s] fun ω =>
      killedAt ζ W s ω - killedAt ζ (VL (Fin.last nL)) s ω := fun s =>
    (Sec2.TwoSeed.measurable_killed hWa s).sub (Sec2.TwoSeed.measurable_killed (hVLa _) s)
  have h := Ito.measurable_stopped_of_agree (X := fun s ω => W s ω - VL (Fin.last nL) s ω) hσ hK hG0
    (1 : ℝ) (fun ω hω s hs => ?_) (fun ω hω => ?_) r
  · exact h
  · have hlife := (isStripLife_stripLoc (hgood ω hω) hω (n := n)).mono hs
    simp only [killedAt, hlife.1, ↓reduceIte]
  · have hF := (hgood ω hω).1.isForcePath
    have hsub : Iic (stripLoc G W VL VR B ζ n ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs =>
      ((isStripLife_stripLoc (hgood ω hω) hω (n := n)).mono hs).1
    exact (hF.continuousOn_w.sub (hF.continuousOn_vL _)).mono hsub

include hgood in
theorem continuous_gapStop (n : ℕ) (ω : Ω) :
    Continuous fun r => gapStop G W VL (stripLoc G W VL VR B ζ n) r ω := by
  by_cases hω : ω ∈ G
  · have hF := (hgood ω hω).1.isForcePath
    have hsub : Iic (stripLoc G W VL VR B ζ n ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs =>
      ((isStripLife_stripLoc (hgood ω hω) hω (n := n)).mono hs).1
    have hc := (hF.continuousOn_w.sub (hF.continuousOn_vL (Fin.last nL))).mono hsub
    simp only [gapStop, hω, ↓reduceIte]
    exact hc.comp_continuous (continuous_id.min continuous_const) fun r => mem_Iic.2 (min_le_right _ _)
  · simp only [gapStop, hω, ↓reduceIte]; exact continuous_const

include hE hGm hGc hgood in
/-- **The stopped strip coordinates are adapted.** -/
theorem measurable_coordS_stopped (n : ℕ) (t : ℝ≥0) :
    Measurable[usualAugmentation 𝓕 P t] fun ω =>
      coordS xL xR G W VL VR (min t (stripLoc G W VL VR B ζ n ω)) ω := by
  obtain ⟨-, -, hVLa, hVRa, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  set 𝓖 := usualAugmentation 𝓕 P
  set σ := stripLoc G W VL VR B ζ n
  have hG0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) 0
  have hσ := isStoppingTime_stripLoc hE hGm hGc hgood n
  have hprog : IsStronglyProgressive 𝓖 (gapStop G W VL σ) :=
    StronglyAdapted.isStronglyProgressive_of_continuous
      (fun r => (measurable_gapStop hE hGm hGc hgood n r).stronglyMeasurable)
      (continuous_gapStop hgood n)
  set K : ℝ≥0 → Ω → SCoord nL nR := fun s ω => ((fun i => killedAt ζ (VL i) s ω),
    (fun j => killedAt ζ (VR j) s ω), ∫ u in (0 : ℝ)..s, ((gapStop G W VL σ u.toNNReal ω) ^ 2)⁻¹)
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
    (X := fun s ω => stripCoordAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s) hσ hK hG0
    ((xL, xR, 0) : SCoord nL nR) (fun ω hω s hs => ?_) (fun ω hω => ?_) t
  · exact h
  · have hlife := (isStripLife_stripLoc (hgood ω hω) hω (n := n)).mono hs
    refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun j => ?_) ?_)
    · simp only [hKdef, killedAt, hlife.1, ↓reduceIte, stripCoordAt]
    · simp only [hKdef, killedAt, hlife.1, ↓reduceIte, stripCoordAt]
    · simp only [hKdef, stripCoordAt, Strip.stripClock, Strip.extPath]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le s.coe_nonneg] at hu
      have hus : u.toNNReal ≤ σ ω := (Sec2.toNNReal_le_of_mem_Icc hu).trans hs
      simp only [gapStop, hω, ↓reduceIte, min_eq_left hus]
  · have hF := (hgood ω hω).1.isForcePath
    have hlife := isStripLife_stripLoc (hgood ω hω) hω (n := n)
    have hsub : Iic (σ ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs => (hlife.mono hs).1
    have hT : ContinuousOn (fun s : ℝ≥0 => Strip.stripClock (Strip.extPath (W · ω))
        (Strip.extPath (VL (Fin.last nL) · ω)) s) (Iic (σ ω)) := by
      have hc := intervalIntegral.continuousOn_primitive_interval'
        (intervalIntegrable_clockRate hF hlife) (left_mem_uIcc (a := (0 : ℝ)) (b := σ ω))
      refine hc.comp NNReal.continuous_coe.continuousOn fun s hs => ?_
      rw [uIcc_of_le (σ ω).coe_nonneg]
      exact ⟨s.coe_nonneg, by exact_mod_cast hs⟩
    exact (continuousOn_pi.2 fun i => (hF.continuousOn_vL i).mono hsub).prodMk
      ((continuousOn_pi.2 fun j => (hF.continuousOn_vR j).mono hsub).prodMk hT)

include hE hGm hGc hgood in
/-- The modified Brownian motion stopped at `σ_n` is adapted. -/
theorem measurable_brownG_stopped_strip (n : ℕ) (t : ℝ≥0) :
    Measurable[usualAugmentation 𝓕 P t] fun ω =>
      Sec2.TwoSeed.brownG G B (min t (stripLoc G W VL VR B ζ n ω)) ω := by
  have hG0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) 0
  have hB' := isFilteredBrownianReal_brownG_strip hE hGm hGc hgood
  have h := Ito.measurable_stopped_of_agree (X := Sec2.TwoSeed.brownG G B)
    (isStoppingTime_stripLoc hE hGm hGc hgood n) hB'.2.1 hG0 (0 : ℝ) (fun ω _ s _ => rfl)
    (fun ω _ => (continuous_brownG_strip hgood ω).continuousOn) t
  convert h using 2 with ω
  by_cases hω : ω ∈ G <;> simp [Sec2.TwoSeed.brownG, hω]

include hE hGm hGc hgood in
/-- **A localized observable with vanishing generator is a martingale** (the common step for `Φ` and `Φ² − κ t`). -/
theorem martingale_obs_stopped (h0 : stripInit xL xR ∈ stripMartRegion κ xL xR ρL ρR)
    {F : SCoord nL nR × ℝ → ℝ} (hF : ContDiffOn ℝ 3 F (stripMartRegion κ xL xR ρL ρR))
    (hgen : ∀ ω ∈ G, ∀ (n : ℕ), ∀ᵐ s ∂volume, s ∈ Ioc 0 (stripLoc G W VL VR B ζ n ω : ℝ) →
      Ito.itoGen F (stripCoordAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s.toNNReal,
        B s.toNNReal ω) (stripDensAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s) = 0)
    (n : ℕ) :
    Martingale (fun t ω => F (coordS xL xR G W VL VR (min t (stripLoc G W VL VR B ζ n ω)) ω,
      Sec2.TwoSeed.brownG G B (min t (stripLoc G W VL VR B ζ n ω)) ω)) (usualAugmentation 𝓕 P) P := by
  set σ := stripLoc G W VL VR B ζ n with hσdef
  have hB' := isFilteredBrownianReal_brownG_strip hE hGm hGc hgood
  have hlam : ∀ ω, IntervalIntegrable (densS G W VL VR · ω) volume 0 (σ ω) := fun ω => by
    by_cases hω : ω ∈ G
    · simpa only [densS, hω, ↓reduceIte] using intervalIntegrable_stripDensAt
        (hgood ω hω).1.isForcePath (isStripLife_stripLoc (hgood ω hω) hω (n := n))
    · simp only [densS, hω, ↓reduceIte]; exact intervalIntegrable_const
  have hΛ : ∀ ω (t : ℝ≥0), t ≤ σ ω → coordS xL xR G W VL VR t ω =
      coordS xL xR G W VL VR 0 ω + ∫ s in (0 : ℝ)..t, densS G W VL VR s ω := by
    intro ω t ht
    by_cases hω : ω ∈ G
    · simp only [coordS, densS, hω, ↓reduceIte]
      exact stripCoordAt_eq_add_integral (hgood ω hω).1.isForcePath
        ((isStripLife_stripLoc (hgood ω hω) hω (n := n)).mono ht)
    · simp only [coordS, densS, hω, ↓reduceIte, intervalIntegral.integral_zero, add_zero]
  have hKb : ∀ ω, ∫ s in (0 : ℝ)..(σ ω), ‖densS G W VL VR s ω‖ ≤ stripKb xL xR n := by
    intro ω
    by_cases hω : ω ∈ G
    · simpa only [densS, hω, ↓reduceIte] using
        integral_norm_stripDensAt_le_stripKb (hgood ω hω) hω hgood (n := n)
    · simp only [densS, hω, ↓reduceIte, norm_zero, intervalIntegral.integral_zero]
      exact stripKb_nonneg xL xR n
  have hK : ∀ ω (t : ℝ≥0), t ≤ σ ω →
      (coordS xL xR G W VL VR t ω, Sec2.TwoSeed.brownG G B t ω) ∈ stripKc κ xL xR ρL ρR n := by
    intro ω t ht
    by_cases hω : ω ∈ G
    · simpa only [coordS, Sec2.TwoSeed.brownG, hω, ↓reduceIte] using
        mem_stripKc_of_le_stripLoc (hgood ω hω) hω hgood ht
    · simp only [coordS, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
      exact mem_insert _ _
  have hM := Ito.martingale_itoLocalized hB' (continuous_brownG_strip hgood)
    (isOpen_stripMartRegion κ xL xR ρL ρR) hF (isCompact_stripKc κ xL xR ρL ρR n)
    (stripKc_subset_region κ xL xR ρL ρR h0 n) (isStoppingTime_stripLoc hE hGm hGc hgood n)
    (measurable_coordS_stopped hE hGm hGc hgood n) hlam hΛ hKb hK
  have hzero : ∀ (t : ℝ≥0) ω, ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0),
      Ito.itoGen F (coordS xL xR G W VL VR s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω)
        (densS G W VL VR s ω) = 0 := by
    intro t ω
    by_cases hω : ω ∈ G
    · simp only [coordS, densS, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
      refine intervalIntegral.integral_zero_ae ?_
      filter_upwards [hgen ω hω n] with s hs hsI
      rw [uIoc_of_le (min t (σ ω)).coe_nonneg] at hsI
      exact hs ⟨hsI.1, hsI.2.trans (by exact_mod_cast min_le_right t (σ ω))⟩
    · have h0' : σ ω = 0 := stripLoc_of_not_mem hω n
      rw [h0', min_eq_right (zero_le (a := t)), NNReal.coe_zero, intervalIntegral.integral_same]
  have e : (fun t ω => F (coordS xL xR G W VL VR (min t (σ ω)) ω,
      Sec2.TwoSeed.brownG G B (min t (σ ω)) ω) -
      ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0), Ito.itoGen F (coordS xL xR G W VL VR s.toNNReal ω,
        Sec2.TwoSeed.brownG G B s.toNNReal ω) (densS G W VL VR s ω)) =
      fun t ω => F (coordS xL xR G W VL VR (min t (σ ω)) ω,
        Sec2.TwoSeed.brownG G B (min t (σ ω)) ω) := by
    funext t ω; rw [hzero t ω, sub_zero]
  rw [e] at hM
  exact hM

include hE hGm hGc hgood in
/-- **The strip martingale** `Φ` stopped at `σ_n` is a martingale of the usual augmentation. -/
theorem martingale_stripMartObs (hκ : 0 ≤ κ) (h0 : stripInit xL xR ∈ stripMartRegion κ xL xR ρL ρR) (n : ℕ) :
    Martingale (fun t ω => stripMartObs κ xL xR ρL ρR
      (coordS xL xR G W VL VR (min t (stripLoc G W VL VR B ζ n ω)) ω,
        Sec2.TwoSeed.brownG G B (min t (stripLoc G W VL VR B ζ n ω)) ω))
      (usualAugmentation 𝓕 P) P := by
  refine martingale_obs_stopped hE hGm hGc hgood h0 (contDiffOn_stripMartObs κ xL xR ρL ρR)
    (fun ω hω m => ?_) n
  have hω' := hgood ω hω
  have hlife := isStripLife_stripLoc hω' hω (n := m)
  have h := ae_itoGen_stripMartObs_eq_zero hω'.1 hκ hlife.1 fun s hs =>
    stripKc_subset_region κ xL xR ρL ρR h0 m (mem_stripKc_of_le_stripLoc hω' hω hgood hs)
  exact h

include hE hGm hGc hgood in
/-- **Its bracket**: `Φ² − κ t(s)` stopped at `σ_n` is a martingale of the usual augmentation. -/
theorem martingale_stripMartObs2 (hκ : 0 ≤ κ) (h0 : stripInit xL xR ∈ stripMartRegion κ xL xR ρL ρR) (n : ℕ) :
    Martingale (fun t ω => stripMartObs2 κ xL xR ρL ρR
      (coordS xL xR G W VL VR (min t (stripLoc G W VL VR B ζ n ω)) ω,
        Sec2.TwoSeed.brownG G B (min t (stripLoc G W VL VR B ζ n ω)) ω))
      (usualAugmentation 𝓕 P) P := by
  refine martingale_obs_stopped hE hGm hGc hgood h0 (contDiffOn_stripMartObs2 κ xL xR ρL ρR)
    (fun ω hω m => ?_) n
  have hω' := hgood ω hω
  have hlife := isStripLife_stripLoc hω' hω (n := m)
  have h := ae_itoGen_stripMartObs2_eq_zero hω'.1 hκ hlife.1 fun s hs =>
    stripKc_subset_region κ xL xR ρL ρR h0 m (mem_stripKc_of_le_stripLoc hω' hω hgood hs)
  exact h

end Adapted

end Zhan

end InteractingSLE
