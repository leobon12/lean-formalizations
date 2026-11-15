/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G12LowObs
import InteractingSLE.Spec.Supplement.G12Core
import InteractingSLE.Spec.Supplement.Aux62Evol

/-!
# Lemma G12 when the weight before the mark is `≤ −2`: the localized Itô formula below `σ_n`

Packet PROVE-G12C. PROVE-G12's localized Itô formula (`G12Loc.martingale_locG`) is stated at its own localizing
times `σ_n = locG n` and for functions smooth on the region of its mark observable. The Lyapunov observable of
`G12LowObs.lean` is smooth on another region (`o > 0, e > 0`), and the expectation argument stops earlier (at the first
time `o` is small, at the separation time of the monitored marks after the restart time, and when the drift energy is
large). This file proves the localized Itô formula **for every stopping time `σ ≤ locG n`** and every `C³` function on
an open set containing a compact set that holds the coordinates up to `σ` (`martingale_of_le_locG`), with the
adaptedness lemmas it needs (`measurable_coordG_of_le`), and the integrability of the generator of the Lyapunov
observable along the path (`intervalIntegrable_itoGen_lowObs`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp7

namespace G12Low

open G12 (GCoord gDriftLin gDriftLin₀ g12Dens coordG densG gapStopG locG kbG coordAtG densAtG clockAt kcG)
open Supp8.GB5 (IsGBGood isFilteredBrownianReal_brownG_gb continuous_brownG_gb measurableSet_good_usual'
  abs_le_norm_state)

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {j₀ : Fin nR}
  {G : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} {n : ℕ} {σ : Ω → ℝ≥0}

section General

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsGBGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (T n ω : WithTop ℝ≥0))
  (hTn : ∀ n ω, T n ω ≤ n) (hy : 0 < xR j₀)
  (hσ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0))
  (hσle : ∀ ω, σ ω ≤ locG xR j₀ G W VL VR B ζ T n ω)

include hgood hσle in
theorem lt_zeta_of_le {ω : Ω} (hω : ω ∈ G) {s : ℝ≥0} (hs : s ≤ σ ω) : (s : ℝ≥0∞) < ζ ω :=
  lt_of_le_of_lt (by exact_mod_cast hs.trans (hσle ω)) (G12.locG_lt_lifetime (hgood ω hω))

include hE hGm hGc hgood hσ hσle in
/-- The gap stopped at `σ` is adapted. -/
theorem measurable_gapStopG_of_le (r : ℝ≥0) :
    Measurable[usualAugmentation 𝓕 P r] (gapStopG G W VR j₀ σ r) := by
  obtain ⟨-, hWa, -, hVRa, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hG0 := measurableSet_good_usual' (𝓕 := 𝓕) hGm hGc 0
  have hK : ∀ s, Measurable[usualAugmentation 𝓕 P s] fun ω =>
      Zhan.killedAt ζ (VR j₀) s ω - Zhan.killedAt ζ W s ω := fun s =>
    (Sec2.TwoSeed.measurable_killed (hVRa j₀) s).sub (Sec2.TwoSeed.measurable_killed hWa s)
  have h := Ito.measurable_stopped_of_agree (X := fun s ω => VR j₀ s ω - W s ω) hσ hK hG0
    (1 : ℝ) (fun ω hω s hs => ?_) (fun ω hω => ?_) r
  · exact h
  · have hsζ := lt_zeta_of_le hgood hσle hω hs
    simp only [Zhan.killedAt, hsζ, ↓reduceIte]
  · have hF := (hgood ω hω).1.isForcePath
    have hsub : Iic (σ ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs => lt_zeta_of_le hgood hσle hω hs
    exact ((hF.continuousOn_vR j₀).sub hF.continuousOn_w).mono hsub

include hgood hσle in
theorem continuous_gapStopG_of_le (ω : Ω) : Continuous fun r => gapStopG G W VR j₀ σ r ω := by
  by_cases hω : ω ∈ G
  · have hF := (hgood ω hω).1.isForcePath
    have hsub : Iic (σ ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs => lt_zeta_of_le hgood hσle hω hs
    have hc := ((hF.continuousOn_vR j₀).sub hF.continuousOn_w).mono hsub
    simp only [gapStopG, hω, ↓reduceIte]
    exact hc.comp_continuous (continuous_id.min continuous_const) fun r => mem_Iic.2 (min_le_right _ _)
  · simp only [gapStopG, hω, ↓reduceIte]; exact continuous_const

include hgood hσle hy in
theorem isMarkLife_of_le {ω : Ω} (hω : ω ∈ G) :
    G11.IsMarkLife (W · ω) (VR j₀ · ω) (ζ ω) (σ ω) :=
  G12.isMarkLife_mono (G12.isMarkLife_locG (hgood ω hω) hω hy (n := n)) (hσle ω)

include hE hGm hGc hgood hσ hσle hy in
/-- **The coordinates stopped at `σ` are adapted.** -/
theorem measurable_coordG_of_le (t : ℝ≥0) :
    Measurable[usualAugmentation 𝓕 P t] fun ω => coordG xL xR G W VL VR j₀ (min t (σ ω)) ω := by
  obtain ⟨-, -, hVLa, hVRa, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  set 𝓖 := usualAugmentation 𝓕 P
  have hG0 := measurableSet_good_usual' (𝓕 := 𝓕) hGm hGc 0
  have hprog : IsStronglyProgressive 𝓖 (gapStopG G W VR j₀ σ) :=
    StronglyAdapted.isStronglyProgressive_of_continuous
      (fun r => (measurable_gapStopG_of_le hE hGm hGc hgood hσ hσle r).stronglyMeasurable)
      (continuous_gapStopG_of_le hgood hσle)
  set K : ℝ≥0 → Ω → GCoord nL nR := fun s ω => ((fun i => Zhan.killedAt ζ (VL i) s ω),
    (fun j => Zhan.killedAt ζ (VR j) s ω), ∫ u in (0 : ℝ)..s, ((gapStopG G W VR j₀ σ u.toNNReal ω) ^ 2)⁻¹)
    with hKdef
  have hK : ∀ s, Measurable[𝓖 s] (K s) := fun s => by
    refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
    · exact @Measurable.of_eval Ω (Fin nL) (fun _ => ℝ) (𝓖 s) _ _ fun i =>
        Sec2.TwoSeed.measurable_killed (hVLa i) s
    · exact @Measurable.of_eval Ω (Fin nR) (fun _ => ℝ) (𝓖 s) _ _ fun j =>
        Sec2.TwoSeed.measurable_killed (hVRa j) s
    · exact (Girsanov.stronglyMeasurable_integral_comp hprog
        (g := fun x : ℝ => (x ^ 2)⁻¹) (by fun_prop) s).measurable
  have h := Ito.measurable_stopped_of_agree
    (X := fun s ω => coordAtG (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) j₀ s) hσ hK hG0
    ((xL, xR, 0) : GCoord nL nR) (fun ω hω s hs => ?_) (fun ω hω => ?_) t
  · convert h using 2 with ω
    by_cases hω : ω ∈ G <;> simp [coordG, hω]
  · have hsζ := lt_zeta_of_le hgood hσle hω hs
    refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun j => ?_) ?_)
    · simp only [hKdef, Zhan.killedAt, hsζ, ↓reduceIte, coordAtG]
    · simp only [hKdef, Zhan.killedAt, hsζ, ↓reduceIte, coordAtG]
    · simp only [hKdef, coordAtG, clockAt]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le s.coe_nonneg] at hu
      have hus : u.toNNReal ≤ σ ω := (Sec2.toNNReal_le_of_mem_Icc hu).trans hs
      simp only [gapStopG, hω, ↓reduceIte, min_eq_left hus]
  · have hF := (hgood ω hω).1.isForcePath
    have hlife := isMarkLife_of_le hgood hy hσle (n := n) hω
    have hTc : ContinuousOn (fun s : ℝ≥0 => clockAt (W · ω) (VR j₀ · ω) s) (Iic (σ ω)) := by
      have hc := intervalIntegral.continuousOn_primitive_interval'
        (G12.intervalIntegrable_clockRate hF hlife) (left_mem_uIcc (a := (0 : ℝ)) (b := σ ω))
      refine hc.comp NNReal.continuous_coe.continuousOn fun s hs => ?_
      rw [uIcc_of_le (σ ω).coe_nonneg]
      exact ⟨s.coe_nonneg, by exact_mod_cast hs⟩
    have hsub : Iic (σ ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs => (G12.isMarkLife_mono hlife hs).1
    exact (continuousOn_pi.2 fun i => (hF.continuousOn_vL i).mono hsub).prodMk
      ((continuousOn_pi.2 fun j => (hF.continuousOn_vR j).mono hsub).prodMk hTc)

include hE hGm hGc hgood hTn hy hσ hσle in
/-- **The localized Itô formula at a stopping time `σ ≤ σ_n`**, for a `C³` function `F` on an open set `U`
containing a compact set `Kc` that holds the coordinates up to `σ`. -/
theorem martingale_of_le_locG {U : Set (GCoord nL nR × ℝ)} (hU : IsOpen U) {F : GCoord nL nR × ℝ → ℝ}
    (hF : ContDiffOn ℝ 3 F U) {Kc : Set (GCoord nL nR × ℝ)} (hKc : IsCompact Kc) (hKU : Kc ⊆ U)
    (hK : ∀ ω (t : ℝ≥0), t ≤ σ ω →
      (coordG xL xR G W VL VR j₀ t ω, Sec2.TwoSeed.brownG G B t ω) ∈ Kc) :
    Martingale (fun t ω => F (coordG xL xR G W VL VR j₀ (min t (σ ω)) ω,
          Sec2.TwoSeed.brownG G B (min t (σ ω)) ω) -
      ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0),
        Ito.itoGen F (coordG xL xR G W VL VR j₀ s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω)
          (densG G W VL VR j₀ s ω)) (usualAugmentation 𝓕 P) P := by
  have hB' := isFilteredBrownianReal_brownG_gb hE hGm hGc hgood
  have hlam : ∀ ω, IntervalIntegrable (densG G W VL VR j₀ · ω) volume 0 (σ ω) := fun ω => by
    by_cases hω : ω ∈ G
    · simpa only [densG, hω, ↓reduceIte] using
        G12.intervalIntegrable_densAtG (hgood ω hω).1.isForcePath (isMarkLife_of_le hgood hy hσle (n := n) hω)
    · simp only [densG, hω, ↓reduceIte]; exact intervalIntegrable_const
  have hΛ : ∀ ω (t : ℝ≥0), t ≤ σ ω → coordG xL xR G W VL VR j₀ t ω =
      coordG xL xR G W VL VR j₀ 0 ω + ∫ s in (0 : ℝ)..t, densG G W VL VR j₀ s ω := by
    intro ω t ht
    by_cases hω : ω ∈ G
    · simp only [coordG, densG, hω, ↓reduceIte]
      exact G12.coordAtG_eq_add_integral (hgood ω hω).1.isForcePath
        (G12.isMarkLife_mono (isMarkLife_of_le hgood hy hσle (n := n) hω) ht)
    · simp only [coordG, densG, hω, ↓reduceIte, intervalIntegral.integral_zero, add_zero]
  have hKb : ∀ ω, ∫ s in (0 : ℝ)..(σ ω), ‖densG G W VL VR j₀ s ω‖ ≤ kbG xL xR n := by
    intro ω
    by_cases hω : ω ∈ G
    · simp only [densG, hω, ↓reduceIte]
      have hgω := hgood ω hω
      have hF := hgω.1.isForcePath
      have hlife := isMarkLife_of_le hgood hy hσle (n := n) hω
      refine (G12.integral_norm_densAtG_le hF hlife).trans ?_
      rcases (zero_le (a := σ ω)).eq_or_lt with h0 | h0
      · rw [← h0]
        simp only [hF.vL_zero, hF.vR_zero, sub_self, sum_const_zero, clockAt, NNReal.coe_zero,
          intervalIntegral.integral_same, add_zero]
        exact G12.kbG_nonneg xL xR n
      have h0' : 0 < locG xR j₀ G W VL VR B ζ T n ω := h0.trans_le (hσle ω)
      have hlev := G12.levG_nonneg_iff.1 (G12.levG_nonneg_of_le_locG hgω hω h0' (hσle ω))
      have hn : ‖Coupling.stateAt W VL VR (σ ω) ω‖ ≤ n := hlev.2.1
      obtain ⟨-, hvL, hvR⟩ := abs_le_norm_state (Coupling.stateAt W VL VR (σ ω) ω)
      simp only [Coupling.stateAt] at hvL hvR
      have hcl := (G12.clockAt_le_of_le_locG hgood hTn hy hω (n := n) (hσle ω)).2
      have hLi : ∀ i, xL i - VL i (σ ω) ω ≤ ‖xL‖ + n := fun i => by
        have h1 : |xL i| ≤ ‖xL‖ := by
          rw [← Real.norm_eq_abs]; exact norm_le_pi_norm xL i
        linarith [le_abs_self (xL i), neg_abs_le (VL i (σ ω) ω), (hvL i).trans hn]
      have hRj : ∀ j, VR j (σ ω) ω - xR j ≤ ‖xR‖ + n := fun j => by
        have h1 : |xR j| ≤ ‖xR‖ := by
          rw [← Real.norm_eq_abs]; exact norm_le_pi_norm xR j
        linarith [le_abs_self (VR j (σ ω) ω), neg_abs_le (xR j), (hvR j).trans hn]
      have hsL : ∑ i, (xL i - VL i (σ ω) ω) ≤ (nL : ℝ) * (‖xL‖ + n) := by
        calc ∑ i, (xL i - VL i (σ ω) ω) ≤ ∑ _i : Fin nL, (‖xL‖ + n) :=
            Finset.sum_le_sum fun i _ => hLi i
          _ = _ := by simp; ring
      have hsR : ∑ j, (VR j (σ ω) ω - xR j) ≤ (nR : ℝ) * (‖xR‖ + n) := by
        calc ∑ j, (VR j (σ ω) ω - xR j) ≤ ∑ _j : Fin nR, (‖xR‖ + n) :=
            Finset.sum_le_sum fun j _ => hRj j
          _ = _ := by simp; ring
      unfold kbG
      linarith
    · simp only [densG, hω, ↓reduceIte, norm_zero, intervalIntegral.integral_zero]
      exact G12.kbG_nonneg xL xR n
  have hBm : ∀ t, Measurable[usualAugmentation 𝓕 P t] fun ω =>
      Sec2.TwoSeed.brownG G B (min t (σ ω)) ω := fun t => by
    have hG0 := measurableSet_good_usual' (𝓕 := 𝓕) hGm hGc 0
    have h := Ito.measurable_stopped_of_agree (X := Sec2.TwoSeed.brownG G B) hσ hB'.2.1 hG0 (0 : ℝ)
      (fun ω _ s _ => rfl) (fun ω _ => (continuous_brownG_gb hgood ω).continuousOn) t
    convert h using 2 with ω
    by_cases hω : ω ∈ G <;> simp [Sec2.TwoSeed.brownG, hω]
  exact Ito.martingale_itoLocalized hB' (continuous_brownG_gb hgood) hU hF hKc hKU hσ
    (measurable_coordG_of_le hE hGm hGc hgood hy hσ hσle) hlam hΛ hKb hK

end General

/-! ### The stopping times of the expectation argument -/

section Stops

open GB7a Girsanov

open scoped Classical in
/-- The lifetime on the good event (`0` off it). -/
def goodLife (G : Set Ω) (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ := if ω ∈ G then ζ ω else 0

/-- The actual weights on the concatenated marks `allMarks VL VR` (left marks first). -/
def actW (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Fin (nL + nR) → ℝ := Fin.append ρL ρR

/-- The reference weights on the concatenated marks: `0` on the left, `lowRefW` on the right. -/
def refW (nL : ℕ) (xR ρR : Fin nR → ℝ) (k j₀ : Fin nR) (S : ℝ) : Fin (nL + nR) → ℝ :=
  Fin.append (fun _ : Fin nL => (0 : ℝ)) (lowRefW xR ρR k j₀ S)

/-- The level `δ'_n = min(1/(n+1), x_k)` of the inner gap. -/
def lowDelta (xR : Fin nR → ℝ) (k : Fin nR) (n : ℕ) : ℝ := min (G12.dlt n) (xR k)

/-- **The separation time** after `q` at level `δ_n = 1/(n+1)` with horizon `n`: the first time after `q` that a
monitored mark (nonzero actual or reference weight, or `k`) comes `δ_n`-close to the driver. -/
def lowSep (ρL : Fin nL → ℝ) (xR ρR : Fin nR → ℝ) (k j₀ : Fin nR) (S : ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (q : ℝ≥0) (n : ℕ) :
    Ω → ℝ≥0∞ :=
  sepTime (actW ρL ρR) (refW nL xR ρR k j₀ S) (Fin.natAdd nL k) q (G12.dlt n) W (Girsanov.allMarks VL VR)
    (goodLife G ζ) n

/-- **The cut drift difference** (actual word minus reference, divided by `√κ`) between `q` and the separation
time. -/
def lowTheta (κ : ℝ) (ρL : Fin nL → ℝ) (xR ρR : Fin nR → ℝ) (k j₀ : Fin nR) (S : ℝ) (G : Set Ω)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (q : ℝ≥0)
    (n : ℕ) : ℝ≥0 → Ω → ℝ :=
  cmpDrift κ (G12.dlt n) (fun j => refW nL xR ρR k j₀ S j - actW ρL ρR j)
    (lowSep ρL xR ρR k j₀ S G W VL VR ζ q n) (goodLife G ζ) q W (Girsanov.allMarks VL VR)

/-- **The drift energy** `∫₀ᵗ θ²`. -/
def lowEnergy (κ : ℝ) (ρL : Fin nL → ℝ) (xR ρR : Fin nR → ℝ) (k j₀ : Fin nR) (S : ℝ) (G : Set Ω)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (q : ℝ≥0)
    (n : ℕ) : ℝ≥0 → Ω → ℝ :=
  quadInt (lowTheta κ ρL xR ρR k j₀ S G W VL VR ζ q n)

open scoped Classical in
/-- The first time the inner gap `o = V^k − W` falls below `δ`, on the good event (`0` off it). -/
def lowOStop (k : Fin nR) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (δ : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  if ω ∈ G then Coupling.hitBelow (fun s => (Coupling.stateAt W VL VR s ω).2.2 k -
    (Coupling.stateAt W VL VR s ω).1 - δ) (ζ ω) 0 else 0

/-- **The stopping time of the expectation argument**: `σ_n` of PROVE-G12, the first time the inner gap is below
`δ'_n`, the separation time, and the exit of the energy from `[0, C + 1)`. -/
def lowStop (κ : ℝ) (ρL : Fin nL → ℝ) (xR ρR : Fin nR → ℝ) (k j₀ : Fin nR) (S : ℝ) (G : Set Ω)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (T : ℕ → Ω → ℝ≥0) (q : ℝ≥0) (C n : ℕ) (ω : Ω) : ℝ≥0 :=
  Sec2.TwoSeed.capTime (locG xR j₀ G W VL VR B ζ T n)
    (fun ω => min (lowOStop k G W VL VR ζ (lowDelta xR k n) ω)
      (min (lowSep ρL xR ρR k j₀ S G W VL VR ζ q n ω : WithTop ℝ≥0)
        (MathFin.exitTime (lowEnergy κ ρL xR ρR k j₀ S G W VL VR ζ q n) (C + 1) ω))) ω

variable {k : Fin nR} {S : ℝ} {q : ℝ≥0} {C : ℕ}

theorem allMarks_castAdd' (i : Fin nL) : Girsanov.allMarks VL VR (Fin.castAdd nR i) = VL i := by
  simp [Girsanov.allMarks]

theorem allMarks_natAdd' (j : Fin nR) : Girsanov.allMarks VL VR (Fin.natAdd nL j) = VR j := by
  simp [Girsanov.allMarks]

section Adapted

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsGBGood κ xL xR ρL ρR W VL VR B ζ T ω)

include hE hGm hGc in
theorem adaptedBefore_goodLife_W : AdaptedBefore (usualAugmentation 𝓕 P) (goodLife G ζ) W := by
  classical
  obtain ⟨-, hWa, -, -, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  exact adaptedBefore_ite_lifetime hWa (measurableSet_good_usual' (𝓕 := 𝓕) hGm hGc 0)

include hE hGm hGc in
theorem adaptedBefore_goodLife_marks (j : Fin (nL + nR)) :
    AdaptedBefore (usualAugmentation 𝓕 P) (goodLife G ζ) (Girsanov.allMarks VL VR j) := by
  classical
  obtain ⟨-, -, hVLa, hVRa, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hG0 := measurableSet_good_usual' (𝓕 := 𝓕) hGm hGc 0
  cases j using Fin.addCases with
  | left i => rw [allMarks_castAdd']; exact adaptedBefore_ite_lifetime (hVLa i) hG0
  | right i => rw [allMarks_natAdd']; exact adaptedBefore_ite_lifetime (hVRa i) hG0

include hgood in
theorem continuousOn_goodLife_W (ω : Ω) : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < goodLife G ζ ω} := by
  classical
  exact continuousOn_ite_lifetime fun hω => (hgood ω hω).1.isForcePath.continuousOn_w

include hgood in
theorem continuousOn_goodLife_marks (j : Fin (nL + nR)) (ω : Ω) :
    ContinuousOn (Girsanov.allMarks VL VR j · ω) {t | (t : ℝ≥0∞) < goodLife G ζ ω} := by
  classical
  cases j using Fin.addCases with
  | left i =>
    rw [allMarks_castAdd']
    exact continuousOn_ite_lifetime fun hω => (hgood ω hω).1.isForcePath.continuousOn_vL i
  | right i =>
    rw [allMarks_natAdd']
    exact continuousOn_ite_lifetime fun hω => (hgood ω hω).1.isForcePath.continuousOn_vR i

include hE hGm hGc hgood in
theorem measurableSet_lowSep_le (s : ℝ≥0) :
    MeasurableSet[usualAugmentation 𝓕 P s] {ω | lowSep ρL xR ρR k j₀ S G W VL VR ζ q n ω ≤ s} :=
  measurableSet_sepTime_le (G12.dlt_pos n).le (adaptedBefore_goodLife_W hE hGm hGc)
    (adaptedBefore_goodLife_marks hE hGm hGc) (continuousOn_goodLife_W hgood)
    (fun j ω => continuousOn_goodLife_marks hgood j ω) s

include hE hGm hGc hgood in
theorem isStoppingTime_lowSep :
    IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (lowSep ρL xR ρR k j₀ S G W VL VR ζ q n ω : WithTop ℝ≥0) :=
  fun s => measurableSet_lowSep_le hE hGm hGc hgood s

include hE hGm hGc hgood in
theorem isStronglyProgressive_lowTheta :
    IsStronglyProgressive (usualAugmentation 𝓕 P) (lowTheta κ ρL xR ρR k j₀ S G W VL VR ζ q n) :=
  isStronglyProgressive_cmpDrift (G12.dlt_pos n) (adaptedBefore_goodLife_W hE hGm hGc)
    (adaptedBefore_goodLife_marks hE hGm hGc) (measurableSet_lowSep_le hE hGm hGc hgood)

theorem abs_lowTheta_le (t : ℝ≥0) (ω : Ω) :
    |lowTheta κ ρL xR ρR k j₀ S G W VL VR ζ q n t ω| ≤
      cmpBound κ (G12.dlt n) (fun j => refW nL xR ρR k j₀ S j - actW ρL ρR j) :=
  abs_cmpDrift_le (G12.dlt_pos n) t ω

include hE hGm hGc hgood in
theorem continuous_lowEnergy (ω : Ω) :
    Continuous fun t => lowEnergy κ ρL xR ρR k j₀ S G W VL VR ζ q n t ω := by
  have hθ := isStronglyProgressive_lowTheta (κ := κ) (k := k) (j₀ := j₀) (S := S) (q := q) (n := n)
    hE hGm hGc hgood
  have hθ2 : IsStronglyProgressive (usualAugmentation 𝓕 P)
      (fun t ω => lowTheta κ ρL xR ρR k j₀ S G W VL VR ζ q n t ω ^ 2) := fun t => (hθ t).pow 2
  have hb : ∀ t ω, |lowTheta κ ρL xR ρR k j₀ S G W VL VR ζ q n t ω ^ 2| ≤
      cmpBound κ (G12.dlt n) (fun j => refW nL xR ρR k j₀ S j - actW ρL ρR j) ^ 2 := fun t ω => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_lowTheta_le t ω) 2
  exact continuous_drift hθ2 hb ω

include hE hGm hGc hgood in
theorem measurable_lowEnergy (t : ℝ≥0) :
    Measurable[usualAugmentation 𝓕 P t] (lowEnergy κ ρL xR ρR k j₀ S G W VL VR ζ q n t) :=
  (stronglyMeasurable_integral_comp (isStronglyProgressive_lowTheta hE hGm hGc hgood)
    (measurable_id.pow_const 2) t).measurable

include hE hGm hGc hgood in
theorem isStoppingTime_lowOStop (δ : ℝ) :
    IsStoppingTime (usualAugmentation 𝓕 P) (lowOStop k G W VL VR ζ δ) := by
  classical
  exact Supp8.GB5.isStoppingTime_hit_gb hE hGm hGc hgood
    (Φ := fun st : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => st.2.2 k - st.1 - δ) (by fun_prop)

include hE hGm hGc hgood in
theorem isStoppingTime_lowStop (hT : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (T n ω : WithTop ℝ≥0)) :
    IsStoppingTime (usualAugmentation 𝓕 P)
      fun ω => (lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω : WithTop ℝ≥0) :=
  Sec2.TwoSeed.isStoppingTime_capTime (G12.isStoppingTime_locG hE hGm hGc hgood hT)
    ((isStoppingTime_lowOStop hE hGm hGc hgood _).min ((isStoppingTime_lowSep hE hGm hGc hgood).min
      (MathFin.isStoppingTime_exitTime_of_measurable (measurable_lowEnergy hE hGm hGc hgood)
        (continuous_lowEnergy hE hGm hGc hgood) (C + 1))))

end Adapted

theorem lowStop_le_locG (ω : Ω) :
    lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω ≤ locG xR j₀ G W VL VR B ζ T n ω :=
  Sec2.TwoSeed.capTime_le _ _ ω

theorem lowStop_le_right (ω : Ω) :
    (lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω : WithTop ℝ≥0) ≤
      min (lowOStop k G W VL VR ζ (lowDelta xR k n) ω)
        (min (lowSep ρL xR ρR k j₀ S G W VL VR ζ q n ω : WithTop ℝ≥0)
          (MathFin.exitTime (lowEnergy κ ρL xR ρR k j₀ S G W VL VR ζ q n) (C + 1) ω)) :=
  Sec2.TwoSeed.capTime_le_right _ _ ω

theorem lowStop_le_sep (ω : Ω) :
    (lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω : WithTop ℝ≥0) ≤
      (lowSep ρL xR ρR k j₀ S G W VL VR ζ q n ω : WithTop ℝ≥0) :=
  le_trans (lowStop_le_right ω) (le_trans (min_le_right _ _) (min_le_left _ _))

theorem lowStop_le_energy (ω : Ω) :
    (lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω : WithTop ℝ≥0) ≤
      MathFin.exitTime (lowEnergy κ ρL xR ρR k j₀ S G W VL VR ζ q n) (C + 1) ω :=
  le_trans (lowStop_le_right ω) (le_trans (min_le_right _ _) (min_le_right _ _))

theorem lowStop_le_oStop (ω : Ω) :
    (lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω : WithTop ℝ≥0) ≤
      lowOStop k G W VL VR ζ (lowDelta xR k n) ω :=
  le_trans (lowStop_le_right ω) (min_le_left _ _)

theorem lowStop_le_horizon (ω : Ω) : lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω ≤ n := by
  have h1 := lowStop_le_sep (κ := κ) (ρL := ρL) (xR := xR) (ρR := ρR) (k := k) (j₀ := j₀) (S := S) (G := G)
    (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) (T := T) (q := q) (C := C) (n := n) ω
  have h2 : (lowSep ρL xR ρR k j₀ S G W VL VR ζ q n ω : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0) :=
    sepTime_le_horizon ω
  exact WithTop.coe_le_coe.1 (h1.trans h2)

end Stops

end G12Low

end Supp7

end InteractingSLE
