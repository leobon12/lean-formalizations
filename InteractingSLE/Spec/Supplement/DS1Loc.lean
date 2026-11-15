/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS1Drift
import InteractingSLE.Spec.Supplement.GB5Loc

/-!
# Lemma DS1: localization and the localized Itô formula

Packet PROVE-T14-TIP (specification supplement §12, **Lemma DS1**, `source/spec/p529-576.md` L523–L575, pp. 551–553):
"Stop also at the usual coordinate bounds and remove them by localization. The martingale has mean zero at the
bounded time stop".

For an integrated `SLE_κ(ρ)` evolution, the observable `obs κ p ν r` of `DS1Fun.lean` of the Itô coordinate
`Λ = X₁ + √κ B` (GB5's coordinates `coordAt κ 0 0`, whose second component is `0`) is localized at

  `σ_n = T_n ∧ (first time ‖state‖ > n or the first far gap on either side is below g) ∧ (exit of |B| from (−n, n))`

(`loc`), where `T_n` announces the lifetime. `martingale_obs` is the localized Itô formula
(`Ito.martingale_itoLocalized`).
The good-path predicate and the hitting-time stopping lemmas are GB5's (`Supp8.GB5.IsGBGood`, `isStoppingTime_hit_gb`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp12

namespace DS1

open Supp8.GB5

variable {nL nR : ℕ}

/-! ### The functionals of the stop -/

/-- The first designated far right gap minus `g` (`1` if there is none). -/
def farR (mR : ℕ) (g : ℝ) (st : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : ℝ :=
  if h : mR < nR then st.2.2 ⟨mR, h⟩ - st.1 - g else 1

/-- The first designated far left gap minus `g` (`1` if there is none). -/
def farL (mL : ℕ) (g : ℝ) (st : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : ℝ :=
  if h : mL < nL then st.1 - st.2.1 ⟨mL, h⟩ - g else 1

/-- The localization level: the state stays in the ball of radius `n` and both far gaps stay at least `g`. -/
def lev (mL mR n : ℕ) (g : ℝ) (st : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : ℝ :=
  min ((n : ℝ) - ‖st‖) (min (farR mR g st) (farL mL g st))

theorem continuous_farR (mR : ℕ) (g : ℝ) : Continuous (farR (nL := nL) (nR := nR) mR g) := by
  unfold farR
  by_cases h : mR < nR
  · simp only [h, ↓reduceDIte]; fun_prop
  · simp only [h, ↓reduceDIte]; exact continuous_const

theorem continuous_farL (mL : ℕ) (g : ℝ) : Continuous (farL (nL := nL) (nR := nR) mL g) := by
  unfold farL
  by_cases h : mL < nL
  · simp only [h, ↓reduceDIte]; fun_prop
  · simp only [h, ↓reduceDIte]; exact continuous_const

theorem continuous_lev (mL mR n : ℕ) (g : ℝ) : Continuous (lev (nL := nL) (nR := nR) mL mR n g) :=
  (continuous_const.sub continuous_norm).min ((continuous_farR mR g).min (continuous_farL mL g))

/-! ### The localizing times -/

section Loc

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

open scoped Classical in
/-- The first failure of the localization level, on the good event (`0` off it). -/
def hitD (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (mL mR n : ℕ) (g : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  if ω ∈ G then Coupling.hitBelow (fun s => lev mL mR n g (Coupling.stateAt W VL VR s ω)) (ζ ω) 0 else 0

/-- **The localizing time** `σ_n = T_n ∧ hitD ∧ (exit of |B| from (−n, n))`. -/
def loc (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (T : ℕ → Ω → ℝ≥0) (mL mR n : ℕ) (g : ℝ) (ω : Ω) : ℝ≥0 :=
  Sec2.TwoSeed.capTime (T n) (fun ω => min (hitD G W VL VR ζ mL mR n g ω)
    (MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω)) ω

variable {G : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} {mL mR n : ℕ} {g : ℝ}

theorem loc_le_T (ω : Ω) : loc G W VL VR B ζ T mL mR n g ω ≤ T n ω :=
  Sec2.TwoSeed.capTime_le _ _ ω

theorem loc_le_hitD (ω : Ω) :
    (loc G W VL VR B ζ T mL mR n g ω : WithTop ℝ≥0) ≤ hitD G W VL VR ζ mL mR n g ω :=
  (Sec2.TwoSeed.capTime_le_right _ _ ω).trans (min_le_left _ _)

theorem loc_le_exitTime (ω : Ω) :
    (loc G W VL VR B ζ T mL mR n g ω : WithTop ℝ≥0) ≤ MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω :=
  (Sec2.TwoSeed.capTime_le_right _ _ ω).trans (min_le_right _ _)

theorem loc_lt_lifetime {k : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {ω : Ω} (hω : IsGBGood k xL xR ρL ρR W VL VR B ζ T ω) :
    (loc G W VL VR B ζ T mL mR n g ω : ℝ≥0∞) < ζ ω :=
  lt_of_le_of_lt (by exact_mod_cast loc_le_T ω) (hω.2.2.2.1 n)

theorem lev_nonneg_of_le_loc {k : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {ω : Ω} (hω : IsGBGood k xL xR ρL ρR W VL VR B ζ T ω) (hωG : ω ∈ G)
    (hσ0 : 0 < loc G W VL VR B ζ T mL mR n g ω) {r : ℝ≥0} (hr : r ≤ loc G W VL VR B ζ T mL mR n g ω) :
    0 ≤ lev mL mR n g (Coupling.stateAt W VL VR r ω) := by
  have h := loc_le_hitD (G := G) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) (T := T) (mL := mL)
    (mR := mR) (n := n) (g := g) ω
  simp only [hitD, hωG, ↓reduceIte] at h
  have hF := hω.1.isForcePath
  exact nonneg_of_le_hitBelow ((continuous_lev mL mR n g).comp_continuousOn
    (hF.continuousOn_w.prodMk ((continuousOn_pi.2 hF.continuousOn_vL).prodMk
      (continuousOn_pi.2 hF.continuousOn_vR)))) (loc_lt_lifetime hω) h hσ0 hr

theorem abs_B_le_of_le_loc {k : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hgood : ∀ ω ∈ G, IsGBGood k xL xR ρL ρR W VL VR B ζ T ω) {ω : Ω} (hωG : ω ∈ G)
    {r : ℝ≥0} (hr : r ≤ loc G W VL VR B ζ T mL mR n g ω) : |B r ω| ≤ n := by
  rcases (zero_le (a := r)).eq_or_lt with h0 | h0
  · rw [← h0, (hgood ω hωG).2.2.1, abs_zero]; exact Nat.cast_nonneg n
  have h := MathFin.abs_le_N_of_le_exitTime (continuous_brownG_gb hgood) h0
    ((WithTop.coe_le_coe.2 hr).trans (loc_le_exitTime ω))
  simpa only [Sec2.TwoSeed.brownG, hωG, ↓reduceIte] using h

end Loc

section StoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {k : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {G : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} {mL mR n : ℕ} {g : ℝ}

/-- **The localizing times are stopping times of the usual augmentation.** -/
theorem isStoppingTime_loc (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
    (hgood : ∀ ω ∈ G, IsGBGood k xL xR ρL ρR W VL VR B ζ T ω)
    (hT : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (T n ω : WithTop ℝ≥0)) :
    IsStoppingTime (usualAugmentation 𝓕 P)
      fun ω => (loc G W VL VR B ζ T mL mR n g ω : WithTop ℝ≥0) :=
  Sec2.TwoSeed.isStoppingTime_capTime (hT n)
    ((isStoppingTime_hit_gb hE hGm hGc hgood (continuous_lev mL mR n g)).min
      (MathFin.isStoppingTime_exitTime_of_measurable
        (isFilteredBrownianReal_brownG_gb hE hGm hGc hgood).2.1 (continuous_brownG_gb hgood) n))

end StoppingTime

/-! ### The compact set -/

section Compact

/-- The compact set of the localization: `x = Λ.1 − √κ b ≥ 0` and `‖q‖ ≤ (2 + √κ) n + |x_{R,0}|`. -/
def kc (κ : ℝ) (n : ℕ) (x0 : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  {q | 0 ≤ gapX κ q ∧ ‖q‖ ≤ (2 + Real.sqrt κ) * n + |x0|}

theorem isCompact_kc (κ : ℝ) (n : ℕ) (x0 : ℝ) : IsCompact (kc κ n x0) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const (continuous_gapX κ)).inter
      (isClosed_le continuous_norm continuous_const)
  · refine (Metric.isBounded_closedBall (x := (0 : (ℝ × ℝ) × ℝ))
      (r := (2 + Real.sqrt κ) * n + |x0|)).subset fun q hq => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hq.2

theorem kc_subset_obsRegion {κ ν : ℝ} (hν : 0 < ν) (n : ℕ) (x0 : ℝ) : kc κ n x0 ⊆ obsRegion κ ν :=
  fun q hq => by
    show 0 < gapX κ q + ν
    linarith [hq.1]

end Compact

/-! ### The localized Itô formula -/

section Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {k : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {G : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} {mL mR n : ℕ} {g : ℝ}

/-- **Up to `σ_n` the coordinates and the Brownian motion stay in the compact set.** -/
theorem mem_kc_of_le_loc (hnR : 0 < nR) (hx0 : 0 ≤ xR ⟨0, hnR⟩)
    (hgood : ∀ ω ∈ G, IsGBGood k xL xR ρL ρR W VL VR B ζ T ω) (ω : Ω) {r : ℝ≥0}
    (hr : r ≤ loc G W VL VR B ζ T mL mR n g ω) :
    (coordG k xR G W VR B ⟨0, hnR⟩ ⟨0, hnR⟩ r ω, Sec2.TwoSeed.brownG G B r ω) ∈
      kc k n (xR ⟨0, hnR⟩) := by
  set i0 : Fin nR := ⟨0, hnR⟩
  have hM : |xR i0| ≤ (2 + Real.sqrt k) * n + |xR i0| := by
    have : 0 ≤ (2 + Real.sqrt k) * n := by have := Real.sqrt_nonneg k; positivity
    linarith
  have hinit : (((xR i0, xR i0 - xR i0), (0 : ℝ)) : (ℝ × ℝ) × ℝ) ∈ kc k n (xR i0) := by
    refine ⟨?_, ?_⟩
    · simp only [gapX, mul_zero, sub_zero]; exact hx0
    · simp only [sub_self, Prod.norm_def, Real.norm_eq_abs, abs_zero]
      have : 0 ≤ (2 + Real.sqrt k) * n + |xR i0| := (abs_nonneg _).trans hM
      exact max_le (max_le hM this) this
  by_cases hωG : ω ∈ G
  swap
  · simp only [coordG, Sec2.TwoSeed.brownG, hωG, ↓reduceIte]; exact hinit
  have hω := hgood ω hωG
  have hF := hω.1.isForcePath
  simp only [coordG, Sec2.TwoSeed.brownG, hωG, ↓reduceIte]
  rcases (zero_le (a := loc G W VL VR B ζ T mL mR n g ω)).eq_or_lt with h0 | h0
  · have hr0 : r = 0 := le_antisymm (h0 ▸ hr) bot_le
    subst hr0
    have hw : W 0 ω = 0 := hF.w_zero
    have hj : VR i0 0 ω = xR i0 := hF.vR_zero i0
    simp only [coordAt, hw, hj, hω.2.2.1, mul_zero, add_zero, sub_zero]
    exact hinit
  have hrζ : (r : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hr) (loc_lt_lifetime hω)
  have hlev := lev_nonneg_of_le_loc hω hωG h0 hr
  simp only [lev, le_min_iff] at hlev
  have hn : ‖Coupling.stateAt W VL VR r ω‖ ≤ n := by linarith [hlev.1]
  obtain ⟨hw, -, hv⟩ := abs_le_norm_state (Coupling.stateAt W VL VR r ω)
  simp only [Coupling.stateAt] at hw hv
  have hB := abs_B_le_of_le_loc hgood hωG hr
  have hsk : 0 ≤ Real.sqrt k := Real.sqrt_nonneg k
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨?_, ?_⟩
  · simp only [gapX, coordAt]
    have := hF.w_le_vR hrζ i0
    linarith
  · have ha : |VR i0 r ω - W r ω + Real.sqrt k * B r ω| ≤ (2 + Real.sqrt k) * n := by
      have h1 := abs_add_le (VR i0 r ω - W r ω) (Real.sqrt k * B r ω)
      have h2 := abs_sub (VR i0 r ω) (W r ω)
      rw [abs_mul, abs_of_nonneg hsk] at h1
      have h3 : Real.sqrt k * |B r ω| ≤ Real.sqrt k * n := mul_le_mul_of_nonneg_left hB hsk
      linarith [(hv i0).trans hn, hw.trans hn]
    have hb : |B r ω| ≤ (2 + Real.sqrt k) * n := hB.trans (by nlinarith)
    have hxa := abs_nonneg (xR i0)
    simp only [coordAt, sub_self, Prod.norm_def, Real.norm_eq_abs, abs_zero]
    refine max_le (max_le (by linarith) (by positivity)) (by linarith)

variable (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsGBGood k xL xR ρL ρR W VL VR B ζ T ω)
  (hT : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (T n ω : WithTop ℝ≥0))

include hE hGm hGc hgood hT in
/-- **The stopped coordinates are adapted.** -/
theorem measurable_coordG_loc (hnR : 0 < nR) (t : ℝ≥0) :
    Measurable[usualAugmentation 𝓕 P t] fun ω =>
      coordG k xR G W VR B ⟨0, hnR⟩ ⟨0, hnR⟩ (min t (loc G W VL VR B ζ T mL mR n g ω)) ω := by
  obtain ⟨-, hWa, -, hVRa, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  set 𝓖 := usualAugmentation 𝓕 P
  set i0 : Fin nR := ⟨0, hnR⟩
  have hG0 := measurableSet_good_usual' (𝓕 := 𝓕) hGm hGc 0
  have hσ := isStoppingTime_loc (mL := mL) (mR := mR) (n := n) (g := g) hE hGm hGc hgood hT
  have hB' := isFilteredBrownianReal_brownG_gb hE hGm hGc hgood
  set Kp : ℝ≥0 → Ω → ℝ × ℝ := fun s ω =>
    ((if (s : ℝ≥0∞) < ζ ω then VR i0 s ω else 0) - (if (s : ℝ≥0∞) < ζ ω then W s ω else 0) +
        Real.sqrt k * Sec2.TwoSeed.brownG G B s ω,
      (if (s : ℝ≥0∞) < ζ ω then VR i0 s ω else 0) - (if (s : ℝ≥0∞) < ζ ω then VR i0 s ω else 0))
    with hKp
  have hK : ∀ s, Measurable[𝓖 s] (Kp s) := fun s =>
    (((Sec2.TwoSeed.measurable_killed (hVRa i0) s).sub (Sec2.TwoSeed.measurable_killed hWa s)).add
      (measurable_const.mul (hB'.2.1 s))).prodMk
      ((Sec2.TwoSeed.measurable_killed (hVRa i0) s).sub (Sec2.TwoSeed.measurable_killed (hVRa i0) s))
  have h := Ito.measurable_stopped_of_agree
    (X := fun s ω => coordAt k i0 i0 (W · ω) (fun i t => VR i t ω) (B · ω) s) hσ hK hG0
    ((xR i0, xR i0 - xR i0) : ℝ × ℝ) (fun ω hω s hs => ?_) (fun ω hω => ?_) t
  · convert h using 2 with ω
    by_cases hω : ω ∈ G <;> simp [coordG, hω]
  · have hsζ : (s : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hs) (loc_lt_lifetime (hgood ω hω))
    simp only [hKp, hsζ, ↓reduceIte, Sec2.TwoSeed.brownG, hω, coordAt]
  · have hF := (hgood ω hω).1.isForcePath
    have hsub : Iic (loc G W VL VR B ζ T mL mR n g ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} :=
      fun s hs => lt_of_le_of_lt (by exact_mod_cast hs) (loc_lt_lifetime (hgood ω hω))
    have hBc : ContinuousOn (B · ω) (Iic (loc G W VL VR B ζ T mL mR n g ω)) :=
      (hgood ω hω).2.1.continuousOn
    exact ((((hF.continuousOn_vR i0).mono hsub).sub (hF.continuousOn_w.mono hsub)).add
      (continuousOn_const.mul hBc)).prodMk (((hF.continuousOn_vR i0).mono hsub).sub
        ((hF.continuousOn_vR i0).mono hsub))

include hE hGm hGc hgood hT in
/-- **The localized Itô formula for the DS1 observable**: with `σ = σ_n`,
`f(X₁(t ∧ σ)) − ∫₀^{t∧σ} itoGen` is a martingale of the usual augmentation. -/
theorem martingale_obs (hnR : 0 < nR) (hx0 : 0 ≤ xR ⟨0, hnR⟩) {p ν r : ℝ} (hν : 0 < ν) :
    Martingale (fun t ω =>
      obs k p ν r (coordG k xR G W VR B ⟨0, hnR⟩ ⟨0, hnR⟩ (min t (loc G W VL VR B ζ T mL mR n g ω)) ω,
          Sec2.TwoSeed.brownG G B (min t (loc G W VL VR B ζ T mL mR n g ω)) ω) -
        ∫ s in (0 : ℝ)..(min t (loc G W VL VR B ζ T mL mR n g ω) : ℝ≥0),
          Ito.itoGen (obs k p ν r) (coordG k xR G W VR B ⟨0, hnR⟩ ⟨0, hnR⟩ s.toNNReal ω,
            Sec2.TwoSeed.brownG G B s.toNNReal ω) (densG ρL ρR G W VL VR ⟨0, hnR⟩ ⟨0, hnR⟩ s ω))
      (usualAugmentation 𝓕 P) P := by
  set i0 : Fin nR := ⟨0, hnR⟩
  set σ := loc G W VL VR B ζ T mL mR n g with hσdef
  have hB' := isFilteredBrownianReal_brownG_gb hE hGm hGc hgood
  have hlam : ∀ ω, IntervalIntegrable (densG ρL ρR G W VL VR i0 i0 · ω) volume 0 (σ ω) := fun ω => by
    by_cases hω : ω ∈ G
    · simpa only [densG, hω, ↓reduceIte] using
        intervalIntegrable_densAt (hgood ω hω).1 (loc_lt_lifetime (hgood ω hω))
    · simp only [densG, hω, ↓reduceIte]; exact intervalIntegrable_const
  have hΛ : ∀ ω (t : ℝ≥0), t ≤ σ ω → coordG k xR G W VR B i0 i0 t ω =
      coordG k xR G W VR B i0 i0 0 ω + ∫ s in (0 : ℝ)..t, densG ρL ρR G W VL VR i0 i0 s ω := by
    intro ω t ht
    by_cases hω : ω ∈ G
    · simp only [coordG, densG, hω, ↓reduceIte]
      exact coordAt_eq_add_integral (hgood ω hω).1 (hgood ω hω).2.2.1
        (lt_of_le_of_lt (by exact_mod_cast ht) (loc_lt_lifetime (hgood ω hω)))
    · simp only [coordG, densG, hω, ↓reduceIte, intervalIntegral.integral_zero, add_zero]
  have hKb0 : 0 ≤ gbKb xL xR ρL ρR i0 i0 n := by
    unfold gbKb
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : 0 ≤ ∑ i, |ρL i| * ((|xL i| + n) / 2) :=
      sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (by positivity)
    have h2 : 0 ≤ ∑ i, |ρR i| * ((n + |xR i|) / 2) :=
      sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (by positivity)
    have := abs_nonneg (xR i0)
    linarith
  have hKb : ∀ ω, ∫ s in (0 : ℝ)..(σ ω), ‖densG ρL ρR G W VL VR i0 i0 s ω‖ ≤
      gbKb xL xR ρL ρR i0 i0 n := by
    intro ω
    by_cases hω : ω ∈ G
    · simp only [densG, hω, ↓reduceIte]
      rcases (zero_le (a := σ ω)).eq_or_lt with h0 | h0
      · rw [← h0, NNReal.coe_zero, intervalIntegral.integral_same]; exact hKb0
      have hO := lev_nonneg_of_le_loc (hgood ω hω) hω h0 le_rfl
      simp only [lev, le_min_iff] at hO
      have hn : ‖Coupling.stateAt W VL VR (σ ω) ω‖ ≤ n := by linarith [hO.1]
      obtain ⟨-, hvL, hvR⟩ := abs_le_norm_state (Coupling.stateAt W VL VR (σ ω) ω)
      exact integral_norm_densAt_le (hgood ω hω).1 (loc_lt_lifetime (hgood ω hω))
        (fun i => (hvL i).trans hn) (fun i => (hvR i).trans hn)
    · simp only [densG, hω, ↓reduceIte, norm_zero, intervalIntegral.integral_zero]
      exact hKb0
  exact Ito.martingale_itoLocalized hB' (continuous_brownG_gb hgood) (isOpen_obsRegion k ν)
    (contDiffOn_obs k p ν r) (isCompact_kc k n (xR i0)) (kc_subset_obsRegion hν n (xR i0))
    (isStoppingTime_loc hE hGm hGc hgood hT) (measurable_coordG_loc hE hGm hGc hgood hT hnR)
    hlam hΛ hKb (fun ω t ht => mem_kc_of_le_loc hnR hx0 hgood ω ht)

end Martingale

end DS1

end Supp12

end InteractingSLE
