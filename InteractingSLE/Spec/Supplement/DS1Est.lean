/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS1Level

/-!
# Lemma DS1: the regularized occupation bound at one localization level

Packet PROVE-T14-TIP (specification supplement §12, **Lemma DS1**, `source/spec/p529-576.md` L523–L575, pp. 551–553):
"The martingale has mean zero at the bounded time stop, while the endpoint expectation of `f_ν` is uniformly
bounded. This proves (DS1.3)."

* `gapStop`: the gap `X₁ = V^{R,0} − W` stopped at a time `σ` (on the good event);
* `levelInt φ σ X t ω = ∫⁻_{(0, t]} 1{s ≤ σ(ω)} φ(X_s(ω)) ds`, and `measurable_levelInt` (the integrand is jointly
  measurable: the stopped gap is continuous in time and measurable in `ω`);
* **`lintegral_levelInt_occ_le`**: at every localization level `n`,
  `E ∫₀^{t∧σ_n} 1{X₁ < r}(X₁ + ν)^{p−2} ds ≤ ((3r)^p + C₂ t)/c₀`, uniformly in `n` and `ν ∈ (0, r]`.
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

/-! ### The stopped gap and the level integrals -/

section Defs

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

open scoped Classical in
/-- The gap `X₁ = V^{R,0} − W` stopped at `σ`, on the good event (`x₀` off it). -/
def gapStop (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (i0 : Fin nR) (x0 : ℝ)
    (σ : Ω → ℝ≥0) (s : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ G then VR i0 (min s (σ ω)) ω - W (min s (σ ω)) ω else x0

/-- `∫⁻_{(0, t]} 1{s ≤ σ(ω)} φ(X_s(ω)) ds`. -/
def levelInt (φ : ℝ → ℝ≥0∞) (σ : Ω → ℝ≥0) (X : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ s in Ioc (0 : ℝ) t, {s : ℝ | s ≤ σ ω}.indicator (fun s => φ (X s.toNNReal ω)) s

end Defs

/-! ### Measurability -/

section Meas

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {k : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {G : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} {mL mR n : ℕ} {g : ℝ}

/-- A finite stopping time is measurable. -/
theorem measurable_of_isStoppingTime' {𝓖 : Filtration ℝ≥0 mΩ} {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime 𝓖 fun ω => (σ ω : WithTop ℝ≥0)) : Measurable σ :=
  measurable_of_Iic fun t => by
    have := (𝓖.le t) _ (hσ t)
    simp only [WithTop.coe_le_coe] at this
    exact this

theorem continuous_gapStop (hgood : ∀ ω ∈ G, IsGBGood k xL xR ρL ρR W VL VR B ζ T ω) (i0 : Fin nR)
    (x0 : ℝ) (ω : Ω) : Continuous fun s : ℝ => gapStop G W VR i0 x0 (loc G W VL VR B ζ T mL mR n g) s.toNNReal ω := by
  by_cases hω : ω ∈ G
  · simp only [gapStop, hω, ↓reduceIte]
    have hF := (hgood ω hω).1.isForcePath
    set σ := loc G W VL VR B ζ T mL mR n g ω
    have hsub : Iic σ ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} :=
      fun s hs => lt_of_le_of_lt (by exact_mod_cast hs) (loc_lt_lifetime (hgood ω hω))
    have hc : ContinuousOn (fun u : ℝ≥0 => VR i0 u ω - W u ω) (Iic σ) :=
      ((hF.continuousOn_vR i0).mono hsub).sub (hF.continuousOn_w.mono hsub)
    have hm : Continuous fun s : ℝ => min s.toNNReal σ := continuous_real_toNNReal.min continuous_const
    exact hc.comp_continuous hm fun s => Set.mem_Iic.2 (min_le_right _ _)
  · simp only [gapStop, hω, ↓reduceIte]; exact continuous_const

variable (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsGBGood k xL xR ρL ρR W VL VR B ζ T ω)
  (hT : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (T n ω : WithTop ℝ≥0))
include hE hGm hGc hgood hT

theorem measurable_gapStop (i0 : Fin nR) (x0 : ℝ) (s : ℝ≥0) :
    Measurable (gapStop G W VR i0 x0 (loc G W VL VR B ζ T mL mR n g) s) := by
  obtain ⟨-, hWa, -, hVRa, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  set 𝓖 := usualAugmentation 𝓕 P
  have hG0 := measurableSet_good_usual' (𝓕 := 𝓕) hGm hGc 0
  have hσ := isStoppingTime_loc (mL := mL) (mR := mR) (n := n) (g := g) hE hGm hGc hgood hT
  set Kp : ℝ≥0 → Ω → ℝ := fun s ω =>
    (if (s : ℝ≥0∞) < ζ ω then VR i0 s ω else 0) - (if (s : ℝ≥0∞) < ζ ω then W s ω else 0) with hKp
  have hK : ∀ s, Measurable[𝓖 s] (Kp s) := fun s =>
    (Sec2.TwoSeed.measurable_killed (hVRa i0) s).sub (Sec2.TwoSeed.measurable_killed hWa s)
  have h := Ito.measurable_stopped_of_agree (X := fun s ω => VR i0 s ω - W s ω) hσ hK hG0 x0
    (fun ω hω s hs => ?_) (fun ω hω => ?_) s
  · exact h.mono (𝓖.le s) le_rfl
  · have hsζ : (s : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hs) (loc_lt_lifetime (hgood ω hω))
    simp only [hKp, hsζ, ↓reduceIte]
  · have hF := (hgood ω hω).1.isForcePath
    have hsub : Iic (loc G W VL VR B ζ T mL mR n g ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} :=
      fun s hs => lt_of_le_of_lt (by exact_mod_cast hs) (loc_lt_lifetime (hgood ω hω))
    exact ((hF.continuousOn_vR i0).mono hsub).sub (hF.continuousOn_w.mono hsub)

/-- **The level integrals are measurable.** -/
theorem measurable_levelInt (i0 : Fin nR) (x0 : ℝ) {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) (t : ℝ) :
    Measurable (levelInt φ (loc G W VL VR B ζ T mL mR n g)
      (gapStop G W VR i0 x0 (loc G W VL VR B ζ T mL mR n g)) t) := by
  set σ := loc G W VL VR B ζ T mL mR n g
  have hσm : Measurable σ := measurable_of_isStoppingTime' (isStoppingTime_loc hE hGm hGc hgood hT)
  have hX : Measurable fun q : ℝ × Ω => gapStop G W VR i0 x0 σ q.1.toNNReal q.2 :=
    measurable_uncurry_of_continuous_of_measurable (u := fun s : ℝ => gapStop G W VR i0 x0 σ s.toNNReal)
      (fun ω => continuous_gapStop hgood i0 x0 ω)
      (fun s => measurable_gapStop hE hGm hGc hgood hT i0 x0 s.toNNReal)
  have hset : MeasurableSet {q : Ω × ℝ | q.2 ≤ σ q.1} :=
    measurableSet_le measurable_snd (measurable_coe_nnreal_real.comp (hσm.comp measurable_fst))
  have hF : Measurable fun q : Ω × ℝ =>
      {s : ℝ | s ≤ σ q.1}.indicator (fun s => φ (gapStop G W VR i0 x0 σ s.toNNReal q.1)) q.2 := by
    have : (fun q : Ω × ℝ => {s : ℝ | s ≤ σ q.1}.indicator
        (fun s => φ (gapStop G W VR i0 x0 σ s.toNNReal q.1)) q.2) =
        {q : Ω × ℝ | q.2 ≤ σ q.1}.indicator (fun q => φ (gapStop G W VR i0 x0 σ q.2.toNNReal q.1)) := by
      funext q; by_cases h : q.2 ≤ σ q.1 <;> simp [indicator, h]
    rw [this]
    exact (hφ.comp (hX.comp measurable_swap)).indicator hset
  exact hF.lintegral_prod_right'

end Meas

/-! ### The estimate at one localization level -/

section Estimate

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {k : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {G : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} {mL mR n : ℕ} {g : ℝ}

/-- On a good path the stopped gap is nonnegative. -/
theorem gapStop_nonneg (hgood : ∀ ω ∈ G, IsGBGood k xL xR ρL ρR W VL VR B ζ T ω) (hnR : 0 < nR)
    {ω : Ω} (hω : ω ∈ G) (s : ℝ≥0) :
    0 ≤ gapStop G W VR ⟨0, hnR⟩ (xR ⟨0, hnR⟩) (loc G W VL VR B ζ T mL mR n g) s ω := by
  simp only [gapStop, hω, ↓reduceIte]
  have hF := (hgood ω hω).1.isForcePath
  have hlt : ((min s (loc G W VL VR B ζ T mL mR n g ω) : ℝ≥0) : ℝ≥0∞) < ζ ω :=
    lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) (loc_lt_lifetime (hgood ω hω))
  exact sub_nonneg.2 (hF.w_le_vR hlt _)

/-- **The pathwise inequality.** On a good path, with `τ = t ∧ σ_n`, the level integral of `h_ν(X₁)` is
`ofReal J` with `c₀ J ≤ (3r)^p − M_t + C₂ t` (`M` the martingale of `martingale_obs`). -/
theorem pathwise_occ (hgood : ∀ ω ∈ G, IsGBGood k xL xR ρL ρR W VL VR B ζ T ω) (hκ : 0 < k) (hnR : 0 < nR)
    (hmR : mR ≤ nR) {p ν r ε Rw a K : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hν : 0 < ν) (hνr : ν ≤ r)
    (hr : 0 < r) (hra : 8 * r ≤ a) (hrg : 2 * r < g) (hκp : k * (1 - p) ≤ ε)
    (hrC : 2 * r * cst0 nL nR Rw g a ≤ ε / 4) (hR : 0 ≤ Rw) (hg : 0 < g) (ha : 0 < a)
    (hρL : ∀ i, |ρL i| ≤ Rw) (hρR : ∀ j, |ρR j| ≤ Rw)
    (hin : ∀ j : Fin nR, (j : ℕ) < mR → ε ≤ ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l + 2)
    (hcross : ∀ i, a ≤ xR ⟨0, hnR⟩ - xL i)
    (hK : ∀ y, |deriv Real.smoothTransition y| ≤ K ∧ |deriv (deriv Real.smoothTransition) y| ≤ K)
    (t : ℝ≥0) {ω : Ω} (hω : ω ∈ G) :
    ∃ J : ℝ, 0 ≤ J ∧
      levelInt (fun x => ENNReal.ofReal (occ p ν r x)) (loc G W VL VR B ζ T mL mR n g)
        (gapStop G W VR ⟨0, hnR⟩ (xR ⟨0, hnR⟩) (loc G W VL VR B ζ T mL mR n g)) t ω = ENNReal.ofReal J ∧
      p * ε / 4 * J ≤ (3 * r) ^ p -
        (obs k p ν r (coordG k xR G W VR B ⟨0, hnR⟩ ⟨0, hnR⟩ (min t (loc G W VL VR B ζ T mL mR n g ω)) ω,
            Sec2.TwoSeed.brownG G B (min t (loc G W VL VR B ζ T mL mR n g ω)) ω) -
          ∫ s in (0 : ℝ)..(min t (loc G W VL VR B ζ T mL mR n g ω) : ℝ≥0),
            Ito.itoGen (obs k p ν r) (coordG k xR G W VR B ⟨0, hnR⟩ ⟨0, hnR⟩ s.toNNReal ω,
              Sec2.TwoSeed.brownG G B s.toNNReal ω) (densG ρL ρR G W VL VR ⟨0, hnR⟩ ⟨0, hnR⟩ s ω)) +
        cst2 k p r K nL nR Rw a * t := by
  set i0 : Fin nR := ⟨0, hnR⟩
  set σ := loc G W VL VR B ζ T mL mR n g with hσdef
  set τ : ℝ≥0 := min t (σ ω) with hτ
  have hgω := hgood ω hω
  have hP := hgω.1
  have hF := hP.isForcePath
  set X : ℝ → ℝ := fun s => gapStop G W VR i0 (xR i0) σ s.toNNReal ω with hXdef
  have hXc : Continuous X := continuous_gapStop hgood i0 (xR i0) ω
  have hX0 : ∀ s, 0 ≤ X s := fun s => gapStop_nonneg hgood hnR hω _
  have hτζ : (τ : ℝ≥0∞) < ζ ω :=
    lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) (loc_lt_lifetime hgω)
  have hτσ : τ ≤ σ ω := min_le_right _ _
  have hτt : τ ≤ t := min_le_left _ _
  -- the occupation integrand is integrable
  have hoccm : Measurable fun s => occ p ν r (X s) := (measurable_occ p ν r).comp hXc.measurable
  have hoccb : ∀ s, ‖occ p ν r (X s)‖ ≤ ν ^ (p - 2) := fun s => by
    rw [Real.norm_eq_abs, abs_of_nonneg (occ_nonneg hν.le (hX0 s))]
    exact occ_le (by linarith) hν (hX0 s)
  have hoccI : IntegrableOn (fun s => occ p ν r (X s)) (Ioc 0 (τ : ℝ)) volume :=
    IntegrableOn.of_bound measure_Ioc_lt_top hoccm.aestronglyMeasurable _ (Eventually.of_forall hoccb)
  set J := ∫ s in (0 : ℝ)..(τ : ℝ), occ p ν r (X s) with hJ
  have hJ0 : 0 ≤ J := intervalIntegral.integral_nonneg τ.coe_nonneg fun s _ => occ_nonneg hν.le (hX0 s)
  refine ⟨J, hJ0, ?_, ?_⟩
  · -- the level integral is `ofReal J`
    unfold levelInt
    have hset : (Iic ((σ ω : ℝ≥0) : ℝ) ∩ Ioc 0 (t : ℝ)) = Ioc 0 (τ : ℝ) := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc, hτ, NNReal.coe_min, le_min_iff]
      tauto
    rw [show {s : ℝ | s ≤ σ ω} = Iic ((σ ω : ℝ≥0) : ℝ) from rfl, lintegral_indicator measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Iic, hset, hJ, intervalIntegral.integral_of_le τ.coe_nonneg,
      ofReal_integral_eq_lintegral_ofReal hoccI (Eventually.of_forall fun s => occ_nonneg hν.le (hX0 s))]
  · -- the generator bound
    have hcoordG : ∀ s : ℝ≥0, coordG k xR G W VR B i0 i0 s ω = coordAt k i0 i0 (W · ω) (fun i t => VR i t ω)
        (B · ω) s := fun s => by simp only [coordG, hω, ↓reduceIte]
    have hbrown : ∀ s : ℝ≥0, Sec2.TwoSeed.brownG G B s ω = B s ω := fun s => by
      simp only [Sec2.TwoSeed.brownG, hω, ↓reduceIte]
    have hdensG : ∀ s : ℝ, densG ρL ρR G W VL VR i0 i0 s ω = densAt ρL ρR i0 i0 (W · ω)
        (fun i t => VL i t ω) (fun i t => VR i t ω) s := fun s => by simp only [densG, hω, ↓reduceIte]
    simp only [hcoordG, hbrown, hdensG]
    set I := ∫ s in (0 : ℝ)..(τ : ℝ), Ito.itoGen (obs k p ν r)
      (coordAt k i0 i0 (W · ω) (fun i t => VR i t ω) (B · ω) s.toNNReal, B s.toNNReal ω)
      (densAt ρL ρR i0 i0 (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s) with hI
    -- the endpoint value
    have hend : obs k p ν r (coordAt k i0 i0 (W · ω) (fun i t => VR i t ω) (B · ω) τ, B τ ω) ≤ (3 * r) ^ p := by
      unfold obs
      rw [show (coordAt k i0 i0 (W · ω) (fun i t => VR i t ω) (B · ω) τ).1 - Real.sqrt k * B τ ω =
        VR i0 τ ω - W τ ω by simp only [coordAt]; ring]
      exact fn_le hp0.le hν.le hνr hr (sub_nonneg.2 (hF.w_le_vR hτζ i0))
    -- the integrated generator
    set C₂ := cst2 k p r K nL nR Rw a
    have hC₂ : 0 ≤ C₂ := cst2_nonneg hκ.le hr ((abs_nonneg _).trans (hK 0).1) hR ha
    have hgen : p * ε / 4 * J - C₂ * τ ≤ I := by
      rcases (zero_le (a := σ ω)).eq_or_lt with h0 | h0
      · have : τ = 0 := le_antisymm (h0 ▸ hτσ) bot_le
        rw [hJ, hI, this, NNReal.coe_zero, intervalIntegral.integral_same, intervalIntegral.integral_same]
        simp
      -- integrability of the generator
      have hv1 : IntervalIntegrable (fun s : ℝ => 2 / (VR i0 s.toNNReal ω - W s.toNNReal ω)) volume 0 τ :=
        intervalIntegrable_two_div_gapR hP hτζ i0
      have hv2 : IntervalIntegrable (Ito.driftAt ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω))
          volume 0 τ := Ito.intervalIntegrable_driftAt hP hτζ
      have hfn1 : Continuous fun s => fn1 p ν r (X s) :=
        continuousOn_fn1.comp_continuous hXc fun s => by
          show -ν < X s; linarith [hX0 s]
      have hfn2 : Continuous fun s => fn2 p ν r (X s) :=
        continuousOn_fn2.comp_continuous hXc fun s => by
          show -ν < X s; linarith [hX0 s]
      have hgi : IntervalIntegrable (fun s => fn1 p ν r (X s) *
          (2 / (VR i0 s.toNNReal ω - W s.toNNReal ω) -
            Ito.driftAt ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s) +
          k / 2 * fn2 p ν r (X s)) volume 0 τ :=
        ((hv1.sub hv2).continuousOn_mul hfn1.continuousOn).add
          (hfn2.intervalIntegrable 0 τ |>.const_mul (k / 2))
      have hXeq : ∀ s : ℝ, 0 ≤ s → s ≤ τ → X s = VR i0 s.toNNReal ω - W s.toNNReal ω := fun s hs0 hsτ => by
        have : s.toNNReal ≤ σ ω := (Real.toNNReal_le_iff_le_coe.2 hsτ).trans hτσ
        simp only [hXdef, gapStop, hω, ↓reduceIte, min_eq_left this]
      have hIi : IntervalIntegrable (fun s => Ito.itoGen (obs k p ν r)
          (coordAt k i0 i0 (W · ω) (fun i t => VR i t ω) (B · ω) s.toNNReal, B s.toNNReal ω)
          (densAt ρL ρR i0 i0 (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s)) volume 0 τ := by
        refine hgi.congr fun s hs => ?_
        rw [uIoc_of_le τ.coe_nonneg] at hs
        have hsζ : (s.toNNReal : ℝ≥0∞) < ζ ω :=
          lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) hτζ
        have hq : (coordAt k i0 i0 (W · ω) (fun i t => VR i t ω) (B · ω) s.toNNReal, B s.toNNReal ω) ∈
            obsRegion k ν := by
          show 0 < gapX k _ + ν
          rw [gapX_coordAt]; linarith [hF.w_le_vR hsζ i0]
        rw [itoGen_obs hκ.le hq, gapX_coordAt, hXeq s hs.1.le hs.2]
        simp only [densAt]
      have hJI : IntervalIntegrable (fun s => occ p ν r (X s)) volume 0 τ :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le τ.coe_nonneg).2 hoccI
      have hmono := intervalIntegral.integral_mono_ae_restrict τ.coe_nonneg
        ((hJI.const_mul (p * ε / 4)).sub (intervalIntegrable_const (c := C₂))) hIi ?_
      · rw [intervalIntegral.integral_sub (hJI.const_mul _) intervalIntegrable_const,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmono
        rw [hJ, hI]; linarith
      rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
      filter_upwards [ae_noncollision hP] with s hs hsI
      have hsτ : s.toNNReal ≤ τ := Real.toNNReal_le_iff_le_coe.2 hsI.2
      have hsζ : (s.toNNReal : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hsτ) hτζ
      obtain ⟨hncL, hncR⟩ := hs hsI.1 hsζ
      have hlev := lev_nonneg_of_le_loc hgω hω h0 (hsτ.trans hτσ)
      simp only [lev, le_min_iff] at hlev
      have hfar : ∀ j : Fin nR, mR ≤ (j : ℕ) → g ≤ VR j s.toNNReal ω - W s.toNNReal ω := fun j hj => by
        have hlt : mR < nR := lt_of_le_of_lt hj j.2
        have h1 := hlev.2.1
        simp only [farR, hlt, ↓reduceDIte, Coupling.stateAt] at h1
        have h2 := hF.monotone_vR hsζ (show (⟨mR, hlt⟩ : Fin nR) ≤ j from hj)
        simp only at h2
        linarith
      have := itoGen_ge_path hP hκ hnR hmR hp0 hp1 hν hνr hr hra hrg hκp hrC hR hg ha hρL hρR hin hcross hK
        hsζ hfar hncL hncR (b := (B · ω))
      rw [← hXeq s hsI.1 hsI.2] at this
      simpa only [Pi.sub_apply] using this
    have hτt' : C₂ * τ ≤ C₂ * t := mul_le_mul_of_nonneg_left (by exact_mod_cast hτt) hC₂
    linarith

/-- **(DS1.3) at one localization level**: `E ∫₀^{t∧σ_n} 1{X₁ < r}(X₁ + ν)^{p−2} ds ≤ ((3r)^p + C₂ t)/c₀`. -/
theorem lintegral_levelInt_occ_le (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hGm : MeasurableSet G) (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsGBGood k xL xR ρL ρR W VL VR B ζ T ω)
    (hT : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (T n ω : WithTop ℝ≥0))
    (hκ : 0 < k) (hnR : 0 < nR) (hx0 : 0 ≤ xR ⟨0, hnR⟩)
    (hmR : mR ≤ nR) {p ν r ε Rw a K : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hν : 0 < ν) (hνr : ν ≤ r)
    (hr : 0 < r) (hra : 8 * r ≤ a) (hrg : 2 * r < g) (hκp : k * (1 - p) ≤ ε) (hε : 0 < ε)
    (hrC : 2 * r * cst0 nL nR Rw g a ≤ ε / 4) (hR : 0 ≤ Rw) (hg : 0 < g) (ha : 0 < a)
    (hρL : ∀ i, |ρL i| ≤ Rw) (hρR : ∀ j, |ρR j| ≤ Rw)
    (hin : ∀ j : Fin nR, (j : ℕ) < mR → ε ≤ ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l + 2)
    (hcross : ∀ i, a ≤ xR ⟨0, hnR⟩ - xL i)
    (hK : ∀ y, |deriv Real.smoothTransition y| ≤ K ∧ |deriv (deriv Real.smoothTransition) y| ≤ K)
    (t : ℝ≥0) :
    ∫⁻ ω, levelInt (fun x => ENNReal.ofReal (occ p ν r x)) (loc G W VL VR B ζ T mL mR n g)
        (gapStop G W VR ⟨0, hnR⟩ (xR ⟨0, hnR⟩) (loc G W VL VR B ζ T mL mR n g)) t ω ∂P ≤
      ENNReal.ofReal (((3 * r) ^ p + cst2 k p r K nL nR Rw a * t) / (p * ε / 4)) := by
  have hPm : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  set i0 : Fin nR := ⟨0, hnR⟩
  set σ := loc G W VL VR B ζ T mL mR n g with hσdef
  set c₀ := p * ε / 4 with hc₀
  have hc₀0 : 0 < c₀ := by positivity
  set C₂ := cst2 k p r K nL nR Rw a
  set M : ℝ≥0 → Ω → ℝ := fun t ω =>
    obs k p ν r (coordG k xR G W VR B i0 i0 (min t (σ ω)) ω, Sec2.TwoSeed.brownG G B (min t (σ ω)) ω) -
      ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0), Ito.itoGen (obs k p ν r)
        (coordG k xR G W VR B i0 i0 s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω)
        (densG ρL ρR G W VL VR i0 i0 s ω) with hMdef
  have hM : Martingale M (usualAugmentation 𝓕 P) P :=
    martingale_obs (mL := mL) (mR := mR) (n := n) (g := g) hE hGm hGc hgood hT hnR hx0 hν
  set Φ0 := fn p ν r (xR i0) with hΦ0
  have hM0 : ∀ ω, M 0 ω = Φ0 := by
    intro ω
    simp only [hMdef, zero_min, NNReal.coe_zero, intervalIntegral.integral_same, sub_zero, obs]
    by_cases hω : ω ∈ G
    · have hF := (hgood ω hω).1.isForcePath
      have hw : W 0 ω = 0 := hF.w_zero
      have hj : VR i0 0 ω = xR i0 := hF.vR_zero i0
      simp only [coordG, Sec2.TwoSeed.brownG, hω, ↓reduceIte, coordAt, hw, hj, (hgood ω hω).2.2.1,
        mul_zero, add_zero, sub_zero, hΦ0]
    · simp only [coordG, Sec2.TwoSeed.brownG, hω, ↓reduceIte, hΦ0, mul_zero, sub_zero]
  have hint : ∫ ω, M t ω ∂P = Φ0 := by
    have h := hM.setIntegral_eq (zero_le (a := t)) MeasurableSet.univ
    simp only [Measure.restrict_univ] at h
    rw [← h]
    simp only [hM0, integral_const, probReal_univ, one_smul]
  have hΦ00 : 0 ≤ Φ0 := fn_nonneg hp0.le hν.le hx0
  -- pathwise bounds on the good event
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  have hpw : ∀ ω ∈ G, levelInt (fun x => ENNReal.ofReal (occ p ν r x)) σ
      (gapStop G W VR i0 (xR i0) σ) t ω ≤ ENNReal.ofReal (((3 * r) ^ p - M t ω + C₂ * t) / c₀) ∧
      0 ≤ ((3 * r) ^ p - M t ω + C₂ * t) / c₀ := by
    intro ω hω
    obtain ⟨J, hJ0, hJeq, hJle⟩ := pathwise_occ (mL := mL) (n := n) hgood hκ hnR hmR hp0 hp1 hν hνr hr hra
      hrg hκp hrC hR hg ha hρL hρR hin hcross hK t hω
    have hle : J ≤ ((3 * r) ^ p - M t ω + C₂ * t) / c₀ := by
      rw [le_div_iff₀ hc₀0, mul_comm]; exact hJle
    exact ⟨hJeq ▸ ENNReal.ofReal_le_ofReal hle, hJ0.trans hle⟩
  have hfi : Integrable (fun ω => ((3 * r) ^ p - M t ω + C₂ * t) / c₀) P :=
    (((integrable_const _).sub (hM.integrable t)).add (integrable_const _)).div_const _
  calc ∫⁻ ω, levelInt (fun x => ENNReal.ofReal (occ p ν r x)) σ (gapStop G W VR i0 (xR i0) σ) t ω ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (((3 * r) ^ p - M t ω + C₂ * t) / c₀) ∂P :=
        lintegral_mono_ae (hGae.mono fun ω hω => (hpw ω hω).1)
    _ = ENNReal.ofReal (∫ ω, ((3 * r) ^ p - M t ω + C₂ * t) / c₀ ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hfi (hGae.mono fun ω hω => (hpw ω hω).2)).symm
    _ = ENNReal.ofReal (((3 * r) ^ p - Φ0 + C₂ * t) / c₀) := by
        have hi1 : Integrable (fun ω => (3 * r) ^ p - M t ω) P := (integrable_const _).sub (hM.integrable t)
        have e1 : ∫ ω, ((3 * r) ^ p - M t ω + C₂ * t) ∂P = ∫ ω, ((3 * r) ^ p - M t ω) ∂P + C₂ * t := by
          rw [integral_add hi1 (integrable_const _)]; simp only [integral_const, probReal_univ, one_smul]
        have e2 : ∫ ω, ((3 * r) ^ p - M t ω) ∂P = (3 * r) ^ p - Φ0 := by
          rw [integral_sub (integrable_const _) (hM.integrable t), hint]
          simp only [integral_const, probReal_univ, one_smul]
        rw [integral_div, e1, e2]
    _ ≤ ENNReal.ofReal (((3 * r) ^ p + C₂ * t) / c₀) := by
        refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hc₀0.le)
        linarith

end Estimate

end DS1

end Supp12

end InteractingSLE
