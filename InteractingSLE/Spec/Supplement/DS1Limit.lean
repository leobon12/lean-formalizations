/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS1Est

/-!
# Lemma DS1: removing the regularization and the localization

Packet PROVE-T14-TIP (specification supplement §12, **Lemma DS1**, `source/spec/p529-576.md` L523–L575, pp. 551–553):
"Letting `ν ↓ 0` gives `E ∫₀ᵀ 1{0 < X₁ < r} X₁^{p−2} dt ≤ C`. Since `x^{−1} ≤ δ^{1−p} x^{p−2}` for `0 < x < δ`,
(DS1.2) follows." and "Stop also at the usual coordinate bounds and remove them by localization."

* `levelInt_le_liminf` and `lintegral_levelInt_le_of_liminf`: Fatou in time and in `ω` (the level integrals are
  measurable);
* `inv_le_rpow_mul` and `occ0`: `1/x ≤ δ^{1−p} x^{p−2}` on `(0, δ)`;
* `IsAlive`: the source's stop ("before a prescribed family of far gaps falls below `g`", before the lifetime);
* `eventually_le_loc`: an alive time is eventually below the localizing times `σ_n`;
* **`lintegral_alive_le`**: a bound uniform in the localization level passes to the stopped integral.
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

/-! ### Fatou for the level integrals -/

section Fatou

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Fatou in time**: if `φ ≤ liminf φ_m` pointwise, the level integral of `φ` is at most the liminf of those
of `φ_m`. -/
theorem levelInt_le_liminf {φ : ℝ → ℝ≥0∞} {φs : ℕ → ℝ → ℝ≥0∞} (hφs : ∀ m, Measurable (φs m))
    (hle : ∀ x, φ x ≤ liminf (fun m => φs m x) atTop) {σ : Ω → ℝ≥0} {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ ω, Measurable fun s : ℝ => X s.toNNReal ω) (t : ℝ) (ω : Ω) :
    levelInt φ σ X t ω ≤ liminf (fun m => levelInt (φs m) σ X t ω) atTop := by
  unfold levelInt
  refine le_trans (lintegral_mono fun s => ?_) (lintegral_liminf_le fun m =>
    ((hφs m).comp (hX ω)).indicator measurableSet_Iic)
  by_cases hs : s ≤ σ ω
  · simp only [Set.indicator, Set.mem_ofPred_eq, hs, ↓reduceIte]; exact hle _
  · simp only [Set.indicator, Set.mem_ofPred_eq, hs, ↓reduceIte]; exact bot_le

/-- **Fatou in `ω`**: a pointwise liminf bound with measurable approximants and uniformly bounded expectations. -/
theorem lintegral_le_of_le_liminf {P : Measure Ω} {F : Ω → ℝ≥0∞} {Fs : ℕ → Ω → ℝ≥0∞}
    (hFs : ∀ m, Measurable (Fs m)) (hle : ∀ᵐ ω ∂P, F ω ≤ liminf (fun m => Fs m ω) atTop) {c : ℝ≥0∞}
    (hc : ∀ m, ∫⁻ ω, Fs m ω ∂P ≤ c) : ∫⁻ ω, F ω ∂P ≤ c := by
  calc ∫⁻ ω, F ω ∂P ≤ ∫⁻ ω, liminf (fun m => Fs m ω) atTop ∂P := lintegral_mono_ae hle
    _ ≤ liminf (fun m => ∫⁻ ω, Fs m ω ∂P) atTop := lintegral_liminf_le hFs
    _ ≤ c := liminf_le_of_frequently_le' (Frequently.of_forall hc)

end Fatou

/-! ### The unregularized density -/

/-- The density `1{0 < x < r} x^{p−2}` obtained by letting `ν ↓ 0`. -/
def occ0 (p r x : ℝ) : ℝ := {y : ℝ | 0 < y ∧ y < r}.indicator (fun y => y ^ (p - 2)) x

theorem measurable_occ0 (p r : ℝ) : Measurable (occ0 p r) := by
  unfold occ0
  exact (measurable_id.pow_const (p - 2)).indicator
    ((measurableSet_lt measurable_const measurable_id).inter (measurableSet_lt measurable_id measurable_const))

/-- `occ0 ≤ liminf_m occ_{ν_m}` with `ν_m = r/(m + 2) ↓ 0`. -/
theorem occ0_le_liminf {p r : ℝ} (x : ℝ) :
    ENNReal.ofReal (occ0 p r x) ≤
      liminf (fun m : ℕ => ENNReal.ofReal (occ p (r / ((m : ℝ) + 2)) r x)) atTop := by
  by_cases hx : 0 < x ∧ x < r
  · have h1 : occ0 p r x = x ^ (p - 2) := by
      rw [occ0, Set.indicator_of_mem (show x ∈ {y : ℝ | 0 < y ∧ y < r} from hx)]
    have h2 : ∀ m : ℕ, occ p (r / ((m : ℝ) + 2)) r x = (x + r / ((m : ℝ) + 2)) ^ (p - 2) := fun m => by
      rw [occ, Set.indicator_of_mem (show x ∈ {y : ℝ | y < r} from hx.2)]
    simp only [h1, h2]
    have hν : Tendsto (fun m : ℕ => r / ((m : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    have hc : ContinuousAt (fun y : ℝ => (x + y) ^ (p - 2)) 0 := by
      have : x + 0 ≠ 0 := by rw [add_zero]; exact hx.1.ne'
      exact (continuousAt_const.add continuousAt_id).rpow_const (Or.inl this)
    have hlim : Tendsto (fun m : ℕ => ENNReal.ofReal ((x + r / ((m : ℝ) + 2)) ^ (p - 2))) atTop
        (𝓝 (ENNReal.ofReal (x ^ (p - 2)))) := by
      have := (ENNReal.continuous_ofReal.tendsto _).comp (hc.tendsto.comp hν)
      simpa only [add_zero, Function.comp_def] using this
    exact hlim.liminf_eq.ge
  · have : occ0 p r x = 0 := by
      rw [occ0, Set.indicator_of_notMem (show x ∉ {y : ℝ | 0 < y ∧ y < r} from hx)]
    rw [this, ENNReal.ofReal_zero]; exact bot_le

/-- `1{0 < x < δ}/x ≤ δ^{1−p} · 1{0 < x < r} x^{p−2}` for `0 ≤ δ ≤ r`, `p < 1`. -/
theorem inv_le_rpow_mul {p δ r : ℝ} (hp1 : p < 1) (hδ : 0 ≤ δ) (hδr : δ ≤ r) (x : ℝ) :
    {y : ℝ | 0 < y ∧ y < δ}.indicator (fun y => 1 / y) x ≤ δ ^ (1 - p) * occ0 p r x := by
  have hocc : 0 ≤ occ0 p r x := by
    unfold occ0
    by_cases hxr : 0 < x ∧ x < r
    · rw [Set.indicator_of_mem (show x ∈ {y : ℝ | 0 < y ∧ y < r} from hxr)]
      exact Real.rpow_nonneg hxr.1.le _
    · rw [Set.indicator_of_notMem (show x ∉ {y : ℝ | 0 < y ∧ y < r} from hxr)]
  by_cases hx : 0 < x ∧ x < δ
  · have hxr : 0 < x ∧ x < r := ⟨hx.1, hx.2.trans_le hδr⟩
    rw [Set.indicator_of_mem (show x ∈ {y : ℝ | 0 < y ∧ y < δ} from hx), occ0,
      Set.indicator_of_mem (show x ∈ {y : ℝ | 0 < y ∧ y < r} from hxr)]
    have e : 1 / x = x ^ (1 - p) * x ^ (p - 2) := by
      rw [← Real.rpow_add hx.1, show 1 - p + (p - 2) = -1 by ring, Real.rpow_neg_one, one_div]
    rw [e]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx.1.le hx.2.le (by linarith))
      (Real.rpow_nonneg hx.1.le _)
  · rw [Set.indicator_of_notMem (show x ∉ {y : ℝ | 0 < y ∧ y < δ} from hx)]
    exact mul_nonneg (Real.rpow_nonneg hδ _) hocc

/-! ### The stop and the removal of the localization -/

section Alive

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The stop of DS1**: at time `s` the system is alive (`s < ζ`) and up to `s` every designated far gap is at least
`g` (right labels `j ≥ m_R`, left labels `i ≥ m_L`; "Stop the integrated system before a prescribed family of far
gaps falls below `g > 0`"). -/
def IsAlive (mL mR : ℕ) (g : ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (s : ℝ≥0) (ω : Ω) : Prop :=
  (s : ℝ≥0∞) < ζ ω ∧ ∀ u ≤ s, (∀ j : Fin nR, mR ≤ (j : ℕ) → g ≤ VR j u ω - W u ω) ∧
    ∀ i : Fin nL, mL ≤ (i : ℕ) → g ≤ W u ω - VL i u ω

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {k : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {G : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} {mL mR : ℕ} {g : ℝ}

/-- **An alive time is eventually below the localizing times.** -/
theorem eventually_le_loc (hgood : ∀ ω ∈ G, IsGBGood k xL xR ρL ρR W VL VR B ζ T ω)
    (hTm : ∀ ω, Monotone fun n => T n ω) {ω : Ω} (hω : ω ∈ G) {s : ℝ≥0}
    (hs : IsAlive mL mR g W VL VR ζ s ω) : ∀ᶠ n in atTop, s ≤ loc G W VL VR B ζ T mL mR n g ω := by
  have hgω := hgood ω hω
  obtain ⟨N₁, hN₁⟩ := hgω.2.2.2.2 s hs.1
  have hsub : Icc 0 s ⊆ {u : ℝ≥0 | (u : ℝ≥0∞) < ζ ω} := fun u hu =>
    lt_of_le_of_lt (by exact_mod_cast hu.2) hs.1
  obtain ⟨M₁, hM₁⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) s)).exists_bound_of_continuousOn
    ((continuousOn_stateAt_gb hgood hω).mono hsub)
  obtain ⟨M₂, hM₂⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) s)).exists_bound_of_continuousOn
    (hgω.2.1.continuousOn (s := Icc 0 s))
  filter_upwards [eventually_ge_atTop N₁, eventually_gt_atTop ⌈max M₁ M₂⌉₊] with n hn1 hn2
  have hnM : max M₁ M₂ < n := Nat.lt_of_ceil_lt hn2
  have hM1n : M₁ < n := lt_of_le_of_lt (le_max_left _ _) hnM
  have hM2n : M₂ < n := lt_of_le_of_lt (le_max_right _ _) hnM
  rw [← WithTop.coe_le_coe, loc, Sec2.TwoSeed.coe_capTime]
  refine le_min (WithTop.coe_le_coe.2 (hN₁.trans (hTm ω hn1))) (le_min ?_ ?_)
  · simp only [hitD, hω, ↓reduceIte]
    refine Coupling.le_hitBelow fun u _ hlt => ?_
    by_contra hus
    push Not at hus
    have hu' : u ∈ Icc 0 s := ⟨zero_le, hus.le⟩
    refine absurd hlt (not_lt.2 ?_)
    simp only [lev, le_min_iff]
    obtain ⟨hR, hL⟩ := hs.2 u hus.le
    refine ⟨?_, ?_, ?_⟩
    · have := hM₁ u hu'; linarith
    · unfold farR
      split_ifs with h
      · have := hR ⟨mR, h⟩ le_rfl; simp only [Coupling.stateAt]; linarith
      · exact zero_le_one
    · unfold farL
      split_ifs with h
      · have := hL ⟨mL, h⟩ le_rfl; simp only [Coupling.stateAt]; linarith
      · exact zero_le_one
  · by_contra hlt
    push Not at hlt
    obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    have hes : e < s := by rw [← he] at hlt; exact_mod_cast hlt
    obtain ⟨u, hu, hnu⟩ := (MathFin.exitTime_le_iff (continuous_brownG_gb hgood) n e ω).1 (he ▸ le_rfl)
    have hu' : u ∈ Icc 0 s := ⟨zero_le, hu.2.trans hes.le⟩
    have h1 := hM₂ u hu'
    simp only [Sec2.TwoSeed.brownG, hω, ↓reduceIte] at hnu
    rw [Real.norm_eq_abs] at h1
    linarith

/-- **Removing the localization**: a bound on the level integrals uniform in the localization level bounds the
integral over the alive times. -/
theorem lintegral_alive_le (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hGm : MeasurableSet G) (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsGBGood k xL xR ρL ρR W VL VR B ζ T ω)
    (hT : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (T n ω : WithTop ℝ≥0))
    (hTm : ∀ ω, Monotone fun n => T n ω) (hnR : 0 < nR) {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) (t : ℝ)
    {c : ℝ≥0∞}
    (hc : ∀ n, ∫⁻ ω, levelInt φ (loc G W VL VR B ζ T mL mR n g)
      (gapStop G W VR ⟨0, hnR⟩ (xR ⟨0, hnR⟩) (loc G W VL VR B ζ T mL mR n g)) t ω ∂P ≤ c) :
    ∫⁻ ω, (∫⁻ s in Ioc (0 : ℝ) t, {s : ℝ | IsAlive mL mR g W VL VR ζ s.toNNReal ω}.indicator
      (fun s => φ (VR ⟨0, hnR⟩ s.toNNReal ω - W s.toNNReal ω)) s) ∂P ≤ c := by
  refine lintegral_le_of_le_liminf (fun n => measurable_levelInt hE hGm hGc hgood hT _ _ hφ t) ?_ hc
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  filter_upwards [hGae] with ω hω
  unfold levelInt
  refine le_trans (lintegral_mono fun s => ?_) (lintegral_liminf_le fun n =>
    (hφ.comp (continuous_gapStop hgood _ _ ω).measurable).indicator measurableSet_Iic)
  by_cases hs : IsAlive mL mR g W VL VR ζ s.toNNReal ω
  · rw [Set.indicator_of_mem (show s ∈ {s : ℝ | IsAlive mL mR g W VL VR ζ s.toNNReal ω} from hs)]
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [eventually_le_loc hgood hTm hω hs] with n hn
    have hs' : s ≤ (loc G W VL VR B ζ T mL mR n g ω : ℝ) :=
      (Real.le_coe_toNNReal s).trans (by exact_mod_cast hn)
    rw [Set.indicator_of_mem (show s ∈ {s : ℝ | s ≤ loc G W VL VR B ζ T mL mR n g ω} from hs')]
    simp only [gapStop, hω, ↓reduceIte, min_eq_left hn]
    exact le_rfl
  · rw [Set.indicator_of_notMem (show s ∉ {s : ℝ | IsAlive mL mR g W VL VR ζ s.toNNReal ω} from hs)]
    exact bot_le

end Alive

end DS1

end Supp12

end InteractingSLE
