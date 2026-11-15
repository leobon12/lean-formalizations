/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SwBCat
import InteractingSLE.Foundations.Loewner.YuanCorollary13Finite

/-!
# The vertical slit, and stopped drivers generate traces on `[0, ∞)`

Packet PROVE-GW2-GEOM2. A GW2 piece is stopped at `min t ζ`; its stopped driver is constant afterwards.
Theorem 1.3 (`StagedPiecesRegular`) gives a driver continuous on the closed `[0, min t ζ]` and a
generating trace on that horizon only. Freezing the driver at the stop continues the Loewner chain by the
zero driver, whose trace is the vertical slit `t ↦ 2√t i`. Concatenation with boundary hits allowed
(`LoewnerConcat.isGeneratingTrace_catPath_bdry`) then gives a trace on `[0, ∞)`:

* `slitTrace`, **`isGeneratingTrace_zero_slit`**: the zero driver generates `t ↦ 2√t i` on `[0, ∞)`;
* **`exists_isGeneratingTrace_frozen`**: a driver continuous on `[0, σ]` from `0` with a generating trace
  on `[0, σ]`, frozen at `σ`, generates a trace on `[0, ∞)` agreeing with the given one on `[0, σ]`.

No lifetime or boundary-avoidance hypothesis is used; the stop may be the lifetime itself.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open Sec7.StripSideHeightProb

/-- The vertical slit `t ↦ 2 √t i`, the trace of the zero driver. -/
def slitTrace (t : ℝ≥0) : ℂ := ((2 * Real.sqrt t : ℝ) : ℂ) * I

theorem continuous_slitTrace : Continuous slitTrace :=
  (continuous_ofReal.comp (continuous_const.mul
    (Real.continuous_sqrt.comp NNReal.continuous_coe))).mul continuous_const

theorem slitTrace_im (t : ℝ≥0) : (slitTrace t).im = 2 * Real.sqrt t := by
  simp only [slitTrace, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]

theorem slitTrace_re (t : ℝ≥0) : (slitTrace t).re = 0 := by
  simp only [slitTrace, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, zero_mul, sub_zero]

/-- In `ℍ`, the image of `[0, t]` is the closed vertical slit of height `2√t`. -/
theorem mem_slitTrace_image_iff {t : ℝ≥0} {z : ℂ} (hz : z ∈ H) :
    z ∈ slitTrace '' Icc 0 t ↔ z.re = 0 ∧ z.im ≤ 2 * Real.sqrt t := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨slitTrace_re u, ?_⟩
    rw [slitTrace_im]
    have hut : (u : ℝ) ≤ t := NNReal.coe_le_coe.2 hu.2
    have := Real.sqrt_le_sqrt hut
    linarith
  · rintro ⟨hre, hle⟩
    have hz0 : 0 < z.im := hz
    have hsq : 0 ≤ (z.im / 2) ^ 2 := sq_nonneg _
    refine ⟨((z.im / 2) ^ 2).toNNReal, ⟨zero_le, ?_⟩, ?_⟩
    · rw [Real.toNNReal_le_iff_le_coe]
      have h1 : z.im / 2 ≤ Real.sqrt t := by linarith
      have h2 := pow_le_pow_left₀ (by positivity) h1 2
      rwa [Real.sq_sqrt (NNReal.coe_nonneg t)] at h2
    · have hs : Real.sqrt (((z.im / 2) ^ 2).toNNReal : ℝ) = z.im / 2 := by
        rw [Real.coe_toNNReal _ hsq, Real.sqrt_sq (by positivity)]
      apply Complex.ext
      · rw [slitTrace_re, hre]
      · rw [slitTrace_im, hs]
        ring

/-- **The zero driver generates the vertical slit** on `[0, ∞)`. -/
theorem isGeneratingTrace_zero_slit :
    IsGeneratingTrace (fun _ => (0 : ℝ)) ⊤ slitTrace := by
  refine ⟨by simp [slitTrace], continuous_slitTrace.continuousOn, fun t _ => ?_⟩
  have heq : H \ fwdHull (fun s : ℝ => (fun _ : ℝ≥0 => (0 : ℝ)) s.toNNReal) t =
      H \ slitTrace '' Icc 0 t := by
    ext z
    simp only [Set.mem_sdiff]
    constructor
    · rintro ⟨hz, hK⟩
      exact ⟨hz, fun hA => hK ((YuanCorollary13.mem_fwdHull_zero_iff t.2 hz).2
        ((mem_slitTrace_image_iff hz).1 hA))⟩
    · rintro ⟨hz, hA⟩
      exact ⟨hz, fun hK => hA ((mem_slitTrace_image_iff hz).2
        ((YuanCorollary13.mem_fwdHull_zero_iff t.2 hz).1 hK))⟩
  have hslit : H \ slitTrace '' Icc 0 t = H \ YuanCorollary13.slitSet t := by
    ext z
    simp only [Set.mem_sdiff, YuanCorollary13.slitSet]
    constructor
    · rintro ⟨hz, hA⟩
      exact ⟨hz, fun h => hA ((mem_slitTrace_image_iff hz).2 h.2)⟩
    · rintro ⟨hz, hS⟩
      exact ⟨hz, fun h => hS ⟨hz, (mem_slitTrace_image_iff hz).1 h⟩⟩
  have hpre : IsPreconnected (H \ slitTrace '' Icc 0 t) := by
    rw [hslit]
    exact YuanCorollary13.isPreconnected_H_diff_slitSet t
  have hhigh : ∀ y : ℝ, 2 * Real.sqrt t < y → ((y : ℂ) * I) ∈ H \ slitTrace '' Icc 0 t := by
    intro y hy
    have hyH : ((y : ℂ) * I) ∈ H := by
      change 0 < ((y : ℂ) * I).im
      simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      linarith [Real.sqrt_nonneg (t : ℝ)]
    refine ⟨hyH, fun hA => ?_⟩
    have h := ((mem_slitTrace_image_iff hyH).1 hA).2
    simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero] at h
    linarith
  have hy0 : 2 * Real.sqrt t < 2 * Real.sqrt t + 1 := by linarith
  refine ⟨⟨_, heq ▸ hhigh _ hy0, ?_⟩, ?_⟩
  · rw [heq]
    exact hpre.connectedComponentIn (hhigh _ hy0)
  · rw [heq]
    intro hb
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).1 hb
    set y : ℝ := 2 * Real.sqrt t + |R| + 1 with hy
    have hyt : 2 * Real.sqrt t < y := by rw [hy]; linarith [abs_nonneg R]
    have hm := hR (hhigh y hyt)
    rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith [Real.sqrt_nonneg (t : ℝ)])] at hm
    linarith [le_abs_self R, Real.sqrt_nonneg (t : ℝ)]

/-- **A stopped driver generates a trace on `[0, ∞)`.** If `w` is continuous on `[0, σ]`, starts at `0`
and generates `η` on `[0, σ]`, then the driver frozen at `σ` generates, on `[0, ∞)`, a trace agreeing
with `η` on `[0, σ]` (followed by the image of the vertical slit). -/
theorem exists_isGeneratingTrace_frozen {w : ℝ≥0 → ℝ} {σ : ℝ≥0}
    (hw : ContinuousOn w (Icc 0 σ)) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w σ η) :
    ∃ η' : ℝ≥0 → ℂ, IsGeneratingTrace (fun u => w (min u σ)) ⊤ η' ∧
      ∀ u ≤ σ, η' u = η u := by
  set w₀ : ℝ≥0 → ℝ := fun u => w (min u σ) with hw₀
  have hc : Continuous w₀ :=
    hw.comp_continuous (continuous_id.min continuous_const)
      fun u => ⟨zero_le, min_le_right _ _⟩
  have h00 : w₀ 0 = 0 := by simp only [hw₀, zero_le, min_eq_left, hw0]
  have hη₀ : IsGeneratingTrace w₀ σ η := by
    refine ⟨hη.1, hη.2.1, fun t ht => ?_⟩
    have htσ : (t : ℝ) < σ := NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 ht)
    rw [InteractingSLE.fwdHull_eq_of_eqOn (W := fun s : ℝ => w₀ s.toNNReal)
      (W' := fun s : ℝ => w s.toNNReal) (NNReal.coe_nonneg t) htσ fun r hr => ?_]
    · exact hη.2.2 t ht
    · have hr' : r.toNNReal ≤ σ := Real.toNNReal_le_iff_le_coe.2 hr.2
      simp only [hw₀, min_eq_left hr']
  have hcat := LoewnerConcat.isGeneratingTrace_catPath_bdry hc h00 continuous_const rfl hη₀
    isGeneratingTrace_zero_slit
  have hcw : catPath w₀ σ (fun _ => (0 : ℝ)) = w₀ := by
    funext u
    by_cases hu : u ≤ σ
    · exact catPath_of_le hu
    · have hσu : σ ≤ u := le_of_not_ge hu
      simp only [catPath, hu, ↓reduceIte, add_zero, hw₀, min_self, min_eq_right hσu]
  rw [hcw] at hcat
  refine ⟨LoewnerConcat.joinedTrace w₀ η σ slitTrace, hcat, fun u hu => ?_⟩
  exact LoewnerConcat.joinedTrace_of_le hu

end InteractingSLE.Theorem14.GW2TipSystem.Gm
