/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtJHit

/-!
# A two-seed driver does not pause at a level

Packet PROVE-LOCEXT-J, input (U) of Aux. lemma 54. For an integrated two-seed evolution `SLE_κ(ρ_−; ρ_+)` from `0⁻, 0⁺`
with weights `> −2`, almost surely the driver does not pause at any fixed level `a > 0`
(`ae_not_isLevelPause_twoSeed`): it never reaches `|W| ≥ a` and then stays `|W| ≤ a` for a positive time.

The proof uses no Brownian oscillation estimate. Let `g(a)` be the probability of a pause at level `a`.

* **Scaling**: the dilation `t ↦ (√c)⁻¹ W_{ct}` of the evolution is again a two-seed evolution with the same weights
  (`IsIntegratedSLEEvolution.dilate_zero`), so its dyadic code has the same law (`Assembly3.map_stCode_eq_twoSeed`); the
  dilated driver pauses at `a` iff the driver pauses at `√c · a` (`isLevelPause_dilPath_iff`). Hence `g` is constant on
  `(0, ∞)`.
* **Fubini**: every path pauses at countably many levels (`countable_setOf_isLevelPause`), so the set of pairs
  (level, code) with a pause is null for `Lebesgue ⊗ law(code)`; integrating in the other order gives
  `∫_{(0,∞)} g = 0`, so the constant `g` vanishes.

The generic facts used here (`ae_stCode_mem_gUC`, `ae_dec_gDrv_stCode`): for an evolution with infinite lifetime, the
decoded driver of its dyadic code is its driver.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open Coupling Sec2.Assembly Sec2.Assembly2 Sec2.Assembly3

/-! ### The code of an evolution with infinite lifetime -/

section CodeOf

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

theorem univ_eq_setOf_lt_top : (univ : Set ℝ≥0) = {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} :=
  (eq_univ_of_forall fun _ => ENNReal.coe_lt_top).symm

/-- On a path with infinite lifetime the driving state is continuous. -/
theorem continuous_of_isIntegratedSLEPath_top {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ⊤) :
    Continuous w ∧ (∀ i, Continuous (vL i)) ∧ ∀ j, Continuous (vR j) := by
  have hp' := hp.isSLEPathUpTo (le_refl ⊤)
  refine ⟨continuousOn_univ.1 (univ_eq_setOf_lt_top ▸ hp'.continuousOn_w), fun i =>
    continuousOn_univ.1 (univ_eq_setOf_lt_top ▸ hp'.continuousOn_vL i), fun j =>
    continuousOn_univ.1 (univ_eq_setOf_lt_top ▸ hp'.continuousOn_vR j)⟩

/-- The driver code of the dyadic code is the encoded killed driver. -/
theorem gDrv_stCode (ω : Ω) : gDrv (stCode ζ W VL VR B ω) = enc fun t => Girsanov.killed ζ W t ω := rfl

theorem gL_stCode (i : Fin nL) (ω : Ω) :
    gL i (stCode ζ W VL VR B ω) = enc fun t => Girsanov.killed ζ (VL i) t ω := rfl

theorem gR_stCode (j : Fin nR) (ω : Ω) :
    gR j (stCode ζ W VL VR B ω) = enc fun t => Girsanov.killed ζ (VR j) t ω := rfl

theorem killed_eq_of_top {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hω : ζ ω = ⊤) : (fun t => Girsanov.killed ζ X t ω) = (X · ω) :=
  funext fun _ => Girsanov.killed_of_lt (by rw [hω]; exact ENNReal.coe_lt_top)

/-- **The code of a path with infinite lifetime decodes to the path**: the driver code is uniformly continuous and
decodes to the driver, and the mark codes decode to the marks. -/
theorem stCode_decode_of_top {ω : Ω} (hω : ζ ω = ⊤)
    (hp : IsIntegratedSLEPath a xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) (ζ ω)) :
    stCode ζ W VL VR B ω ∈ gUC ∧ dec (gDrv (stCode ζ W VL VR B ω)) = (W · ω) ∧
      (∀ i, dec (gL i (stCode ζ W VL VR B ω)) = (VL i · ω)) ∧
      ∀ j, dec (gR j (stCode ζ W VL VR B ω)) = (VR j · ω) := by
  rw [hω] at hp
  obtain ⟨hW, hVL, hVR⟩ := continuous_of_isIntegratedSLEPath_top hp
  refine ⟨fun N => ?_, ?_, fun i => ?_, fun j => ?_⟩
  · rw [gDrv_stCode, killed_eq_of_top hω]
    exact uc_enc_of_continuous hW N
  · rw [gDrv_stCode, killed_eq_of_top hω]
    exact dec_enc_of_continuous hW
  · rw [gL_stCode, killed_eq_of_top hω]
    exact dec_enc_of_continuous (hVL i)
  · rw [gR_stCode, killed_eq_of_top hω]
    exact dec_enc_of_continuous (hVR j)

theorem measurable_stCode_of_evolution (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    Measurable (stCode ζ W VL VR B) :=
  measurable_stCode hE.2.1 hE.2.2.1 hE.2.2.2.1 fun t => (hE.1.2.1 t).mono (𝓕.le t) le_rfl

/-- **The probability of a pause is the code-law measure of the pause section.** -/
theorem measure_isLevelPause_eq (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (b : ℝ) :
    P {ω | IsLevelPause b (W · ω)} = (P.map (stCode ζ W VL VR B)) ((fun c => (b, c)) ⁻¹' pauseSet) := by
  have hm := measurable_stCode_of_evolution hE
  rw [Measure.map_apply hm (measurable_prodMk_left measurableSet_pauseSet)]
  refine measure_congr ?_
  filter_upwards [hζ, hE.2.2.2.2] with ω hω hp
  obtain ⟨h1, h2, -, -⟩ := stCode_decode_of_top hω hp
  change (IsLevelPause b (W · ω)) = (stCode ζ W VL VR B ω ∈ gUC ∧ IsLevelPause b (dec (gDrv (stCode ζ W VL VR B ω))))
  rw [h2]
  exact propext ⟨fun h => ⟨h1, h⟩, fun h => h.2⟩

end CodeOf

/-! ### Two-seed drivers do not pause -/

section TwoSeed

variable {κ ρa ρb : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The pause probability of a two-seed driver is the same at every positive level.** -/
theorem measure_isLevelPause_twoSeed_eq (hκ : 0 < κ) (hρa : -2 < ρa) (hρb : -2 < ρb)
    (hE : IsIntegratedSLEEvolution κ (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0) (fun _ => ρa) (fun _ => ρb) P 𝓕
      W VL VR B ζ) {c : ℝ≥0} (hc : c ≠ 0) (b : ℝ) :
    P {ω | IsLevelPause b (W · ω)} = P {ω | IsLevelPause (√(c : ℝ) * b) (W · ω)} := by
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := ae_lifetime_eq_top_twoSeed hκ hE hρa hρb
  have hE' := hE.dilate_zero hc
  have hζ' : ∀ᵐ ω ∂P, ζ ω / c = ⊤ := by
    filter_upwards [hζ] with ω hω
    rw [hω]
    exact ENNReal.top_div_of_ne_top ENNReal.coe_ne_top
  have hlaw := map_stCode_eq_twoSeed hκ hρa hρb hE' hE
  rw [measure_isLevelPause_eq hE hζ, ← hlaw, ← measure_isLevelPause_eq hE' hζ']
  congr 1
  ext ω
  exact isLevelPause_dilPath_iff (w := fun t => W t ω) hc b

/-- **A two-seed driver almost surely does not pause at a positive level.** -/
theorem ae_not_isLevelPause_twoSeed (hκ : 0 < κ) (hρa : -2 < ρa) (hρb : -2 < ρb)
    (hE : IsIntegratedSLEEvolution κ (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0) (fun _ => ρa) (fun _ => ρb) P 𝓕
      W VL VR B ζ) {b : ℝ} (hb : 0 < b) : ∀ᵐ ω ∂P, ¬ IsLevelPause b (W · ω) := by
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := ae_lifetime_eq_top_twoSeed hκ hE hρa hρb
  set μ : Measure (GCode 1 1) := P.map (stCode ζ W VL VR B) with hμ
  have hμp : IsProbabilityMeasure μ := inferInstance
  set g : ℝ → ℝ≥0∞ := fun x => μ ((fun c => (x, c)) ⁻¹' pauseSet) with hg
  -- `g` is constant on `(0, ∞)`
  have hconst : ∀ x, 0 < x → g x = g b := by
    intro x hx
    have hc : ((b / x) ^ 2).toNNReal ≠ 0 := by
      rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
    have hsq : √((((b / x) ^ 2).toNNReal : ℝ≥0) : ℝ) * x = b := by
      rw [Real.coe_toNNReal _ (by positivity), Real.sqrt_sq (by positivity)]
      field_simp
    have h1 := measure_isLevelPause_twoSeed_eq hκ hρa hρb hE hc x
    rw [hsq, measure_isLevelPause_eq hE hζ, measure_isLevelPause_eq hE hζ] at h1
    exact h1
  -- Fubini on `(0, ∞) × codes`
  set ν : Measure ℝ := volume.restrict (Ioi 0) with hν
  have hP : MeasurableSet (pauseSet (nL := 1) (nR := 1)) := measurableSet_pauseSet
  have h0 : (ν.prod μ) pauseSet = 0 := by
    rw [Measure.prod_apply_symm hP]
    refine (lintegral_congr fun c => ?_).trans lintegral_zero
    refine measure_mono_null (fun x hx => ?_) ((countable_setOf_isLevelPause (dec (gDrv c))).measure_zero ν)
    exact hx.2
  have h1 : (ν.prod μ) pauseSet = ∫⁻ x in Ioi 0, g x := by
    rw [Measure.prod_apply hP]
  have h2 : ∫⁻ x in Ioi (0 : ℝ), g x = g b * volume (Ioi (0 : ℝ)) := by
    rw [← setLIntegral_const]
    exact setLIntegral_congr_fun measurableSet_Ioi fun x hx => hconst x hx
  rw [h0, h2, Real.volume_Ioi, ENNReal.mul_top'] at h1
  have hgb : g b = 0 := by
    by_contra hne
    simp [hne] at h1
  rw [ae_iff]
  simp only [not_not]
  rw [measure_isLevelPause_eq hE hζ]
  exact hgb

end TwoSeed

end LocalExt

end InteractingSLE
