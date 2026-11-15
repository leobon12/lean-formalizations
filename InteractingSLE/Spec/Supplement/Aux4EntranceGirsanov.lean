/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.GirsanovDensity

/-!
# Aux. lemma 4, II: the separated drifts over a short entrance interval (total variation)

Packet PROVE-T14-DS3. In Aux. lemma 4 (spec pp. 29–30) the separated marks are added by a Girsanov change of measure
with a bounded drift `D`, `|D| ≤ C`: "if `|D^{(n)}| ≤ C` and `p > 1`, then `sup_n E Z_n^p ≤ exp{p(p − 1)C²T/(2κ)}`". For
the restart of Lemma DS3 at the small time `τ_r ≤ r²/16` only a short interval is needed, and the change of measure is
then close to the identity in total variation, uniformly in the weights:

* `integral_sq_doleansDensity_le`: `E Z_t² ≤ exp(C² t)` for the Doléans density of a drift bounded by `C` (Fatou from the
  landed dyadic approximations `Girsanov.sq_integral_approxDensity_le`);
* `integral_abs_one_sub_doleansDensity_le`: `E |1 − Z_t| ≤ e` whenever `exp(C² t) ≤ 1 + e²`
  (from `|x| ≤ x²/(2e) + e/2` and `E Z_t = 1`);
* **`lintegral_le_girsanov_add`**, **`lintegral_girsanov_le_add`**: for a `𝓕_t`-measurable `h` with values in `[0, 1]`
  and `t ≤ T`, `|∫ h dP − ∫ h dQ_T| ≤ e` with `Q_T = Z_T · P` (layer cake and the martingale property of `Z`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp12

namespace Aux4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {B θ : ℝ≥0 → Ω → ℝ} [hB : IsFilteredPreBrownian B 𝓕 P]

/-- **`E Z_t² ≤ exp(C² t)`.** -/
theorem integral_sq_doleansDensity_le (hθm : StronglyAdapted 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) (t : ℝ≥0) :
    ∫ ω, doleansDensity P 𝓕 B θ t ω ^ 2 ∂P ≤ Real.exp (C ^ 2 * (t : ℝ)) := by
  set c := ⌈(t : ℝ)⌉₊
  have htc : t ≤ (c : ℝ≥0) := by simpa using le_shift t 0
  obtain ⟨ms, hms⟩ := exists_subseq_ae_tendsto_approxDensity (B := B) hθm hθb hθreg htc id tendsto_id
  have hint : ∀ n, Integrable (fun ω => approxDensity B θ (n + c) t ω ^ 2) P := fun n =>
    (memLp_approxDensity (B := B) (P := P) hθm hθb htc n).integrable_sq
  have hfatou : ∫⁻ ω, ENNReal.ofReal (doleansDensity P 𝓕 B θ t ω ^ 2) ∂P ≤
      liminf (fun k => ∫⁻ ω, ENNReal.ofReal (approxDensity B θ (ms k + c) t ω ^ 2) ∂P) atTop := by
    calc ∫⁻ ω, ENNReal.ofReal (doleansDensity P 𝓕 B θ t ω ^ 2) ∂P
        = ∫⁻ ω, liminf (fun k => ENNReal.ofReal (approxDensity B θ (ms k + c) t ω ^ 2)) atTop ∂P := by
          refine lintegral_congr_ae (hms.mono fun ω h => ?_)
          exact ((ENNReal.continuous_ofReal.tendsto _).comp (h.1.pow 2)).liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le fun k =>
          ((measurable_approxDensity (B := B) (P := P) hθm hθb _ t).pow_const 2).ennreal_ofReal
  have hbd : ∀ k, ∫⁻ ω, ENNReal.ofReal (approxDensity B θ (ms k + c) t ω ^ 2) ∂P ≤
      ENNReal.ofReal (Real.exp (C ^ 2 * (t : ℝ))) := fun k => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hint _) (Eventually.of_forall fun ω => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (sq_integral_approxDensity_le (B := B) hθm hθb htc _)
  have hle : ∫⁻ ω, ENNReal.ofReal (doleansDensity P 𝓕 B θ t ω ^ 2) ∂P ≤
      ENNReal.ofReal (Real.exp (C ^ 2 * (t : ℝ))) :=
    hfatou.trans (liminf_le_of_le (by isBoundedDefault) fun b hb => by
      obtain ⟨k, hk⟩ := hb.exists
      exact hk.trans (hbd k))
  have hZ2 : Integrable (fun ω => doleansDensity P 𝓕 B θ t ω ^ 2) P :=
    (memLp_doleansDensity (B := B) hθm hθb hθreg t).integrable_sq
  rw [← ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le, ofReal_integral_eq_lintegral_ofReal hZ2
    (Eventually.of_forall fun ω => sq_nonneg _)]
  exact hle

/-- **`E |1 − Z_t| ≤ e`** when `exp(C² t) ≤ 1 + e²`. -/
theorem integral_abs_one_sub_doleansDensity_le (hθm : StronglyAdapted 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) (t : ℝ≥0) {e : ℝ} (he : 0 < e)
    (hCe : Real.exp (C ^ 2 * (t : ℝ)) ≤ 1 + e ^ 2) :
    ∫ ω, |1 - doleansDensity P 𝓕 B θ t ω| ∂P ≤ e := by
  have hZ := (memLp_doleansDensity (B := B) hθm hθb hθreg t)
  have hZ1 : Integrable (doleansDensity P 𝓕 B θ t) P := hZ.integrable one_le_two
  have hZ2 : Integrable (fun ω => doleansDensity P 𝓕 B θ t ω ^ 2) P := hZ.integrable_sq
  have hE1 := integral_doleansDensity (B := B) hθm hθb hθreg t
  have hE2 := integral_sq_doleansDensity_le (B := B) hθm hθb hθreg t
  -- `|x| ≤ x² / (2e) + e / 2`
  have hpt : ∀ ω, |1 - doleansDensity P 𝓕 B θ t ω| ≤
      (1 - 2 * doleansDensity P 𝓕 B θ t ω + doleansDensity P 𝓕 B θ t ω ^ 2) / (2 * e) + e / 2 := by
    intro ω
    set z := doleansDensity P 𝓕 B θ t ω
    have h1 : (1 - 2 * z + z ^ 2) = (1 - z) ^ 2 := by ring
    rw [h1, div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (|1 - z| - e), sq_abs (1 - z), abs_nonneg (1 - z)]
  have hint : Integrable (fun ω => (1 - 2 * doleansDensity P 𝓕 B θ t ω +
      doleansDensity P 𝓕 B θ t ω ^ 2) / (2 * e) + e / 2) P :=
    ((((integrable_const 1).sub (hZ1.const_mul 2)).add hZ2).div_const _).add (integrable_const _)
  calc ∫ ω, |1 - doleansDensity P 𝓕 B θ t ω| ∂P
      ≤ ∫ ω, ((1 - 2 * doleansDensity P 𝓕 B θ t ω + doleansDensity P 𝓕 B θ t ω ^ 2) / (2 * e) + e / 2) ∂P :=
        integral_mono ((integrable_const 1).sub hZ1).abs hint hpt
    _ = (1 - 2 * 1 + ∫ ω, doleansDensity P 𝓕 B θ t ω ^ 2 ∂P) / (2 * e) + e / 2 := by
        have i0 : Integrable (fun ω => 1 - 2 * doleansDensity P 𝓕 B θ t ω) P :=
          (integrable_const 1).sub (hZ1.const_mul 2)
        have i1 : Integrable (fun ω => 1 - 2 * doleansDensity P 𝓕 B θ t ω +
            doleansDensity P 𝓕 B θ t ω ^ 2) P := i0.add hZ2
        have i2 : Integrable (fun ω => (1 - 2 * doleansDensity P 𝓕 B θ t ω +
            doleansDensity P 𝓕 B θ t ω ^ 2) / (2 * e)) P := i1.div_const _
        have e1 : ∫ ω, (1 - 2 * doleansDensity P 𝓕 B θ t ω) ∂P = 1 - 2 * 1 := by
          rw [integral_sub (integrable_const 1) (hZ1.const_mul 2), integral_const_mul, hE1]
          simp
        rw [integral_add i2 (integrable_const _), integral_div, integral_add i0 hZ2, e1]
        simp
    _ ≤ (1 - 2 * 1 + (1 + e ^ 2)) / (2 * e) + e / 2 := by gcongr; exact hE2.trans hCe
    _ = e := by field_simp; ring

/-- **Total variation on `𝓕_t`**: `P F ≤ Q_T F + e` and `Q_T F ≤ P F + e` for `F ∈ 𝓕_t`, `t ≤ T`. -/
theorem measure_le_girsanov_add (hθm : StronglyAdapted 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) {t T : ℝ≥0} (htT : t ≤ T) {e : ℝ} (he : 0 < e)
    (hCe : Real.exp (C ^ 2 * (t : ℝ)) ≤ 1 + e ^ 2) {F : Set Ω} (hF : MeasurableSet[𝓕 t] F) :
    P F ≤ girsanovMeasure P 𝓕 B θ T F + ENNReal.ofReal e ∧
      girsanovMeasure P 𝓕 B θ T F ≤ P F + ENNReal.ofReal e := by
  have hFm : MeasurableSet F := 𝓕.le t _ hF
  have hZ := memLp_doleansDensity (B := B) hθm hθb hθreg
  have hQ : girsanovMeasure P 𝓕 B θ T F = ENNReal.ofReal (∫ ω in F, doleansDensity P 𝓕 B θ t ω ∂P) := by
    rw [girsanovMeasure, withDensity_apply _ hFm, ← ofReal_integral_eq_lintegral_ofReal
      ((hZ T).integrable one_le_two).integrableOn (Eventually.of_forall fun ω => (doleansDensity_pos T ω).le),
      setIntegral_doleansDensity_eq (B := B) hθm hθb hθreg htT hF]
  have hP : P F = ENNReal.ofReal (∫ ω in F, (1 : ℝ) ∂P) := by
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hint : Integrable (doleansDensity P 𝓕 B θ t) P := (hZ t).integrable one_le_two
  have hdiff : |∫ ω in F, (1 : ℝ) ∂P - ∫ ω in F, doleansDensity P 𝓕 B θ t ω ∂P| ≤ e := by
    rw [← integral_sub (integrable_const _).integrableOn hint.integrableOn]
    refine (abs_integral_le_integral_abs).trans ?_
    refine (setIntegral_le_integral ((integrable_const _).sub hint).abs
      (Eventually.of_forall fun ω => abs_nonneg _)).trans ?_
    exact integral_abs_one_sub_doleansDensity_le (B := B) hθm hθb hθreg t he hCe
  rw [abs_le] at hdiff
  have hZF : 0 ≤ ∫ ω in F, doleansDensity P 𝓕 B θ t ω ∂P :=
    setIntegral_nonneg hFm fun ω _ => (doleansDensity_pos t ω).le
  have h1F : 0 ≤ ∫ ω in F, (1 : ℝ) ∂P := setIntegral_nonneg hFm fun _ _ => zero_le_one
  rw [hQ, hP]
  constructor
  · rw [← ENNReal.ofReal_add hZF he.le]; exact ENNReal.ofReal_le_ofReal (by linarith)
  · rw [← ENNReal.ofReal_add h1F he.le]; exact ENNReal.ofReal_le_ofReal (by linarith)

/-- Layer cake for a `[0, 1]`-valued function, levels restricted to `(0, 1)`. -/
theorem lintegral_eq_lintegral_levels {μ : Measure Ω} {h : Ω → ℝ≥0∞} (hm : Measurable h) (h1 : ∀ ω, h ω ≤ 1) :
    ∫⁻ ω, h ω ∂μ = ∫⁻ s in Ioi 0, μ {ω | s < (h ω).toReal} := by
  have e : ∀ ω, h ω = ENNReal.ofReal ((h ω).toReal) := fun ω =>
    (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (h1 ω))).symm
  rw [lintegral_congr e]
  exact lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall fun ω => ENNReal.toReal_nonneg)
    hm.ennreal_toReal.aemeasurable

/-- **Total variation for `[0, 1]`-valued `𝓕_t`-measurable functions.** -/
theorem lintegral_le_girsanov_add (hθm : StronglyAdapted 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) {t T : ℝ≥0} (htT : t ≤ T) {e : ℝ} (he : 0 < e)
    (hCe : Real.exp (C ^ 2 * (t : ℝ)) ≤ 1 + e ^ 2) {h : Ω → ℝ≥0∞} (hm : Measurable[𝓕 t] h)
    (h1 : ∀ ω, h ω ≤ 1) :
    ∫⁻ ω, h ω ∂P ≤ ∫⁻ ω, h ω ∂(girsanovMeasure P 𝓕 B θ T) + ENNReal.ofReal e ∧
      ∫⁻ ω, h ω ∂(girsanovMeasure P 𝓕 B θ T) ≤ ∫⁻ ω, h ω ∂P + ENNReal.ofReal e := by
  have hm' : Measurable h := hm.mono (𝓕.le t) le_rfl
  have hlev : ∀ s : ℝ, MeasurableSet[𝓕 t] {ω | s < (h ω).toReal} := fun s =>
    measurableSet_lt measurable_const hm.ennreal_toReal
  have hempty : ∀ s : ℝ, 1 ≤ s → {ω | s < (h ω).toReal} = ∅ := fun s hs => by
    ext ω
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
    exact (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h1 ω)).trans hs
  set ind : ℝ → ℝ≥0∞ := (Iio (1 : ℝ)).indicator fun _ => ENNReal.ofReal e with hind
  have hind_int : ∫⁻ s in Ioi 0, ind s = ENNReal.ofReal e := by
    rw [hind, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      setLIntegral_const, Iio_inter_Ioi, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one]
  have key : ∀ (μ ν : Measure Ω), (∀ s : ℝ, 0 < s → s < 1 → μ {ω | s < (h ω).toReal} ≤
      ν {ω | s < (h ω).toReal} + ENNReal.ofReal e) →
      ∫⁻ ω, h ω ∂μ ≤ ∫⁻ ω, h ω ∂ν + ENNReal.ofReal e := by
    intro μ ν hμν
    rw [lintegral_eq_lintegral_levels hm' h1, lintegral_eq_lintegral_levels hm' h1, ← hind_int,
      ← lintegral_add_right _ (measurable_const.indicator measurableSet_Iio)]
    refine setLIntegral_mono' measurableSet_Ioi fun s hs => ?_
    by_cases hs1 : s < 1
    · simp only [indicator_of_mem (mem_Iio.2 hs1)]
      exact hμν s hs hs1
    · rw [hempty s (not_lt.1 hs1), measure_empty]; exact zero_le
  exact ⟨key _ _ fun s _ _ => (measure_le_girsanov_add (B := B) hθm hθb hθreg htT he hCe (hlev s)).1,
    key _ _ fun s _ _ => (measure_le_girsanov_add (B := B) hθm hθb hθreg htT he hCe (hlev s)).2⟩

end Aux4

end Supp12

end InteractingSLE
