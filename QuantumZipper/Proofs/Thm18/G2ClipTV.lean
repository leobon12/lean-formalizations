import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Measurable

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 clipped-shift node: the one-dimensional density step

Sheffield (arXiv:1012.4797, proof of Prop. 5.5, p. 66) writes `h = α φ + h₀` with a Gaussian
coefficient `α` independent of `h₀`; given `h₀` (and the root), the length `L` is a smooth
strictly increasing function `f(α)` of `α`, hence has a conditional density, and shifting `L` by
an amount in `[0, ρ]` that does not depend on `α` costs `o(1)` in total variation as `ρ → 0`.
This file proves the real-analysis content of that sentence:

* `g2clip_L1_translate`: continuity of translation in `L¹(ℝ)` (standard; e.g. Folland, *Real
  Analysis*, Prop. 8.5; proof: approximation by compactly supported continuous functions,
  `Integrable.exists_hasCompactSupport_integral_sub_le`, and Heine–Cantor);
* `g2clip_tv_translate`: a finite measure `ν ≪ Leb` on `ℝ` satisfies
  `|ν E − ν (E − d)| ≤ ε` for all Borel `E` and `|d| < ρ` (the TV form);
* `g2clip_map_ac`: the image of `ν ≪ Leb` under a differentiable `f` with `f' > 0` is
  absolutely continuous (one-dimensional change of variables,
  `lintegral_image_eq_lintegral_abs_deriv_mul`);
* `g2clip_tv_shift`: the two combined: `|ν{f ∈ E} − ν{f + d ∈ E}| ≤ ε` uniformly in `E`, `|d| < ρ`;
* `g2clip_lintegral_tendsto_zero`: dominated convergence for a family of (possibly
  non-measurable) moduli `β n ≤ 1` tending pointwise to `0`, under a finite measure (via
  `exists_measurable_le_lintegral_eq`); this averages the per-sample moduli over the rest of
  the data (`h₀` and the root) in the rooted measure.

Own elementary proofs of textbook facts (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

/-- **Continuity of translation in `L¹(ℝ)`** (Folland, *Real Analysis*, Prop. 8.5). -/
theorem g2clip_L1_translate {G : ℝ → ℝ} (hG : Integrable G) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ d : ℝ, |d| < ρ → ∫ y, |G y - G (y - d)| ≤ ε := by
  obtain ⟨u, hu_supp, hu_int, hu_cont, hu_i⟩ :=
    hG.exists_hasCompactSupport_integral_sub_le (ε := ε / 3) (by positivity)
  set K := Metric.cthickening 1 (tsupport u) with hKdef
  have hK : IsCompact K := hu_supp.isCompact.cthickening
  set V := volume.real K with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  have huc := hu_supp.uniformContinuous_of_continuous hu_cont
  rw [Metric.uniformContinuous_iff] at huc
  obtain ⟨ρ₀, hρ₀, hρ⟩ := huc (ε / 3 / (V + 1)) (by positivity)
  refine ⟨min ρ₀ 1, lt_min hρ₀ one_pos, fun d hd => ?_⟩
  have hd0 : |d| < ρ₀ := hd.trans_le (min_le_left _ _)
  have hd1 : |d| < 1 := hd.trans_le (min_le_right _ _)
  have hud : Integrable fun y => u (y - d) := hu_i.comp_sub_right d
  have hGd : Integrable fun y => G (y - d) := hG.comp_sub_right d
  have hmid : ∫ y, |u y - u (y - d)| ≤ ε / 3 := by
    have hpt : ∀ y, |u y - u (y - d)| ≤ K.indicator (fun _ => ε / 3 / (V + 1)) y := by
      intro y
      by_cases hy : y ∈ K
      · rw [indicator_of_mem hy]
        have h := hρ (a := y) (b := y - d) (by rw [Real.dist_eq]; simpa using hd0)
        rw [Real.dist_eq] at h
        exact h.le
      · rw [indicator_of_notMem hy]
        have h1 : y ∉ tsupport u := fun h => hy (Metric.self_subset_cthickening _ h)
        have h2 : y - d ∉ tsupport u := fun h => hy
          (Metric.mem_cthickening_of_dist_le y (y - d) 1 _ h
            (by rw [Real.dist_eq]; simpa using hd1.le))
        rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]
        simp
    have hKm : MeasurableSet K := Metric.isClosed_cthickening.measurableSet
    have hKfin : volume K < ⊤ := hK.measure_lt_top
    calc ∫ y, |u y - u (y - d)| ≤ ∫ y, K.indicator (fun _ => ε / 3 / (V + 1)) y :=
          integral_mono (hu_i.sub hud).abs
            ((integrableOn_const hKfin.ne).integrable_indicator hKm) hpt
      _ = V * (ε / 3 / (V + 1)) := by
          rw [integral_indicator_const _ hKm, smul_eq_mul]
      _ ≤ ε / 3 := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
  have hshift : ∫ y, |u (y - d) - G (y - d)| = ∫ y, |G y - u y| := by
    have h := integral_sub_right_eq_self (μ := volume) (fun y => |u y - G y|) d
    rw [h]
    exact integral_congr_ae (Eventually.of_forall fun y => abs_sub_comm _ _)
  have hGu : ∫ y, |G y - u y| ≤ ε / 3 := by
    simpa [Real.norm_eq_abs] using hu_int
  have i1 : Integrable fun y => |G y - u y| := (hG.sub hu_i).abs
  have i2 : Integrable fun y => |u y - u (y - d)| := (hu_i.sub hud).abs
  have i3 : Integrable fun y => |u (y - d) - G (y - d)| := (hud.sub hGd).abs
  calc ∫ y, |G y - G (y - d)|
      ≤ ∫ y, (|G y - u y| + |u y - u (y - d)| + |u (y - d) - G (y - d)|) := by
        refine integral_mono (hG.sub hGd).abs ((i1.add i2).add i3) fun y => ?_
        show |G y - G (y - d)| ≤ |G y - u y| + |u y - u (y - d)| + |u (y - d) - G (y - d)|
        calc |G y - G (y - d)| ≤ |G y - u y| + |u y - G (y - d)| := abs_sub_le _ _ _
          _ ≤ |G y - u y| + (|u y - u (y - d)| + |u (y - d) - G (y - d)|) :=
              add_le_add le_rfl (abs_sub_le _ _ _)
          _ = _ := by ring
    _ = (∫ y, |G y - u y|) + (∫ y, |u y - u (y - d)|) + ∫ y, |u (y - d) - G (y - d)| := by
        have h1 := integral_add (i1.add i2) i3
        have h2 := integral_add i1 i2
        simp only [Pi.add_apply] at h1 h2
        rw [h1, h2]
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        rw [hshift]
        exact add_le_add (add_le_add hGu hmid) hGu
    _ = ε := by ring

/-- **Total-variation continuity of translation** for a finite measure `ν ≪ Leb` on `ℝ`. -/
theorem g2clip_tv_translate {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ν ≪ volume) {ε : ℝ}
    (hε : 0 < ε) : ∃ ρ > 0, ∀ d : ℝ, |d| < ρ → ∀ E : Set ℝ, MeasurableSet E →
      |ν.real E - ν.real ((fun x => x + d) ⁻¹' E)| ≤ ε := by
  set G : ℝ → ℝ := fun x => (ν.rnDeriv volume x).toReal with hGdef
  have hGi : Integrable G := Measure.integrable_toReal_rnDeriv
  obtain ⟨ρ, hρ, hL⟩ := g2clip_L1_translate hGi hε
  refine ⟨ρ, hρ, fun d hd E hE => ?_⟩
  have hrep : ∀ S : Set ℝ, MeasurableSet S → ν.real S = ∫ x, S.indicator G x := fun S hS => by
    rw [integral_indicator hS]
    exact (Measure.setIntegral_toReal_rnDeriv' hν hS).symm
  have hpre : MeasurableSet ((fun x => x + d) ⁻¹' E) := (measurable_add_const d) hE
  have hGd : Integrable fun y => G (y - d) := hGi.comp_sub_right d
  have e2 : ∫ x, ((fun x => x + d) ⁻¹' E).indicator G x =
      ∫ y, E.indicator (fun y => G (y - d)) y := by
    rw [← integral_add_right_eq_self (fun y => E.indicator (fun y => G (y - d)) y) d]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases h : x + d ∈ E
    · simp [indicator, h]
    · simp [indicator, h]
  rw [hrep E hE, hrep _ hpre, e2, ← integral_sub (hGi.indicator hE) (hGd.indicator hE),
    ← indicator_sub]
  refine (abs_integral_le_integral_abs).trans ?_
  refine (integral_mono ((hGi.sub hGd).indicator hE).abs (hGi.sub hGd).abs fun y => ?_).trans
    (hL d hd)
  by_cases h : y ∈ E
  · simp [indicator_of_mem h]
  · simp [indicator_of_notMem h]

/-- **Absolute continuity of an image law** under a differentiable `f` with `f' > 0`. -/
theorem g2clip_map_ac {ν : Measure ℝ} (hν : ν ≪ volume) {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hpos : ∀ x, 0 < deriv f x) : ν.map f ≪ volume := by
  refine Measure.AbsolutelyContinuous.mk fun E hE hE0 => ?_
  rw [Measure.map_apply hf.continuous.measurable hE]
  refine hν ?_
  set s := f ⁻¹' E
  have hs : MeasurableSet s := hf.continuous.measurable hE
  have hinj : InjOn f s := (strictMono_of_deriv_pos hpos).injective.injOn
  have key := lintegral_image_eq_lintegral_abs_deriv_mul hs
    (fun x _ => (hf x).hasDerivAt.hasDerivWithinAt) hinj (fun _ => (1 : ℝ≥0∞))
  have himg : volume (f '' s) = 0 := measure_mono_null (image_preimage_subset f E) hE0
  rw [setLIntegral_one, himg] at key
  have hmeas : Measurable fun x => ENNReal.ofReal |deriv f x| * 1 :=
    (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (measurable_deriv f))).mul_const 1
  have hae := (lintegral_eq_zero_iff hmeas).1 key.symm
  rw [Filter.EventuallyEq, ae_restrict_iff' hs] at hae
  have : ∀ᵐ x ∂volume, x ∉ s := by
    filter_upwards [hae] with x hx hxs
    have h1 := hx hxs
    simp only [mul_one, Pi.zero_apply, ENNReal.ofReal_eq_zero] at h1
    exact absurd h1 (not_le.2 (abs_pos.2 (hpos x).ne'))
  rw [ae_iff] at this
  simpa using this

/-- **The shift estimate for a monotone function of an absolutely continuous variable**: if
`α ∼ ν ≪ Leb` and `L = f(α)` with `f' > 0`, then `|P(L ∈ E) − P(L + d ∈ E)| ≤ ε` for all Borel
`E` and all `|d| < ρ`. -/
theorem g2clip_tv_shift {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ν ≪ volume) {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hpos : ∀ x, 0 < deriv f x) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ d : ℝ, |d| < ρ → ∀ E : Set ℝ, MeasurableSet E →
      |ν.real (f ⁻¹' E) - ν.real ((fun a => f a + d) ⁻¹' E)| ≤ ε := by
  have hm := hf.continuous.measurable
  obtain ⟨ρ, hρ, h⟩ := g2clip_tv_translate (ν := ν.map f) (g2clip_map_ac hν hf hpos) hε
  refine ⟨ρ, hρ, fun d hd E hE => ?_⟩
  have := h d hd E hE
  rwa [map_measureReal_apply hm hE, map_measureReal_apply hm ((measurable_add_const d) hE)]
    at this

/-- **Dominated convergence for non-measurable moduli**: if `β n ≤ 1` and `β n ξ → 0` for every
`ξ`, then `∫⁻ β n ∂Q → 0` for a finite measure `Q` (the lower integral `∫⁻` of mathlib). -/
theorem g2clip_lintegral_tendsto_zero {Ξ : Type*} [MeasurableSpace Ξ] (Q : Measure Ξ)
    [IsFiniteMeasure Q] (β : ℕ → Ξ → ℝ≥0∞) (hb : ∀ n ξ, β n ξ ≤ 1)
    (hlim : ∀ ξ, Tendsto (fun n => β n ξ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ ξ, β n ξ ∂Q) atTop (𝓝 0) := by
  choose ψ hψm hψle hψeq using fun n => exists_measurable_le_lintegral_eq Q (β n)
  simp_rw [hψeq]
  have h0 : Tendsto (fun n => ∫⁻ ξ, ψ n ξ ∂Q) atTop (𝓝 (∫⁻ _ξ, 0 ∂Q)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => 1) hψm
      (fun n => Eventually.of_forall fun ξ => (hψle n ξ).trans (hb n ξ))
      (by simp [measure_ne_top]) (Eventually.of_forall fun ξ => ?_)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hlim ξ)
      (fun n => bot_le) (fun n => hψle n ξ)
  simpa using h0

end Thm18Asm
end QuantumZipper
