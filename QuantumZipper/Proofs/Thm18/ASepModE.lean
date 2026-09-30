import QuantumZipper.Proofs.Thm18.ASepModD
import QuantumZipper.Proofs.Zipper.XFlowEnergyE1Push

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP (mod E): strip bound and `|log Im|` bounds for a pushforward that shrinks `Im` by `κ`

For `Φ` with `κ Im z ≤ Im Φ(z)` and `‖Φ(z)‖ ≤ Rb` (`Rb ≥ 1`) on the support of `μ`:
`|log Im Φ z| ≤ |log Im z| + |log κ| + log Rb`, hence

* `integrable_log_im_map_scaled`, `integral_log_im_map_scaled_le`: `|log Im|` is integrable for
  `μ.map Φ`, with the integral bound;
* `stripBound_map_scaled`: `μ.map Φ` inherits the strip bound of `μ` with the same exponent.

This generalizes `CoordRegComp.stripBound_map` (which has `κ = 1`, no norm bound). Own elementary
argument.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace QuantumZipper
namespace ASep

theorem abs_log_im_le_scaled {κ Rb : ℝ} (hκ : 0 < κ) (hRb : 1 ≤ Rb) {z w : ℂ} (hz : 0 < z.im)
    (hzw : κ * z.im ≤ w.im) (hw : ‖w‖ ≤ Rb) :
    |Real.log w.im| ≤ |Real.log z.im| + |Real.log κ| + Real.log Rb := by
  have hcw : 0 < κ * z.im := mul_pos hκ hz
  have hw0 : 0 < w.im := hcw.trans_le hzw
  have a1 := Real.log_le_log hcw hzw
  have a2 := Real.log_le_log hw0 ((Complex.im_le_norm w).trans hw)
  have a3 : 0 ≤ Real.log Rb := Real.log_nonneg hRb
  rw [Real.log_mul hκ.ne' hz.ne'] at a1
  refine abs_le.2 ⟨?_, ?_⟩
  · linarith [neg_abs_le (Real.log z.im), neg_abs_le (Real.log κ)]
  · linarith [abs_nonneg (Real.log z.im), abs_nonneg (Real.log κ)]

variable {μ : Measure ℂ} [IsProbabilityMeasure μ] {Φ : ℂ → ℂ} {κ Rb : ℝ}

theorem integrable_log_im_map_scaled (hΦ : Measurable Φ) (hκ : 0 < κ) (hRb : 1 ≤ Rb)
    (hμ : ∀ᵐ z ∂μ, z ∈ H ∧ κ * z.im ≤ (Φ z).im ∧ ‖Φ z‖ ≤ Rb)
    (hl : Integrable (fun z : ℂ => |Real.log z.im|) μ) :
    Integrable (fun z : ℂ => |Real.log z.im|) (μ.map Φ) := by
  have hlm : Measurable fun x : ℂ => |Real.log x.im| :=
    continuous_abs.measurable.comp (Real.measurable_log.comp Complex.measurable_im)
  rw [integrable_map_measure hlm.aestronglyMeasurable hΦ.aemeasurable]
  refine Integrable.mono' (hl.add (integrable_const (|Real.log κ| + Real.log Rb)))
    (hlm.comp hΦ).aestronglyMeasurable (hμ.mono fun z hz => ?_)
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_abs, Pi.add_apply]
  have := abs_log_im_le_scaled hκ hRb hz.1 hz.2.1 hz.2.2
  linarith

theorem integral_log_im_map_scaled_le (hΦ : Measurable Φ) (hκ : 0 < κ) (hRb : 1 ≤ Rb)
    (hμ : ∀ᵐ z ∂μ, z ∈ H ∧ κ * z.im ≤ (Φ z).im ∧ ‖Φ z‖ ≤ Rb)
    (hl : Integrable (fun z : ℂ => |Real.log z.im|) μ) :
    ∫ z, |Real.log z.im| ∂(μ.map Φ) ≤
      ∫ z, |Real.log z.im| ∂μ + (|Real.log κ| + Real.log Rb) := by
  have hlm : Measurable fun x : ℂ => |Real.log x.im| :=
    continuous_abs.measurable.comp (Real.measurable_log.comp Complex.measurable_im)
  rw [integral_map hΦ.aemeasurable hlm.aestronglyMeasurable]
  have hi : Integrable (fun z => |Real.log (Φ z).im|) μ := by
    have := integrable_log_im_map_scaled hΦ hκ hRb hμ hl
    rwa [integrable_map_measure hlm.aestronglyMeasurable hΦ.aemeasurable] at this
  calc ∫ z, |Real.log (Φ z).im| ∂μ
      ≤ ∫ z, (|Real.log z.im| + (|Real.log κ| + Real.log Rb)) ∂μ :=
        integral_mono_ae hi (hl.add (integrable_const _)) (hμ.mono fun z hz => by
          have := abs_log_im_le_scaled hκ hRb hz.1 hz.2.1 hz.2.2
          linarith)
    _ = _ := by rw [integral_add hl (integrable_const _)]; simp

/-- **Strip bound of a pushforward that shrinks `Im` by at most `κ`.** -/
theorem stripBound_map_scaled (hΦ : Measurable Φ) (hκ : 0 < κ) (hRb : 1 ≤ Rb)
    (hμ : ∀ᵐ z ∂μ, z ∈ H ∧ κ * z.im ≤ (Φ z).im ∧ ‖Φ z‖ ≤ Rb)
    (hl : Integrable (fun z : ℂ => |Real.log z.im|) μ) {c γ : ℝ} (hc : 0 ≤ c) (hγ : 0 < γ)
    (hS : CoordReg.StripBound μ c γ) :
    CoordReg.StripBound (μ.map Φ)
      ((1 + |Real.log κ| + Real.log Rb) * (c + (1 + ∫ z, |Real.log z.im| ∂μ)) / κ ^ γ) γ := by
  intro t ht ht1
  set Lk : ℝ := 1 + |Real.log κ| + Real.log Rb with hLk
  have hlogRb : 0 ≤ Real.log Rb := Real.log_nonneg hRb
  have hLk1 : 1 ≤ Lk := by rw [hLk]; linarith [abs_nonneg (Real.log κ)]
  set I : ℝ := ∫ z, |Real.log z.im| ∂μ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun _ => abs_nonneg _
  rw [integral_map hΦ.aemeasurable (CoordRegComp.measurable_stripFun t).aestronglyMeasurable]
  have hint1 : Integrable (fun z : ℂ => 1 + |Real.log z.im|) μ := (integrable_const 1).add hl
  have hmS : ∀ s : ℝ, MeasurableSet {z : ℂ | z.im ≤ s} :=
    fun s => measurableSet_le Complex.measurable_im measurable_const
  have hint2 : Integrable
      ({z : ℂ | z.im ≤ t / κ}.indicator fun z => 1 + |Real.log z.im|) μ :=
    hint1.indicator (hmS _)
  have hpt : ∀ᵐ z ∂μ, {z : ℂ | z.im ≤ t}.indicator (fun z => 1 + |Real.log z.im|) (Φ z) ≤
      Lk * {z : ℂ | z.im ≤ t / κ}.indicator (fun z => 1 + |Real.log z.im|) z := by
    filter_upwards [hμ] with z hz
    by_cases hzt : (Φ z).im ≤ t
    · have hzt' : z.im ≤ t / κ := by
        rw [le_div_iff₀ hκ]; linarith [hz.2.1]
      rw [indicator_of_mem (show Φ z ∈ {z : ℂ | z.im ≤ t} from hzt),
        indicator_of_mem (show z ∈ {z : ℂ | z.im ≤ t / κ} from hzt')]
      have hb := abs_log_im_le_scaled hκ hRb hz.1 hz.2.1 hz.2.2
      have hA := abs_nonneg (Real.log z.im)
      have hK := abs_nonneg (Real.log κ)
      rw [hLk]; nlinarith
    · rw [indicator_of_notMem (show Φ z ∉ {z : ℂ | z.im ≤ t} from hzt)]
      exact mul_nonneg (by linarith) (indicator_nonneg (fun _ _ => by positivity) _)
  have hstep : ∫ z, {z : ℂ | z.im ≤ t}.indicator (fun z => 1 + |Real.log z.im|) (Φ z) ∂μ ≤
      Lk * ∫ z, {z : ℂ | z.im ≤ t / κ}.indicator (fun z => 1 + |Real.log z.im|) z ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg (ae_of_all _ fun z =>
      indicator_nonneg (fun _ _ => by positivity) _) (hint2.const_mul Lk) hpt
  refine hstep.trans ?_
  have htg : 0 < t ^ γ := Real.rpow_pos_of_pos ht _
  have hkg : 0 < κ ^ γ := Real.rpow_pos_of_pos hκ _
  have hgoal : ∀ X : ℝ, X ≤ (c + (1 + I)) * (t ^ γ / κ ^ γ) →
      Lk * X ≤ Lk * (c + (1 + I)) / κ ^ γ * t ^ γ := by
    intro X hX
    calc Lk * X ≤ Lk * ((c + (1 + I)) * (t ^ γ / κ ^ γ)) :=
          mul_le_mul_of_nonneg_left hX (by linarith)
      _ = _ := by field_simp
  apply hgoal
  by_cases hsm : t / κ ≤ 1
  · have h1 := hS (t / κ) (div_pos ht hκ) hsm
    rw [Real.div_rpow ht.le hκ.le] at h1
    have : 0 ≤ (1 + I) * (t ^ γ / κ ^ γ) := by positivity
    nlinarith
  · push Not at hsm
    have h1 : ∫ z, {z : ℂ | z.im ≤ t / κ}.indicator (fun z => 1 + |Real.log z.im|) z ∂μ ≤ 1 + I := by
      calc _ ≤ ∫ z, (1 + |Real.log z.im|) ∂μ :=
            integral_mono_of_nonneg (ae_of_all _ fun z =>
              indicator_nonneg (fun _ _ => by positivity) _) hint1
              (ae_of_all _ fun z => indicator_le_self' (fun _ _ => by positivity) z)
        _ = 1 + I := by rw [integral_add (integrable_const 1) hl]; simp [hI]
    have h2 : 1 ≤ t ^ γ / κ ^ γ := by
      rw [← Real.div_rpow ht.le hκ.le]
      exact Real.one_le_rpow hsm.le hγ.le
    have : 0 ≤ c * (t ^ γ / κ ^ γ) := by positivity
    nlinarith

end ASep
end QuantumZipper
