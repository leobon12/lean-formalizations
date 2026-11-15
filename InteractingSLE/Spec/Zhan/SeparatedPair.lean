/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.SeparatedSeed

/-!
# Transience for a separated pair of marks (`κ ≤ 4`)

Packet PROVE-ZHAN-B3. Astra, *Formalization proofs and dependency audit* (ruling R35), L1416–L1419: "For any
separated pair `p_L < 0 < p_R`, stop the seed law when `R/L = p_R/(−p_L)` … Affine normalization gives exactly that
separated pair." The restart (`exists_codeLaw_traceCodeSet_eq_one`) gives a pair `(−λ, rλ)`, `r = p_R/(−p_L)`, at
which the canonical probability of no transient trace is `0`. The dilation of an evolution of `(p_L, p_R)` by
`c = (−p_L/λ)²` (`IsIntegratedSLEEvolution.dilate`) is an evolution of exactly `(−λ, rλ)`, so by the canonical law
(`measure_eventOf_eq_codeLaw`) its driver almost surely has a transient trace, and dilating the trace back
(`IsGeneratingTrace.dilate`) gives one for the original driver. Every generating trace is that one
(`IsGeneratingTrace.eq_of_le`).

## Main results

* `traceEvent_of_dilPath`: the trace event on `[0, ∞)` is invariant under dilation of the driver.
* `IsIntegratedSLEEvolution.ae_tendsto_norm_trace_pair`: **two-force transience for a separated pair**: for
  `0 < κ ≤ 4`, one mark on each side, `x_L < 0 < x_R`, weights `≥ κ/2 − 2`, almost surely every continuous
  generating trace on `[0, ∞)` tends to `∞`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Zhan

open Sec7.Dilation
open Sec7.RandRestart (TraceEvent traceCodeSet codeLaw)

/-- **The trace event on `[0, ∞)` is invariant under dilation of the driver.** -/
theorem traceEvent_of_dilPath {c : ℝ≥0} (hc : c ≠ 0) {w : ℝ≥0 → ℝ} (h : TraceEvent (dilPath c w) ⊤) :
    TraceEvent w ⊤ := by
  obtain ⟨η, hη, htr⟩ := h
  have hc' : c⁻¹ ≠ 0 := inv_ne_zero hc
  have h2 := hη.dilate hc'
  rw [dilPath_inv_dilPath hc, div_inv_coe hc, ENNReal.top_mul (ENNReal.coe_ne_zero.2 hc)] at h2
  refine ⟨_, h2, fun _ => ?_⟩
  have hs : 0 < (√((c⁻¹ : ℝ≥0) : ℝ))⁻¹ := inv_pos.2 (sqrt_pos_of_ne hc')
  have hlim : Tendsto (fun t : ℝ≥0 => c⁻¹ * t) atTop atTop :=
    tendsto_id.const_mul_atTop (pos_iff_ne_zero.2 hc')
  have e : (fun t : ℝ≥0 => ‖(((√((c⁻¹ : ℝ≥0) : ℝ))⁻¹ : ℝ) : ℂ) * η (c⁻¹ * t)‖) =
      fun t => (√((c⁻¹ : ℝ≥0) : ℝ))⁻¹ * ‖η (c⁻¹ * t)‖ := by
    funext t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  rw [e]
  exact ((htr rfl).comp hlim).const_mul_atTop hs

variable {κ : ℝ} {xL xR ρL ρR : Fin 1 → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **Two-force transience for a separated pair** (`0 < κ ≤ 4`): one mark on each side, `x_L < 0 < x_R`, weights
`≥ κ/2 − 2`. Almost surely every continuous generating trace on `[0, ∞)` tends to `∞`. -/
theorem IsIntegratedSLEEvolution.ae_tendsto_norm_trace_pair (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hρL : κ / 2 - 2 ≤ ρL 0) (hρR : κ / 2 - 2 ≤ ρR 0) (hxL : xL 0 < 0) (hxR : 0 < xR 0)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = xR 0 / -xL 0 := ⟨_, rfl⟩
  have hr0 : 0 < r := hr ▸ div_pos hxR (neg_pos.2 hxL)
  obtain ⟨l, hl, hcode⟩ := exists_codeLaw_traceCodeSet_eq_one hκ hκ4 hρL hρR hr0
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = -xL 0 / l := ⟨_, rfl⟩
  have hs0 : 0 < s := hs ▸ div_pos (neg_pos.2 hxL) hl
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, (c : ℝ) = s ^ 2 := ⟨⟨s ^ 2, sq_nonneg s⟩, rfl⟩
  have hcne : c ≠ 0 := by
    intro h
    rw [h, NNReal.coe_zero] at hc
    exact (pow_pos hs0 2).ne' hc.symm
  have hsqrt : √(c : ℝ) = s := by rw [hc]; exact Real.sqrt_sq hs0.le
  have hxL0 : xL 0 ≠ 0 := hxL.ne
  have hwL : (fun i => (√(c : ℝ))⁻¹ * xL i) = fun _ => -l := funext fun i => by
    rw [Fin.fin_one_eq_zero i, hsqrt, hs]
    field_simp
  have hwR : (fun i => (√(c : ℝ))⁻¹ * xR i) = fun _ => r * l := funext fun i => by
    rw [Fin.fin_one_eq_zero i, hsqrt, hs, hr]
    field_simp
  have hE' : IsIntegratedSLEEvolution κ (fun _ : Fin 1 => -l) (fun _ : Fin 1 => r * l) ρL ρR P
      (dilFiltration c 𝓕) (dilProc c W) (fun i => dilProc c (VL i)) (fun i => dilProc c (VR i))
      (dilProc c B) (fun ω => ζ ω / c) := by
    rw [← hwL, ← hwR]
    exact hE.dilate hcne
  have hsep : ∀ i j, (fun _ : Fin 1 => -l) i < (fun _ : Fin 1 => r * l) j := fun _ _ => by
    have := mul_pos hr0 hl
    linarith
  have e := Sec7.RandRestart.measure_eventOf_eq_codeLaw hκ hsep hE' (Φ := fun w τ => ¬ TraceEvent w τ)
    Sec7.RandRestart.measurableSet_traceCodeSet.compl Sec7.RandRestart.compl_traceCodeSet_iff
    Sec7.RandRestart.not_traceEvent_congr
  rw [hcode] at e
  have hae : ∀ᵐ ω ∂P, TraceEvent (fun t => dilProc c W t ω) (ζ ω / c) := ae_iff.2 e
  have hadm := hasAdmissiblePartialSums_one hρL hρR xL xR
  have hF : IsOrderedForceWord xL xR :=
    ⟨fun i j _ => by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j], fun i => by
      rw [Fin.fin_one_eq_zero i]; exact hxL.le, fun i j _ => by
      rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j], fun i => by
      rw [Fin.fin_one_eq_zero i]; exact hxR.le⟩
  filter_upwards [hae, IsIntegratedSLEEvolution.ae_shiftGood hκ hκ4 hF hadm hE] with ω hω ⟨hζ, hWc, hW0, _⟩ η hη
  rw [hζ, ENNReal.top_div_of_ne_top ENNReal.coe_ne_top] at hω
  obtain ⟨η₀, hη₀, htr⟩ := traceEvent_of_dilPath (w := fun t => W t ω) hcne hω
  have heq : η = η₀ := funext fun t => hη.eq_of_le hη₀ hWc.continuousOn hW0 le_top
  rw [heq]
  exact htr rfl

end InteractingSLE.Zhan
