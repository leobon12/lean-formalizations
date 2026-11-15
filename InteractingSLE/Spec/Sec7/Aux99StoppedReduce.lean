/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Continuity2OneForce

/-!
# Aux. lemma 99 stopped from complete one-mark words

Packet PROVE-ZHAN-A8. The stopped assertion of Aux. lemma 99 (`Sec7.Aux99StoppedStatement κ`: one right mark at
`x > 0`, any weight, a trace up to and including the first swallow, closed there when the swallow is before the
lifetime, transient if there is no swallow) follows from completeness of the one-mark word (a continuous generating
trace up to and including the lifetime, transient on infinite lifetime):

* the trace restricts to `[0, τ]`, `τ = firstMeet ≤ ζ` (`IsGeneratingTrace.mono_horizon`);
* `τ = ∞` forces `ζ = ∞`, hence transience;
* at `τ < ζ` the closed form is PROVE-SEC7-C3's `IsGeneratingTrace.isGeneratingTraceIcc` (the driver is continuous
  before `ζ` and starts at `0`).

Completeness of the one-mark word is, for `ρ > −2`, Wang–Wu's Lemma 5.1 from the seed word
(`WangWu.Lemma51.isCompleteForceWord_oneRight_of_seed`), and for `ρ ≤ −2` the named statement
`WangWu.Lemma51.OneRightNonAdmissibleStatement κ`. Hence (`aux99StoppedStatement_of_seed_of_nonAdmissible`):

  `seed completeness (ρ > −2) ∧ OneRightNonAdmissibleStatement κ → Aux99StoppedStatement κ`,

the converse of the landed `oneRightNonAdmissibleStatement_of_stopped` up to the seed theorem.

Also: complete words are invariant under dilation of the positions (`LP.IsCompleteForceWord.dilate`), and the trace
event under dilation of the driver (`traceEvent_dilPath`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

open Sec7.Dilation Sec7.RandRestart

/-! ### Dilation of the trace event and of complete words -/

theorem div_coe_eq_top {ζ : ℝ≥0∞} {c : ℝ≥0} (hc : c ≠ 0) (h : ζ / c = ⊤) : ζ = ⊤ := by
  rcases ENNReal.div_eq_top.1 h with h' | h'
  · exact absurd h'.2 (ENNReal.coe_ne_zero.2 hc)
  · exact h'.1

/-- **The trace event under dilation of the driver.** -/
theorem traceEvent_dilPath {c : ℝ≥0} (hc : c ≠ 0) {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (h : TraceEvent w ζ) :
    TraceEvent (dilPath c w) (ζ / c) := by
  obtain ⟨η, hη, htr⟩ := h
  exact ⟨_, hη.dilate hc, fun h => ZhanGT4.tendsto_norm_dilate hc (htr (div_coe_eq_top hc h))⟩

theorem div_coe_div_coe_inv {ζ : ℝ≥0∞} {c : ℝ≥0} (hc : c ≠ 0) : ζ / c / ((c⁻¹ : ℝ≥0) : ℝ≥0∞) = ζ := by
  rw [ENNReal.coe_inv hc, div_eq_mul_inv, inv_inv]
  exact ENNReal.div_mul_cancel (ENNReal.coe_ne_zero.2 hc) ENNReal.coe_ne_top

theorem traceEvent_of_dilPath {c : ℝ≥0} (hc : c ≠ 0) {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (h : TraceEvent (dilPath c w) (ζ / c)) : TraceEvent w ζ := by
  have h' := traceEvent_dilPath (inv_ne_zero hc) h
  rwa [dilPath_inv_dilPath hc, div_coe_div_coe_inv hc] at h'

/-- **Complete words are invariant under dilation of the positions** (`λ > 0`). -/
theorem _root_.InteractingSLE.LP.IsCompleteForceWord.dilate {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (h : LP.IsCompleteForceWord.{u} κ xL xR ρL ρR)
    {lam : ℝ} (hlam : 0 < lam) :
    LP.IsCompleteForceWord.{u} κ (fun i => lam * xL i) (fun j => lam * xR j) ρL ρR := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  set c : ℝ≥0 := ⟨lam ^ 2, sq_nonneg lam⟩ with hcdef
  have hc : c ≠ 0 := by
    intro h0
    have : lam ^ 2 = 0 := congrArg NNReal.toReal h0
    exact (pow_pos hlam 2).ne' this
  have hsq : √(c : ℝ) = lam := by
    show √(lam ^ 2) = lam
    exact Real.sqrt_sq hlam.le
  have hE' := hE.dilate hc
  have e1 : (fun i => (√(c : ℝ))⁻¹ * (lam * xL i)) = xL := by
    funext i; rw [hsq, ← mul_assoc, inv_mul_cancel₀ hlam.ne', one_mul]
  have e2 : (fun i => (√(c : ℝ))⁻¹ * (lam * xR i)) = xR := by
    funext i; rw [hsq, ← mul_assoc, inv_mul_cancel₀ hlam.ne', one_mul]
  rw [e1, e2] at hE'
  filter_upwards [h P (dilFiltration c 𝓕) _ _ _ _ _ hE'] with ω ⟨η, hη, htr⟩
  exact traceEvent_of_dilPath hc ⟨η, hη, htr⟩

/-! ### The stopped assertion from completeness -/

section Stopped

variable {κ : ℝ} {xL ρL : Fin 0 → ℝ} {xR ρR : Fin 1 → ℝ}

/-- **The stopped Aux. lemma 99 for a complete one-mark word.** -/
theorem aux99Stopped_of_isCompleteForceWord (hC : LP.IsCompleteForceWord.{u} κ xL xR ρL ρR)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 0 → ℝ≥0 → Ω → ℝ)
    (VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ,
      IsGeneratingTrace (fun t => W t ω) (firstMeet W (VR 0) ζ ω) η ∧
      (firstMeet W (VR 0) ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) ∧
      ∀ σ : ℝ≥0, (σ : ℝ≥0∞) = firstMeet W (VR 0) ζ ω → (σ : ℝ≥0∞) < ζ ω →
        IsGeneratingTraceIcc (fun t => W t ω) σ η := by
  filter_upwards [hC P 𝓕 W VL VR B ζ hE, hE.2.2.2.2] with ω ⟨η, hη, htr⟩ hp
  have hle : firstMeet W (VR 0) ζ ω ≤ ζ ω := firstMeet_le_lifetime
  refine ⟨η, hη.mono_horizon hle, fun htop => htr (top_le_iff.1 (htop ▸ hle)), fun σ _ hσζ => ?_⟩
  exact Sec7.IsGeneratingTrace.isGeneratingTraceIcc hη hp.isForcePath.continuousOn_w hp.isForcePath.w_zero hσζ

/-- **`Aux99StoppedStatement κ` from complete one-mark words.** -/
theorem aux99StoppedStatement_of_complete
    (h : ∀ (xL ρL : Fin 0 → ℝ) (xR ρR : Fin 1 → ℝ), 0 < xR 0 → LP.IsCompleteForceWord.{u} κ xL xR ρL ρR) :
    Aux99StoppedStatement.{u} κ := by
  intro xL ρL xR ρR hx Ω mΩ P _ 𝓕 W VL VR B ζ hE
  exact aux99Stopped_of_isCompleteForceWord (h xL ρL xR ρR hx) P 𝓕 W VL VR B ζ hE

/-- **`Aux99StoppedStatement κ` from the seed one-force theorem (`ρ > −2`) and Wang–Wu's Lemma 5.1 for `ρ ≤ −2`.** -/
theorem aux99StoppedStatement_of_seed_of_nonAdmissible (hκ : 0 < κ)
    (hseed : ∀ (xL ρL : Fin 0 → ℝ) (ρR : Fin 1 → ℝ), -2 < ρR 0 →
      LP.IsCompleteForceWord.{u} κ xL (fun _ => 0) ρL ρR)
    (hna : WangWu.Lemma51.OneRightNonAdmissibleStatement.{u} κ) : Aux99StoppedStatement.{u} κ := by
  refine aux99StoppedStatement_of_complete fun xL ρL xR ρR hx => ?_
  rcases lt_or_ge (-2) (ρR 0) with hρ | hρ
  · exact WangWu.Lemma51.isCompleteForceWord_oneRight_of_seed hκ hx hρ (hseed xL ρL ρR hρ)
  · exact hna xL ρL xR ρR hx hρ

end Stopped

end Sec7

end InteractingSLE
