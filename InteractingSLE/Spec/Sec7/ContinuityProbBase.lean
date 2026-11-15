/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.SLE.All
import InteractingSLE.Spec.Sec2.TerminalEscape
import InteractingSLE.Spec.Sec2.AddMarksGirsanov
import InteractingSLE.Spec.Supplement.LPAssembly

/-!
# §7.3, the κ < 4 induction: the zero-force base and bounded-drift localization of the trace

Packet PROVE-SEC7-C2. Specification §7.3, "Revised induction for Theorem 1.3, `0 < κ < 4`"
(`source/spec/p337-384.md` L843): "Zero force points give ordinary SLE, also covered by the admissible
seed theorem with zero weights." And the bounded-drift comparison used throughout §7.3 (Aux. lemma 103,
L292: "Deleting the entire right group changes the driver by a bounded drift on every bounded
physical-time interval […] Girsanov on the integrated equations […] transfers the induction
hypothesis"; L305: "delete all other initially separated marks up to a sufficiently small gap cutoff,
stopped also at physical time one. Their drift is bounded").

* `not_thresholdCondition_zero`: with all weights zero the threshold condition never holds.
* `IsIntegratedSLEPath.w_eq_of_zero`, `Sec2.IsSLEPathUpTo.w_eq_of_zero`: with all weights zero the
  driver is `√a · b`.
* `IsIntegratedSLEPath.lifetime_eq_top_of_zero`: with all weights zero and a continuous driving path the
  lifetime is infinite (the Sec2 terminal alternative `tendsto_or_criticalEscape`: a finite positive
  lifetime would need a threshold state or a side total `−2`).
* **`isCompleteForceWord_zero`**: every force word with all weights zero (in particular the empty word)
  is complete (`LP.IsCompleteForceWord`) for every `κ > 0`: almost surely `ζ = ∞`, the driver is `√κ B`,
  and the ordinary SLE trace (`ae_exists_trace_all`) is a transient generating trace. This is the
  zero-force base of the revised induction.
* `IsGeneratingTrace.of_eqOn_lt`: a generating trace of a driver on `[0, ∞)` is a generating trace of
  every driver agreeing with it before `T`, on `[0, T]`.
* **`Sec2.IsSLEEvolutionUpTo.ae_exists_isGeneratingTrace_of_separated`** (bounded-drift localization):
  for a local evolution before a bounded stopping time `τ` before which every mark of nonzero weight
  stays at distance `≥ δ > 0` from the driver, almost surely the driver has a continuous generating trace
  on `[0, τ]`, endpoint included. Proof: Girsanov (`girsanov_changeWeights`, all weights to `0`) gives an
  equivalent measure under which the driver is `√κ B̃` before `τ` with `B̃` Brownian; the ordinary SLE
  trace of `√κ B̃` generates the same hulls before `τ`; equivalence of the measures transfers the
  almost-sure statement.
* `IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_of_separated`: the same for an evolution of
  Definition 2.1 and a stopping time `τ ≤ ζ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

/-! ### Zero weights: the driver is Brownian and the lifetime is infinite -/

/-- With all weights zero the threshold condition never holds (every side sum is `0 > −2`). -/
theorem not_thresholdCondition_zero {nL nR : ℕ} (w : ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) :
    ¬ ForceWord.ThresholdCondition (0 : Fin nL → ℝ) (0 : Fin nR → ℝ) w vL vR := by
  simp only [ForceWord.ThresholdCondition, Pi.zero_apply, Finset.sum_const_zero, not_or, not_le]
  norm_num

/-- The drift sums vanish for zero weights. -/
theorem sum_integral_zero_div {n : ℕ} (g : Fin n → ℝ → ℝ) (t : ℝ) :
    (∑ i, ∫ s in (0 : ℝ)..t, (0 : Fin n → ℝ) i / g i s) = 0 := by
  simp only [Pi.zero_apply, zero_div, intervalIntegral.integral_zero, Finset.sum_const_zero]

end Sec7

open Sec7

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
  {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- With all weights zero the driver of an integrated path is `√a · b` before the lifetime. -/
theorem IsIntegratedSLEPath.w_eq_of_zero (h : IsIntegratedSLEPath a xL xR 0 0 w vL vR b ζ)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : w t = Real.sqrt a * b t := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hw, -⟩ := h
  rw [hw t ht, sum_integral_zero_div, sum_integral_zero_div, add_zero, add_zero]

/-- With all weights zero the driver of a local path is `√a · b` before `τ`. -/
theorem Sec2.IsSLEPathUpTo.w_eq_of_zero {τ : ℝ≥0∞}
    (h : Sec2.IsSLEPathUpTo a xL xR 0 0 w vL vR b τ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ) :
    w t = Real.sqrt a * b t := by
  rw [h.w_eq ht, sum_integral_zero_div, sum_integral_zero_div, add_zero, add_zero]

/-- **With all weights zero the lifetime is infinite** (for a continuous driving path `b`). At `ζ = 0`
maximality would make the seed a threshold state; at a finite positive `ζ` the terminal alternative of
Sec2 (`IsIntegratedSLEPath.tendsto_or_criticalEscape`) gives a threshold limit state or a side total
`−2`; with zero weights neither is possible. -/
theorem IsIntegratedSLEPath.lifetime_eq_top_of_zero
    (h : IsIntegratedSLEPath a xL xR 0 0 w vL vR b ζ) (hb : Continuous b) : ζ = ⊤ := by
  by_contra hne
  rcases eq_or_ne ζ 0 with h0 | h0
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hthr, -⟩ := h
    exact not_thresholdCondition_zero 0 xL xR (hthr h0)
  · lift ζ to ℝ≥0 using hne with T
    have hT : 0 < T := pos_iff_ne_zero.2 (by exact_mod_cast h0)
    rcases h.tendsto_or_criticalEscape hT rfl hb.continuousOn with
      ⟨w₀, vL₀, vR₀, -, hthr⟩ | ⟨hs, -⟩ | ⟨hs, -⟩
    · exact not_thresholdCondition_zero w₀ vL₀ vR₀ hthr
    · simp only [Pi.zero_apply, Finset.sum_const_zero] at hs
      norm_num at hs
    · simp only [Pi.zero_apply, Finset.sum_const_zero] at hs
      norm_num at hs

namespace Sec7

/-- **The zero-force base of the revised induction** (Specification p. 378, L843: "Zero force points
give ordinary SLE, also covered by the admissible seed theorem with zero weights"). For `κ > 0`, every
force word whose weights are all zero — in particular the empty word — is complete: every integrated
evolution has, almost surely, infinite lifetime and a continuous generating trace on `[0, ∞)` tending to
infinity. -/
theorem isCompleteForceWord_zero {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) : LP.IsCompleteForceWord.{u} κ xL xR 0 0 := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  obtain ⟨hB, -, -, -, hpath⟩ := hE
  filter_upwards [hpath, hB.1.cont, ae_exists_trace_all hB.1 hκ] with ω hp hc htr
  obtain ⟨⟨η, hη⟩, htr⟩ := htr
  have hζ : ζ ω = ⊤ := hp.lifetime_eq_top_of_zero hc
  have hW : (fun t => W t ω) = fun t => Real.sqrt κ * B t ω := funext fun t =>
    hp.w_eq_of_zero (by rw [hζ]; exact ENNReal.coe_lt_top)
  refine ⟨η, ?_, fun _ => htr η hη⟩
  rw [hζ, hW]
  exact hη

/-- `LP.IsCompleteForceWord` for weights that are zero, stated with pointwise hypotheses. -/
theorem isCompleteForceWord_of_forall_eq_zero {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hL : ∀ i, ρL i = 0)
    (hR : ∀ i, ρR i = 0) : LP.IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  obtain rfl : ρL = 0 := funext hL
  obtain rfl : ρR = 0 := funext hR
  exact isCompleteForceWord_zero hκ xL xR

end Sec7

/-! ### Generating traces of drivers that agree before a time -/

/-- A generating trace of a driver `w'` on `[0, ∞)` is a generating trace on `[0, T]` of every driver
`w` that agrees with `w'` before `T` (hulls only depend on the driver up to their time,
`fwdHull_eq_of_eqOn`). -/
theorem IsGeneratingTrace.of_eqOn_lt {w w' : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w' ⊤ η) {T : ℝ≥0∞} (hww' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → w t = w' t) :
    IsGeneratingTrace w T η := by
  obtain ⟨h0, hc, hfill⟩ := hη
  refine ⟨h0, hc.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top, fun t ht => ?_⟩
  obtain ⟨t₂, htt₂, ht₂T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have hK : QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) t
      = QuantumZipper.fwdHull (fun s : ℝ => w' s.toNNReal) t := by
    refine fwdHull_eq_of_eqOn t.2 (by exact_mod_cast htt₂) fun r hr => hww' _ ?_
    refine lt_of_le_of_lt ?_ ht₂T
    exact_mod_cast (Real.toNNReal_le_iff_le_coe.2 hr.2)
  rw [hK]
  exact hfill t ENNReal.coe_lt_top

/-! ### Bounded-drift localization of the trace (Girsanov) -/

section Localization

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ' τ : Ω → ℝ≥0∞}

/-- **Bounded-drift localization of the trace** (Specification §7.3: Aux. lemma 103, L292 and L305, "their
drift is bounded"; the Girsanov comparison of Theorem 2.2's proof, L486–L488). Let `(W, V, B)` be a local
integrated evolution before `ζ'`, and `τ ≤ ζ' ∧ T` a stopping time before which every mark of nonzero
weight stays at distance at least `δ > 0` from the driver. Then almost surely the driver has a continuous
generating trace on `[0, τ]`, including the endpoint `τ`. -/
theorem Sec2.IsSLEEvolutionUpTo.ae_exists_isGeneratingTrace_of_separated [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hE : Sec2.IsSLEEvolutionUpTo κ xL xR ρL ρR P 𝓕 W VL VR B ζ')
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s}) (hτζ : ∀ ω, τ ω ≤ ζ' ω) {T : ℝ≥0}
    (hτT : ∀ ω, τ ω ≤ T) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω →
      (∀ i, ρL i ≠ 0 → δ ≤ |W t ω - VL i t ω|) ∧ ∀ i, ρR i ≠ 0 → δ ≤ |W t ω - VR i t ω|) :
    ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (τ ω) η := by
  obtain ⟨hQ, hE'⟩ := hE.girsanov_changeWeights hκ 0 0 hτ hτζ hτT hδ (by
    filter_upwards [hgap] with ω hg t ht
    exact ⟨fun i hi => (hg t ht).1 i (Ne.symm hi), fun i hi => (hg t ht).2 i (Ne.symm hi)⟩)
  refine hQ.ac'.ae_le ?_
  have := hQ.isProb
  filter_upwards [hE'.ae_path, ae_exists_trace_all hE'.brownian.1 hκ] with ω hp htr
  obtain ⟨⟨η, hη⟩, -⟩ := htr
  exact ⟨η, hη.of_eqOn_lt fun t ht => hp.w_eq_of_zero ht⟩

/-- Bounded-drift localization of the trace for an evolution of Definition 2.1. -/
theorem IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_of_separated [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ')
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s}) (hτζ : ∀ ω, τ ω ≤ ζ' ω) {T : ℝ≥0}
    (hτT : ∀ ω, τ ω ≤ T) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω →
      (∀ i, ρL i ≠ 0 → δ ≤ |W t ω - VL i t ω|) ∧ ∀ i, ρR i ≠ 0 → δ ≤ |W t ω - VR i t ω|) :
    ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (τ ω) η :=
  hE.isSLEEvolutionUpTo.ae_exists_isGeneratingTrace_of_separated hκ hτ hτζ hτT hδ hgap

end Localization

end InteractingSLE
