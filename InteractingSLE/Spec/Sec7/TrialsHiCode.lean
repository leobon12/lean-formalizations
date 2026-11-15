/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.TwoForceRatio
import InteractingSLE.Spec.Sec7.ContinuityProb6Shift
import InteractingSLE.Spec.Sec2.Assembly2Entr

/-!
# The success event of the midpoint trials: coding, dilation, restart

Packet PROVE-TRIALS-HI. Specification §7.3, Aux. lemma 113, the case `τ = ∞` with both side totals above
`d = κ/2 − 4` (`source/spec/p337-384.md` L725–L737, p. 372): the event `G` of (TI15.1) is "finite `τ`, or transience".
Here the trial event is the complement of ZhanGT4's **non-transience event** `NonTransientEvent w ζ` (infinite
horizon, a continuous generating trace on `[0, ∞)`, no transient one; `ZhanGT4.ntCodeSet` its Borel code set). For a
continuous driver with an infinite lifetime, `¬ NonTransientEvent` says that every generating trace on `[0, ∞)` tends
to infinity (`not_nonTransientEvent_iff`).

This file proves the three facts about this event that the trial argument uses:

* **dilation invariance** of its canonical probability at every ordered separated word, without any assumption on
  the lifetime (`codeLaw_nt_dilate'`; ZhanGT4's `codeLaw_nt_dilate` assumes an infinite lifetime);
* **monotonicity under restart** (pullback at infinity): if the driver of an infinite lifetime is non-transient, so is
  the driver restarted at any time (`nonTransientEvent_shiftNN`);
* the event is measurable for `⨆ₜ 𝓕ₜ` (`measurableSet_nonTransient`), as the terminal trial principle requires.

## Main results

* `nonTransientEvent_dilPath_iff`, `codeLaw_nt_dilate'`;
* `not_nonTransientEvent_iff`, `nonTransientEvent_shiftNN`;
* `measurableSet_nonTransient`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace TrialsHi

open ZhanGT4 Zhan Sec7.Dilation Sec7.RandRestart Sec2 Sec2.Assembly Sec2.Restart

/-! ### The event on one driver -/

section Path

variable {c : ℝ≥0}

/-- For a continuous driver vanishing at `0`, the complement of the non-transience event on an infinite horizon says
that every continuous generating trace on `[0, ∞)` tends to infinity. -/
theorem not_nonTransientEvent_iff {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) :
    ¬ NonTransientEvent w ⊤ ↔
      ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace w ⊤ η → Tendsto (fun t => ‖η t‖) atTop atTop := by
  rw [nonTransientEvent_iff hw hw0]
  constructor
  · intro h η hη
    by_contra hn
    refine h ⟨⟨η, hη⟩, fun ⟨η', hη', htr⟩ => hn ?_⟩
    refine htr.congr fun t => ?_
    rw [hη'.eq_of_le hη hw.continuousOn hw0 le_top]
  · rintro h ⟨⟨η, hη⟩, hnot⟩
    exact hnot ⟨η, hη, h η hη⟩

/-- On a finite horizon the non-transience event fails. -/
theorem not_nonTransientEvent_of_ne_top {w : ℝ≥0 → ℝ} {τ : ℝ≥0∞} (hτ : τ ≠ ⊤) : ¬ NonTransientEvent w τ :=
  fun h => hτ h.1

/-- **Dilation invariance of the non-transience event**, for every horizon: for a driver continuous before `τ` and
vanishing at `0`, the dilated driver on the horizon `τ / c` is non-transient iff the driver is. -/
theorem nonTransientEvent_dilPath_iff (hc : c ≠ 0) {w : ℝ≥0 → ℝ} {τ : ℝ≥0∞}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < τ}) (hw0 : w 0 = 0) :
    NonTransientEvent (dilPath c w) (τ / c) ↔ NonTransientEvent w τ := by
  rcases eq_or_ne τ ⊤ with rfl | hτ
  · have hwc : Continuous w := continuousOn_univ.1 (hw.mono fun t _ => ENNReal.coe_lt_top)
    have hdc : Continuous (dilPath c w) :=
      continuous_const.mul (hwc.comp (continuous_const.mul continuous_id))
    have hd0 : dilPath c w 0 = 0 := by simp [dilPath, hw0]
    rw [ENNReal.top_div_of_ne_top ENNReal.coe_ne_top, nonTransientEvent_iff hdc hd0,
      nonTransientEvent_iff hwc hw0, hasTrace_dilPath_iff hc, hasTransTrace_dilPath_iff hc]
  · have hτc : τ / c ≠ ⊤ := ENNReal.div_ne_top hτ (ENNReal.coe_ne_zero.2 hc)
    exact iff_of_false (not_nonTransientEvent_of_ne_top hτc) (not_nonTransientEvent_of_ne_top hτ)

/-- **Pullback at infinity for the non-transience event**: if a continuous driver vanishing at `0` is non-transient
on `[0, ∞)`, so is the driver restarted at any time `σ`. (The restarted driver has a trace, Yuan's Corollary 1.3; if
it had a transient one, the original trace would be transient.) -/
theorem nonTransientEvent_shiftNN {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    (h : NonTransientEvent w ⊤) (σ : ℝ≥0) : NonTransientEvent (shiftNN w σ) ⊤ := by
  have hwc₂ : Continuous (shiftNN w σ) := (hw.comp (continuous_const.add continuous_id)).sub continuous_const
  rw [nonTransientEvent_iff hw hw0] at h
  rw [nonTransientEvent_iff hwc₂ (shiftNN_zero _ _)]
  obtain ⟨⟨η, hη⟩, hnot⟩ := h
  obtain ⟨η₂, hη₂⟩ := Positive.exists_isGeneratingTrace_shiftNN_of_isGeneratingTrace hw hw0 hη σ
  refine ⟨⟨η₂, hη₂⟩, fun ⟨η₃, hη₃, htr⟩ => hnot ⟨η, hη, ?_⟩⟩
  exact Positive.tendsto_norm_of_shiftNN_tendsto hw hw0 hη hη₃ htr

end Path

/-! ### Dilation of the canonical probability -/

section Kernel

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **Dilation invariance of the canonical non-transience probability** at every ordered separated word, with no
assumption on the lifetime: `codeLaw ntCodeSet (λ x) = codeLaw ntCodeSet x` for `λ = (√c)⁻¹ > 0`. (An evolution from
`x` exists by Theorem 2.2; its dilation is an evolution from `λ x`.) -/
theorem codeLaw_nt_dilate' (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR) (hsep : ∀ i j, xL i < xR j)
    {c : ℝ≥0} (hc : c ≠ 0) :
    codeLaw κ ρL ρR ntCodeSet ((fun i => (√(c : ℝ))⁻¹ * xL i), fun j => (√(c : ℝ))⁻¹ * xR j) =
      codeLaw κ ρL ρR ntCodeSet (xL, xR) := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ hF (ρL := ρL) (ρR := ρR)
  have hc' : (0 : ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  have hs : 0 < (√(c : ℝ))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hc')
  have hsep' : ∀ i j, (√(c : ℝ))⁻¹ * xL i < (√(c : ℝ))⁻¹ * xR j := fun i j =>
    mul_lt_mul_of_pos_left (hsep i j) hs
  rw [← measure_nonTransient_eq_codeLaw hκ hsep' (hE.dilate hc), ← measure_nonTransient_eq_codeLaw hκ hsep hE]
  refine measure_congr (eventuallyEqSet_iff.2 ?_)
  filter_upwards [hE.2.2.2.2] with ω hp
  show NonTransientEvent (dilPath c fun t => W t ω) (ζ ω / c) ↔ NonTransientEvent (fun t => W t ω) (ζ ω)
  exact nonTransientEvent_dilPath_iff hc hp.2.2.2.1 hp.1

end Kernel

/-! ### Measurability of the event of an evolution -/

section Measurability

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The non-transience event of an adapted driver is measurable for `⨆ₜ 𝓖ₜ`**: on an infinite lifetime the
rational-time values of the driver are those of the killed driver, each `𝓖_q`-measurable. -/
theorem measurableSet_nonTransient (hW : AdaptedBefore 𝓖 ζ W)
    (hζ : IsStoppingTime 𝓖 fun ω => (ζ ω : WithTop ℝ≥0)) :
    MeasurableSet[⨆ t, 𝓖 t] {ω | NonTransientEvent (fun t => W t ω) (ζ ω)} := by
  have hζm : Measurable[⨆ t, 𝓖 t] fun ω => (ζ ω : WithTop ℝ≥0) := hζ.measurable_iSup
  have hζtop : MeasurableSet[⨆ t, 𝓖 t] {ω | ζ ω = ⊤} := hζm (measurableSet_singleton ⊤)
  have hK : Measurable[⨆ t, 𝓖 t] fun ω (q : ℚ≥0) => Girsanov.killed ζ W q ω := by
    let _ : MeasurableSpace Ω := ⨆ t, 𝓖 t
    exact measurable_pi_iff.2 fun q => (Girsanov.measurable_killed hW q).mono (le_iSup (fun t => 𝓖 t) _) le_rfl
  have hS : MeasurableSet (topSet ∩ transientSetᶜ) := measurableSet_topSet.inter measurableSet_transientSet.compl
  have e : {ω | NonTransientEvent (fun t => W t ω) (ζ ω)} =
      {ω | ζ ω = ⊤} ∩ (fun ω (q : ℚ≥0) => Girsanov.killed ζ W q ω) ⁻¹' (topSet ∩ transientSetᶜ) := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_compl_iff]
    constructor
    · rintro ⟨hτ, h1, h2⟩
      have hk : (fun q : ℚ≥0 => Girsanov.killed ζ W q ω) = ratVals fun t => W t ω := funext fun q =>
        Girsanov.killed_of_lt (by rw [hτ]; exact ENNReal.coe_lt_top)
      rw [hk]
      exact ⟨hτ, h1, h2⟩
    · rintro ⟨hτ, h1, h2⟩
      have hk : (fun q : ℚ≥0 => Girsanov.killed ζ W q ω) = ratVals fun t => W t ω := funext fun q =>
        Girsanov.killed_of_lt (by rw [hτ]; exact ENNReal.coe_lt_top)
      rw [hk] at h1 h2
      exact ⟨hτ, h1, h2⟩
  rw [e]
  exact hζtop.inter (hK hS)

end Measurability

end TrialsHi

end Sec7

end InteractingSLE
