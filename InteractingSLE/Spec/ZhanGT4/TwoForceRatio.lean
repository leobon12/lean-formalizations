/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.TwoForceFibre
import InteractingSLE.Spec.Sec2.JacobiExists
import InteractingSLE.Spec.Ito.FiltrationBasic

/-!
# The gap-ratio transfer: from the two-seed law to every separated two-force pair (Part B.3)

Packet PROVE-ZHAN-GT4-B. Source: Astra, *Follow-up proofs and dependency audit*, §B.3 L1266–L1279 (ruling R38):
"To obtain every separated pair from the seed law, let `L = W − V_L`, `R = V_R − W`, `U = log(R/L)` … (E13). Both
scale integrals diverge, and this clock is infinite … Thus `U` hits any prescribed finite level. Stop when
`R/L = p_R/(−p_L)`, and apply a positive affine normalization. Strong Markov uniqueness makes the mapped future exactly
the desired separated law. Pullback and pushforward at infinity preserve transience. This proves all two-force bases,
including equality at the nonhitting threshold." (Additional note, Lemma 1.7, ruling R39: "This calculation and
transfer use no restriction on `κ`.")

This file proves the transfer for every `κ > 0`, given the recurrence of the gap ratio (the scale computation (E13),
a named statement `TwoSeedRatioRecurrenceStatement κ` here):

* **dilation** (the positive affine normalization): the canonical probability that the driver has a non-transient
  trace is the same for the words `s` and `λ s`, `λ > 0` (`codeLaw_nonTransient_dilate`);
* **pullback at infinity** (deterministic): if the original trace is transient, so is the trace of the driver restarted
  at any time (`tendsto_norm_of_shift`, `η(σ + s) = F̄_σ(η₂(s))` with `F̄_σ` at bounded distance from the identity);
* **the strong Markov restart** at the first time after `1` where `R = r L` (`measure_restart_codeEvent`).

## Main results

* `HasTrace`, `HasTransTrace`, their dilation invariance; `tendsto_norm_of_shift`.
* `NonTransientEvent`, `ntCodeSet`, `codeLaw_nonTransient_dilate`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4

open Zhan Sec7.Dilation Sec7.RandRestart
open QuantumZipper (H Hbar fwdMapInv)

/-! ### Traces and transience under dilation -/

/-- The driver has a continuous generating trace on `[0, ∞)`. -/
def HasTrace (w : ℝ≥0 → ℝ) : Prop := ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ⊤ η

/-- The driver has a transient continuous generating trace on `[0, ∞)`. -/
def HasTransTrace (w : ℝ≥0 → ℝ) : Prop :=
  ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ⊤ η ∧ Tendsto (fun t => ‖η t‖) atTop atTop

section Dilation

variable {c : ℝ≥0}

theorem dilPath_inv_dilPath (hc : c ≠ 0) (w : ℝ≥0 → ℝ) : dilPath c⁻¹ (dilPath c w) = w := by
  funext t
  simp only [dilPath]
  rw [← mul_assoc c c⁻¹ t, mul_inv_cancel₀ hc, one_mul, ← mul_assoc]
  have hc' : (0 : ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  have : (√((c⁻¹ : ℝ≥0) : ℝ))⁻¹ * (√(c : ℝ))⁻¹ = 1 := by
    rw [NNReal.coe_inv, Real.sqrt_inv, inv_inv, mul_inv_cancel₀ (Real.sqrt_pos.2 hc').ne']
  rw [this, one_mul]

theorem isGeneratingTrace_dilate_top (hc : c ≠ 0) {w : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ}
    (h : IsGeneratingTrace w ⊤ η) :
    IsGeneratingTrace (dilPath c w) ⊤ (fun t => (((√(c : ℝ))⁻¹ : ℝ) : ℂ) * η (c * t)) := by
  have := h.dilate hc
  rwa [ENNReal.top_div_of_ne_top ENNReal.coe_ne_top] at this

theorem tendsto_norm_dilate (hc : c ≠ 0) {η : ℝ≥0 → ℂ} (h : Tendsto (fun t => ‖η t‖) atTop atTop) :
    Tendsto (fun t => ‖(((√(c : ℝ))⁻¹ : ℝ) : ℂ) * η (c * t)‖) atTop atTop := by
  have hc' : (0 : ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  have hs : 0 < (√(c : ℝ))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hc')
  have hct : Tendsto (fun t : ℝ≥0 => c * t) atTop atTop :=
    tendsto_id.const_mul_atTop (pos_iff_ne_zero.2 hc)
  have := (h.comp hct).const_mul_atTop hs
  refine this.congr fun t => ?_
  simp only [Function.comp_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]

theorem HasTrace.dilate (hc : c ≠ 0) {w : ℝ≥0 → ℝ} (h : HasTrace w) : HasTrace (dilPath c w) := by
  obtain ⟨η, hη⟩ := h
  exact ⟨_, isGeneratingTrace_dilate_top hc hη⟩

theorem HasTransTrace.dilate (hc : c ≠ 0) {w : ℝ≥0 → ℝ} (h : HasTransTrace w) :
    HasTransTrace (dilPath c w) := by
  obtain ⟨η, hη, htr⟩ := h
  exact ⟨_, isGeneratingTrace_dilate_top hc hη, tendsto_norm_dilate hc htr⟩

theorem hasTrace_dilPath_iff (hc : c ≠ 0) {w : ℝ≥0 → ℝ} : HasTrace (dilPath c w) ↔ HasTrace w := by
  refine ⟨fun h => ?_, HasTrace.dilate hc⟩
  have := h.dilate (inv_ne_zero hc)
  rwa [dilPath_inv_dilPath hc] at this

theorem hasTransTrace_dilPath_iff (hc : c ≠ 0) {w : ℝ≥0 → ℝ} :
    HasTransTrace (dilPath c w) ↔ HasTransTrace w := by
  refine ⟨fun h => ?_, HasTransTrace.dilate hc⟩
  have := h.dilate (inv_ne_zero hc)
  rwa [dilPath_inv_dilPath hc] at this

end Dilation

/-! ### Pullback at infinity -/

/-- **Transience passes to the restarted driver** (pullback at infinity): if `w` has a transient generating trace `η`
on `[0, ∞)` and the driver restarted at `σ` has a generating trace `η₂` on `[0, ∞)`, then `η₂` is transient
(`η(σ + s) = F̄_σ(η₂(s))` and `‖F̄_σ(y) − y‖ ≤ C`). -/
theorem tendsto_norm_of_shift {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) (htr : Tendsto (fun t => ‖η t‖) atTop atTop) {σ : ℝ≥0}
    {η₂ : ℝ≥0 → ℂ} (hη₂ : IsGeneratingTrace (Sec7.shiftNN w σ) ⊤ η₂) :
    Tendsto (fun t => ‖η₂ t‖) atTop atTop := by
  have hwc : ContinuousOn w {s | (s : ℝ≥0∞) < ⊤} := hw.continuousOn
  have h₁ := Sec7.IsGeneratingTrace.isGeneratingTraceIcc hη hwc hw0 (σ := σ) ENNReal.coe_lt_top
  have hσt₂ : (σ : ℝ) < (σ : ℝ) + 1 := lt_add_one _
  have hfc : Continuous (frozenDrive w ((σ : ℝ) + 1)) := continuous_frozenDrive hw.continuousOn
  obtain ⟨hF, -, -, -, -, ⟨C, hC⟩, -⟩ := h₁.extend_props hσt₂ hfc hw0
  set Fb := extendFrom H (fwdMapInv (frozenDrive w ((σ : ℝ) + 1)) σ) with hFb
  have hwc' : ContinuousOn w {s | (s : ℝ≥0∞) < (σ : ℝ≥0∞) + ⊤} := by rw [add_top]; exact hwc
  obtain ⟨hjoin, -⟩ := h₁.join hwc' hw0 hη₂
  rw [add_top] at hjoin
  have hjoinF : ∀ t : ℝ≥0, σ < t → η t = Fb (η₂ (t - σ)) := by
    intro t ht
    rw [hη.eq_of_le hjoin hwc hw0 le_top, Sec7.joinTrace_of_lt ht, hF]
  have hw₂ : Continuous fun s : ℝ => Sec7.shiftNN w σ s.toNNReal := by
    unfold Sec7.shiftNN
    exact ((hw.comp (continuous_const.add continuous_id)).sub continuous_const).comp continuous_real_toNNReal
  have hη₂H : ∀ s, η₂ s ∈ Hbar := fun s =>
    Sec4.im_nonneg_of_isGeneratingTrace hw₂ (Sec7.shiftNN_zero w σ) hη₂ s
  refine tendsto_atTop.2 fun b => ?_
  obtain ⟨T, hT⟩ := eventually_atTop.1 (tendsto_atTop.1 htr (b + C))
  refine eventually_atTop.2 ⟨T + 1, fun s hs => ?_⟩
  have hs0 : 0 < s := lt_of_lt_of_le (lt_of_lt_of_le one_pos le_add_self) hs
  have hσs : σ < σ + s := lt_add_of_pos_right σ hs0
  have h1 := hjoinF (σ + s) hσs
  rw [add_tsub_cancel_left] at h1
  have h2 := hT (σ + s) (le_trans (le_trans le_self_add hs) le_add_self)
  have h3 := hC (η₂ s) (hη₂H s)
  have h4 : ‖Fb (η₂ s)‖ - ‖η₂ s‖ ≤ ‖Fb (η₂ s) - η₂ s‖ := norm_sub_norm_le _ _
  rw [h1] at h2
  linarith

/-! ### The non-transience event and its coding -/

/-- **The non-transience event** of a (driver, horizon) pair: infinite horizon, a continuous generating trace on
`[0, ∞)`, and no transient one (for a continuous driver: its trace is not transient). -/
def NonTransientEvent (w : ℝ≥0 → ℝ) (τ : ℝ≥0∞) : Prop :=
  τ = ⊤ ∧ ratVals w ∈ topSet ∧ ratVals w ∉ transientSet

/-- The Borel set of (driver, horizon) pairs with the non-transience event. -/
def ntSet : Set ((ℝ≥0 → ℝ) × ℝ≥0∞) :=
  (Prod.snd ⁻¹' {⊤}) ∩ ((fun x => ratVals x.1) ⁻¹' (topSet ∩ transientSetᶜ))

theorem measurableSet_ntSet : MeasurableSet ntSet :=
  (measurable_snd (measurableSet_singleton ⊤)).inter
    ((measurable_ratVals.comp measurable_fst) (measurableSet_topSet.inter measurableSet_transientSet.compl))

theorem nonTransientEvent_iff {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) :
    NonTransientEvent w ⊤ ↔ HasTrace w ∧ ¬ HasTransTrace w := by
  have h1 : ratVals w ∈ topSet ↔ HasTrace w := ratVals_mem_topSet_iff hw hw0
  have h2 : ratVals w ∈ transientSet ↔ HasTransTrace w := mem_transientSet_iff hw hw0
  unfold NonTransientEvent
  rw [h1, h2]
  simp

theorem nonTransientEvent_congr (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞)
    (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t) (hn : NonTransientEvent w τ) : NonTransientEvent w' τ := by
  obtain ⟨hτ, h2⟩ := hn
  subst hτ
  have : w = w' := funext fun t => h t ENNReal.coe_lt_top
  subst this
  exact ⟨rfl, h2⟩

/-! ### Dilation invariance of the canonical non-transience probability -/

section Kernel

open Sec2 Sec2.Assembly Sec2.Restart

variable {nL nR : ℕ}

/-- The Borel set of solution codes whose driver has the non-transience event up to the lifetime. -/
def ntCodeSet : Set (XCode nL nR) := (fun x => (cw x, cζ x)) ⁻¹' ntSet

theorem measurableSet_ntCodeSet : MeasurableSet (ntCodeSet (nL := nL) (nR := nR)) :=
  measurable_cw_cζ measurableSet_ntSet

variable {κ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The probability of the non-transience event is the canonical one of the word. -/
theorem measure_nonTransient_eq_codeLaw [IsProbabilityMeasure P] (hκ : 0 < κ) (hsep : ∀ i j, xL i < xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    P {ω | NonTransientEvent (fun t => W t ω) (ζ ω)} = codeLaw κ ρL ρR ntCodeSet (xL, xR) :=
  measure_eventOf_eq_codeLaw hκ hsep hE measurableSet_ntCodeSet (fun _ _ _ => Iff.rfl) nonTransientEvent_congr

/-- **Dilation invariance** (the positive affine normalization of B.3): if the word `(xL, xR)` has an evolution with
infinite lifetime, the canonical probability of a non-transient trace is the same at `λ (xL, xR)` for every `λ > 0`
(here `λ = (√c)⁻¹`). -/
theorem codeLaw_nt_dilate [IsProbabilityMeasure P] (hκ : 0 < κ) (hsep : ∀ i j, xL i < xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) {c : ℝ≥0}
    (hc : c ≠ 0) :
    codeLaw κ ρL ρR ntCodeSet ((fun i => (√(c : ℝ))⁻¹ * xL i), fun j => (√(c : ℝ))⁻¹ * xR j) =
      codeLaw κ ρL ρR ntCodeSet (xL, xR) := by
  have hc' : (0 : ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  have hs : 0 < (√(c : ℝ))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hc')
  have hsep' : ∀ i j, (√(c : ℝ))⁻¹ * xL i < (√(c : ℝ))⁻¹ * xR j := fun i j =>
    mul_lt_mul_of_pos_left (hsep i j) hs
  rw [← measure_nonTransient_eq_codeLaw hκ hsep' (hE.dilate hc), ← measure_nonTransient_eq_codeLaw hκ hsep hE]
  refine measure_congr (eventuallyEqSet_iff.2 ?_)
  filter_upwards [hζ, hE.2.2.2.2] with ω hζω hp
  have hwc : Continuous fun t => W t ω := by
    have h := hp.2.2.2.1
    rw [hζω] at h
    exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)
  have hdc : Continuous (dilPath c fun t => W t ω) :=
    continuous_const.mul (hwc.comp (continuous_const.mul continuous_id))
  have hd0 : dilPath c (fun t => W t ω) 0 = 0 := by simp [dilPath, hp.1]
  show NonTransientEvent (dilPath c fun t => W t ω) (ζ ω / c) ↔ NonTransientEvent (fun t => W t ω) (ζ ω)
  rw [hζω, ENNReal.top_div_of_ne_top ENNReal.coe_ne_top, nonTransientEvent_iff hdc hd0,
    nonTransientEvent_iff hwc hp.1, hasTrace_dilPath_iff hc, hasTransTrace_dilPath_iff hc]

end Kernel

/-! ### The first time after `1` at which a continuous process vanishes -/

section Hit

variable {Ω : Type*}

/-- `max(Y_t, 1 − t)`: nonpositive exactly when `t ≥ 1` and `Y_t ≤ 0`. -/
def posAfter (Y : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun t ω => max (Y t ω) (1 - (t : ℝ))

/-- The zero process. -/
def zeroProc : ℝ≥0 → Ω → ℝ := fun _ _ => 0

/-- **The first time after `1` at which `Y` vanishes**, as the later of the first times after `1` at which `Y ≤ 0`
and `−Y ≤ 0` (each a first meeting time, capped by the lifetime). -/
def hitAfter (Y : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  max (Sec7.firstMeet zeroProc (posAfter Y) ζ ω) (Sec7.firstMeet zeroProc (posAfter (-Y)) ζ ω)

theorem continuousOn_posAfter_sub {Y : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous fun t => Y t ω) (S : Set ℝ≥0) :
    ContinuousOn (fun t => posAfter Y t ω - zeroProc t ω) S :=
  ((hc.max (continuous_const.sub NNReal.continuous_coe)).sub continuous_const).continuousOn

/-- One first meeting: if `Y` vanishes at some time `≥ 1` (infinite lifetime), the first time after `1` with
`Y ≤ 0` is a finite `m ≥ 1` with `Y_m ≤ 0`, and `Y > 0` on `[1, m)`. -/
theorem exists_firstMeet_posAfter {Y : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} (hc : Continuous fun t => Y t ω)
    (hζ : ζ ω = ⊤) {t₀ : ℝ≥0} (ht₀ : 1 ≤ t₀) (hz : Y t₀ ω ≤ 0) :
    ∃ m : ℝ≥0, Sec7.firstMeet zeroProc (posAfter Y) ζ ω = m ∧ 1 ≤ m ∧ Y m ω ≤ 0 ∧
      ∀ t : ℝ≥0, 1 ≤ t → t < m → 0 < Y t ω := by
  have ht₀' : (t₀ : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  have h1 : posAfter Y t₀ ω ≤ zeroProc t₀ ω := by
    simp only [posAfter, zeroProc, max_le_iff]
    exact ⟨hz, by have : (1 : ℝ) ≤ t₀ := by exact_mod_cast ht₀
                  linarith⟩
  have hlt : Sec7.firstMeet zeroProc (posAfter Y) ζ ω < ζ ω :=
    lt_of_le_of_lt (Sec7.firstMeet_le_of ht₀' h1) ht₀'
  obtain ⟨m, hm, -, hmV⟩ := Sec7.exists_eq_firstMeet (continuousOn_posAfter_sub hc _) hlt
  simp only [posAfter, zeroProc, max_le_iff] at hmV
  refine ⟨m, hm, ?_, hmV.1, fun t ht1 htm => ?_⟩
  · have : (1 : ℝ) ≤ m := by linarith [hmV.2]
    exact_mod_cast this
  · have h2 := (Sec7.lt_of_lt_firstMeet (W := zeroProc) (V := posAfter Y) (ζ := ζ) (ω := ω)
      (t := t) (by rw [hm]; exact_mod_cast htm)).2
    simp only [posAfter, zeroProc, lt_max_iff] at h2
    rcases h2 with h2 | h2
    · exact h2
    · have : (1 : ℝ) ≤ t := by exact_mod_cast ht1
      linarith

/-- **The hitting time is a zero of `Y` after time `1`** (pathwise): if `Y` is continuous, the lifetime infinite and
`Y` vanishes at some time `≥ 1`, then `hitAfter Y ζ ω` is a finite time `m ≥ 1` with `Y_m = 0`. -/
theorem exists_hitAfter {Y : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} (hc : Continuous fun t => Y t ω)
    (hζ : ζ ω = ⊤) {t₀ : ℝ≥0} (ht₀ : 1 ≤ t₀) (hz : Y t₀ ω = 0) :
    ∃ m : ℝ≥0, hitAfter Y ζ ω = m ∧ 1 ≤ m ∧ Y m ω = 0 := by
  obtain ⟨mp, hmp, hmp1, hYp, hbp⟩ := exists_firstMeet_posAfter hc hζ ht₀ hz.le
  have hcn : Continuous fun t => (-Y) t ω := hc.neg
  obtain ⟨mm, hmm, hmm1, hYm, hbm⟩ := exists_firstMeet_posAfter (Y := -Y) hcn hζ ht₀ (by simp [hz])
  simp only [Pi.neg_apply, neg_nonpos] at hYm
  simp only [Pi.neg_apply, Left.neg_pos_iff] at hbm
  have hYc : Continuous fun t : ℝ≥0 => Y t ω := hc
  unfold hitAfter
  rw [hmp, hmm]
  rcases le_total mm mp with hle | hle
  · refine ⟨mp, by rw [max_eq_left (by exact_mod_cast hle)], hmp1, ?_⟩
    -- `Y_{mm} ≥ 0 ≥ Y_{mp}`; a zero in `[mm, mp]` must be `mp`
    obtain ⟨t, ht, hYt⟩ := intermediate_value_Icc' hle hYc.continuousOn ⟨hYp, hYm⟩
    rcases ht.2.lt_or_eq with htl | hte
    · exact absurd hYt (hbp t (hmm1.trans ht.1) htl).ne'
    · rw [← hte]; exact hYt
  · refine ⟨mm, by rw [max_eq_right (by exact_mod_cast hle)], hmm1, ?_⟩
    obtain ⟨t, ht, hYt⟩ := intermediate_value_Icc hle hYc.continuousOn ⟨hYp, hYm⟩
    rcases ht.2.lt_or_eq with htl | hte
    · exact absurd hYt (hbm t (hmp1.trans ht.1) htl).ne
    · rw [← hte]; exact hYt

end Hit

/-! ### Adaptedness of functions of the state -/

theorem adaptedBefore_of_eq {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞}
    {W V₁ V₂ X : ℝ≥0 → Ω → ℝ} (F : ℝ≥0 → ℝ × ℝ × ℝ → ℝ) (hF : ∀ t, Measurable (F t))
    (hW : AdaptedBefore 𝓖 ζ W) (h1 : AdaptedBefore 𝓖 ζ V₁) (h2 : AdaptedBefore 𝓖 ζ V₂)
    (hX : ∀ t ω, X t ω = F t (W t ω, V₁ t ω, V₂ t ω)) : AdaptedBefore 𝓖 ζ X := by
  intro t A hA
  have hm : Measurable[𝓖 t] fun ω =>
      (Girsanov.killed ζ W t ω, Girsanov.killed ζ V₁ t ω, Girsanov.killed ζ V₂ t ω) :=
    (Girsanov.measurable_killed hW t).prodMk
      ((Girsanov.measurable_killed h1 t).prodMk (Girsanov.measurable_killed h2 t))
  have hlife : MeasurableSet[𝓖 t] {ω | (t : ℝ≥0∞) < ζ ω} := by
    simpa using hW t univ MeasurableSet.univ
  have heq : {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A} = {ω | (t : ℝ≥0∞) < ζ ω} ∩
      (fun ω => F t (Girsanov.killed ζ W t ω, Girsanov.killed ζ V₁ t ω, Girsanov.killed ζ V₂ t ω)) ⁻¹' A := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨h, hx⟩
      rw [Girsanov.killed_of_lt h, Girsanov.killed_of_lt h, Girsanov.killed_of_lt h, ← hX]
      exact ⟨h, hx⟩
    · rintro ⟨h, hx⟩
      rw [Girsanov.killed_of_lt h, Girsanov.killed_of_lt h, Girsanov.killed_of_lt h, ← hX] at hx
      exact ⟨h, hx⟩
  rw [heq]
  exact hlife.inter (((hF t).comp hm) hA)

/-! ### The named inputs -/

/-- **Named input: recurrence of the gap ratio of the two-seed law** (B.3 L1266–L1273, (E13); additional note
Lemma 1.7, (ZE.6)): "Both scale integrals diverge, and this clock is infinite … Thus `U` hits any prescribed finite
level." For the two-seed law with admissible weights and every `r > 0`, almost surely `R_t = r L_t` at some time
`t ≥ 1` (`L = W − V_L`, `R = V_R − W`). The source's proof is the scale computation for `U = log(R/L)` in the clock
`du = (1/L + 1/R)² dt`; equivalently, the log-clock angle `L/(L + R)` (`Sec2.angleG`, a stationary Jacobi diffusion,
`Sec2.isJacobiMP_angleG`) hits every level of `(0, 1)`. Not proved here. -/
def TwoSeedRatioRecurrenceStatement (κ : ℝ) : Prop :=
  ∀ (ρL ρR : Fin 1 → ℝ), Sec4.HasAdmissiblePartialSums κ ρL ρR (fun _ => 0) (fun _ => 0) →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ →
        ∀ r : ℝ, 0 < r → ∀ᵐ ω ∂P, ∃ t : ℝ≥0, 1 ≤ t ∧ VR 0 t ω - W t ω = r * (W t ω - VL 0 t ω)

/-- **Two-seed transience** as a statement (proved for `κ ≤ 4` by PROVE-ZHAN-B2, and for every `κ` from
`SeparatedNoRealClusterStatement κ` in `TwoForceFibre.lean`). -/
def TwoSeedTransienceStatement (κ : ℝ) : Prop :=
  ∀ (ρL ρR : Fin 1 → ℝ), Sec4.HasAdmissiblePartialSums κ ρL ρR (fun _ => 0) (fun _ => 0) →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
          Tendsto (fun t => ‖η t‖) atTop atTop

theorem twoSeedTransienceStatement_of_separatedNoCluster {κ : ℝ} (hκ : 0 < κ)
    (hN : SeparatedNoRealClusterStatement.{0} κ) : TwoSeedTransienceStatement.{u} κ :=
  fun _ _ hadm _ _ _ _ _ _ _ _ _ _ hE =>
    IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoSeed_of_separatedNoCluster hκ hN hadm hE

theorem twoSeedTransienceStatement_of_le_four {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) :
    TwoSeedTransienceStatement.{u} κ :=
  fun _ _ hadm _ _ _ _ _ _ _ _ _ _ hE => Zhan.IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoSeed hκ hκ4 hadm hE

/-- The seed word with admissible weights. -/
theorem hasAdmissiblePartialSums_seed {κ : ℝ} {ρL ρR : Fin 1 → ℝ} (hL : κ / 2 - 2 ≤ ρL 0)
    (hR : κ / 2 - 2 ≤ ρR 0) : Sec4.HasAdmissiblePartialSums κ ρL ρR (fun _ => 0) (fun _ => 0) := by
  constructor
  · intro x hx _
    have hf : (Finset.univ.filter fun i : Fin 1 => x < (fun _ => (0 : ℝ)) i) = Finset.univ := by
      ext i; simp [hx]
    rwa [hf, Fin.sum_univ_one]
  · intro x hx _
    have hf : (Finset.univ.filter fun i : Fin 1 => (fun _ => (0 : ℝ)) i ≤ x) = Finset.univ := by
      ext i; simp [hx]
    rwa [hf, Fin.sum_univ_one]

/-! ### The restart at the ratio hitting time -/

section Restart

/-- The ratio gap `R − r L` of a one-mark-per-side evolution (`L = W − V_L`, `R = V_R − W`). -/
def ratioGap {Ω : Type*} (r : ℝ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => (VR 0 t ω - W t ω) - r * (W t ω - VL 0 t ω)

/-- The pathwise facts of the two-seed law used at the restart: infinite lifetime, continuity, separation of the left
mark at positive times, a time `≥ 1` with `R = r L`, and a transient trace. -/
def GoodRatio {Ω : Type*} (r : ℝ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) :
    Prop :=
  ζ ω = ⊤ ∧ Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ Continuous (fun t => VL 0 t ω) ∧
    Continuous (fun t => VR 0 t ω) ∧ (∀ t : ℝ≥0, 0 < t → VL 0 t ω < W t ω) ∧
    (∃ t : ℝ≥0, 1 ≤ t ∧ ratioGap r W VL VR t ω = 0) ∧ HasTrace (fun t => W t ω) ∧
    ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → Tendsto (fun t => ‖η t‖) atTop atTop

variable {κ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {ρL ρR : Fin 1 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The strong Markov restart at the ratio hitting time** (B.3 L1273–L1276). For a two-seed evolution (in a
filtration where the null set `N` is measurable at every time) whose paths off `N` have the facts `GoodRatio r`, if
the canonical probability of a non-transient trace is a constant `K` along the ray of words `(−L, r L)`, `L > 0`, then
`K = 0`: restart at `T = ` the first time `≥ 1` with `R = r L` (capped at `n`); the future has no non-transient trace
since the original trace is transient (pullback at infinity); the restarted word is on the ray. -/
theorem eq_zero_of_restart_ratio [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓖 W VL VR B ζ) {r : ℝ}
    {N : Set Ω} (hNm : ∀ t, MeasurableSet[𝓖 t] N) (hN0 : P N = 0)
    (hgood : ∀ ω ∉ N, GoodRatio r W VL VR ζ ω) {K : ℝ≥0∞}
    (hdil : ∀ L : ℝ, 0 < L → codeLaw κ ρL ρR ntCodeSet ((fun _ => -L), fun _ => r * L) = K) : K = 0 := by
  set Y := ratioGap r W VL VR with hY
  -- adaptedness of the processes defining the hitting time
  have hYa : AdaptedBefore 𝓖 ζ (posAfter Y) :=
    adaptedBefore_of_eq (fun t p => max ((p.2.2 - p.1) - r * (p.1 - p.2.1)) (1 - (t : ℝ)))
      (fun t => by fun_prop) hE.2.1 (hE.2.2.1 0) (hE.2.2.2.1 0) fun t ω => rfl
  have hYa' : AdaptedBefore 𝓖 ζ (posAfter (-Y)) :=
    adaptedBefore_of_eq (fun t p => max (-((p.2.2 - p.1) - r * (p.1 - p.2.1))) (1 - (t : ℝ)))
      (fun t => by fun_prop) hE.2.1 (hE.2.2.1 0) (hE.2.2.2.1 0) fun t ω => rfl
  have hZa : AdaptedBefore 𝓖 ζ (zeroProc (Ω := Ω)) :=
    adaptedBefore_of_eq (fun _ _ => 0) (fun _ => measurable_const) hE.2.1 (hE.2.2.1 0) (hE.2.2.2.1 0)
      fun _ _ => rfl
  have hYc : ∀ ω ∉ N, Continuous fun t => Y t ω := fun ω hω => by
    obtain ⟨-, hw, -, hl, hr', -⟩ := hgood ω hω
    exact (hr'.sub hw).sub (continuous_const.mul (hw.sub hl))
  have hT₁ := Sec7.isStoppingTime_firstMeet_off hZa hYa hNm fun ω hω =>
    continuousOn_posAfter_sub (hYc ω hω) _
  have hT₂ := Sec7.isStoppingTime_firstMeet_off hZa hYa' hNm fun ω hω =>
    continuousOn_posAfter_sub (Y := -Y) (hYc ω hω).neg _
  set Th : Ω → ℝ≥0∞ := fun ω => max (Sec7.zeroOn N (Sec7.firstMeet zeroProc (posAfter Y) ζ) ω)
    (Sec7.zeroOn N (Sec7.firstMeet zeroProc (posAfter (-Y)) ζ) ω) with hTh
  have hThs : IsStoppingTime 𝓖 fun ω => (Th ω : WithTop ℝ≥0) := hT₁.max hT₂
  have hhit : ∀ ω ∉ N, ∃ m : ℝ≥0, Th ω = m ∧ 1 ≤ m ∧ Y m ω = 0 := fun ω hω => by
    obtain ⟨hζ, -, -, -, -, -, ⟨t₀, ht₀, hz⟩, -⟩ := hgood ω hω
    have : Th ω = hitAfter Y ζ ω := by
      simp only [hTh, hitAfter, Sec7.zeroOn_of_notMem hω]
    rw [this]
    exact exists_hitAfter (hYc ω hω) hζ ht₀ hz
  -- the capped stopping times and the restart events
  set Tn : ℕ → Ω → ℝ≥0 := fun n ω => (min (Th ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal with hTn
  have hTn_coe : ∀ n ω, ((Tn n ω : ℝ≥0) : ℝ≥0∞) = min (Th ω) ((n : ℝ≥0) : ℝ≥0∞) := fun n ω =>
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))
  have hTns : ∀ n, IsStoppingTime 𝓖 fun ω => ((Tn n ω : ℝ≥0) : WithTop ℝ≥0) := fun n => by
    have h := hThs.min_const (n : ℝ≥0)
    have he : (fun ω => ((Tn n ω : ℝ≥0) : WithTop ℝ≥0)) = fun ω => min (Th ω : WithTop ℝ≥0) (n : ℝ≥0) :=
      funext fun ω => hTn_coe n ω
    rw [he]; exact h
  set A : ℕ → Set Ω := fun n => Nᶜ ∩ {ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} with hA
  have hTnA : ∀ n, ∀ ω ∈ A n, ((Tn n ω : ℝ≥0) : ℝ≥0∞) = Th ω := fun n ω hω => by
    rw [hTn_coe]; exact min_eq_left hω.2.le
  have hAm : ∀ n, MeasurableSet[(hTns n).measurableSpace] (A n) := by
    intro n
    have key : ∀ i : ℝ≥0, MeasurableSet[𝓖 i] (A n ∩ {ω | ((Tn n ω : ℝ≥0) : WithTop ℝ≥0) ≤ i}) := by
      intro i
      have heq : A n ∩ {ω | ((Tn n ω : ℝ≥0) : WithTop ℝ≥0) ≤ i} =
          Nᶜ ∩ ({ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} ∩ {ω | Th ω ≤ (i : ℝ≥0∞)}) := by
        ext ω
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨h1, h2, ?_⟩
          have h3' : ((Tn n ω : ℝ≥0) : ℝ≥0∞) ≤ i := h3
          rwa [hTnA n ω ⟨h1, h2⟩] at h3'
        · rintro ⟨h1, h2, h3⟩
          refine ⟨⟨h1, h2⟩, ?_⟩
          show ((Tn n ω : ℝ≥0) : ℝ≥0∞) ≤ i
          rw [hTnA n ω ⟨h1, h2⟩]; exact h3
      rw [heq]
      refine (hNm i).compl.inter ?_
      rcases lt_or_ge i (n : ℝ≥0) with hin | hni
      · have he : {ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} ∩ {ω | Th ω ≤ (i : ℝ≥0∞)} = {ω | Th ω ≤ (i : ℝ≥0∞)} := by
          refine inter_eq_right.2 fun ω (hω : Th ω ≤ i) => ?_
          exact lt_of_le_of_lt hω (by exact_mod_cast hin)
        rw [he]; exact hThs i
      · have he : {ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} ∩ {ω | Th ω ≤ (i : ℝ≥0∞)} = {ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} := by
          refine inter_eq_left.2 fun ω (hω : Th ω < (n : ℝ≥0)) => ?_
          exact le_trans hω.le (by exact_mod_cast hni)
        rw [he]; exact 𝓖.mono hni _ (hThs.measurableSet_lt (n : ℝ≥0))
    refine ((hTns n).measurableSet _).2 ⟨?_, key⟩
    have h := key (n : ℝ≥0)
    have hsub : A n ∩ {ω | ((Tn n ω : ℝ≥0) : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} = A n :=
      inter_eq_left.2 fun ω _ => by
        show ((Tn n ω : ℝ≥0) : ℝ≥0∞) ≤ ((n : ℝ≥0) : ℝ≥0∞)
        rw [hTn_coe]; exact min_le_right _ _
    rw [hsub] at h
    exact le_iSup (fun t => 𝓖 t) (n : ℝ≥0) _ h
  have hAT : ∀ n, ∀ ω ∈ A n, ((Tn n ω : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
      (0 < Tn n ω ∨ ∀ i j, (fun _ : Fin 1 => (0 : ℝ)) i < (fun _ : Fin 1 => (0 : ℝ)) j) := fun n ω hω => by
    obtain ⟨hζ, -⟩ := hgood ω hω.1
    obtain ⟨m, hm, hm1, -⟩ := hhit ω hω.1
    refine ⟨by rw [hζ]; exact ENNReal.coe_lt_top, Or.inl ?_⟩
    have hTm : Tn n ω = m := by exact_mod_cast (hTnA n ω hω).trans hm
    rw [hTm]; exact lt_of_lt_of_le one_pos hm1
  -- the restart formula
  have hlaw := fun n => measure_restart_codeEvent hκ hE (hTns n) (hAm n) (hAT n)
    (Φ := NonTransientEvent) measurableSet_ntCodeSet (fun _ _ _ => Iff.rfl) nonTransientEvent_congr
  -- the future has no non-transient trace
  have hLHS : ∀ n, A n ∩ {ω | NonTransientEvent (fun t => W (Tn n ω + t) ω - W (Tn n ω) ω)
      (ζ ω - Tn n ω)} = ∅ := by
    intro n
    refine eq_empty_iff_forall_notMem.2 fun ω ⟨hω, hnt⟩ => ?_
    obtain ⟨hζ, hwc, hw0, -, -, -, -, ⟨η, hη⟩, htr⟩ := hgood ω hω.1
    have hζ' : ζ ω - Tn n ω = ⊤ := by rw [hζ]; exact ENNReal.top_sub_coe
    have hnt' : NonTransientEvent (Sec7.shiftNN (fun t => W t ω) (Tn n ω)) ⊤ := by
      rw [← hζ']; exact hnt
    have hwc₂ : Continuous (Sec7.shiftNN (fun t => W t ω) (Tn n ω)) :=
      (hwc.comp (continuous_const.add continuous_id)).sub continuous_const
    rw [nonTransientEvent_iff hwc₂ (Sec7.shiftNN_zero _ _)] at hnt'
    obtain ⟨⟨η₂, hη₂⟩, hnot⟩ := hnt'
    exact hnot ⟨η₂, hη₂, tendsto_norm_of_shift hwc hw0 hη (htr η hη) hη₂⟩
  -- the restarted word lies on the ray
  have hRHS : ∀ n, ∫⁻ ω in A n, codeLaw κ ρL ρR ntCodeSet (wordAt W VL VR (Tn n) ω) ∂P = K * P (A n) := by
    intro n
    have hAmeas : MeasurableSet (A n) := (hTns n).measurableSpace_le _ (hAm n)
    rw [← setLIntegral_const]
    refine setLIntegral_congr_fun hAmeas fun ω hω => ?_
    obtain ⟨-, -, -, -, -, hsep, -⟩ := hgood ω hω.1
    obtain ⟨m, hm, hm1, hYm⟩ := hhit ω hω.1
    have hTm : Tn n ω = m := by exact_mod_cast (hTnA n ω hω).trans hm
    have hL : 0 < W m ω - VL 0 m ω := sub_pos.2 (hsep m (lt_of_lt_of_le one_pos hm1))
    have hYm' : VR 0 m ω - W m ω = r * (W m ω - VL 0 m ω) := by
      simp only [hY, ratioGap] at hYm; linarith
    have hword : wordAt W VL VR (Tn n) ω =
        ((fun _ => -(W m ω - VL 0 m ω)), fun _ => r * (W m ω - VL 0 m ω)) := by
      simp only [wordAt, hTm]
      refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
      · rw [Fin.fin_one_eq_zero i]; simp only; ring
      · rw [Fin.fin_one_eq_zero j]; exact hYm'
    rw [hword, hdil _ hL]
  have hzero : ∀ n, K * P (A n) = 0 := fun n => by
    rw [← hRHS n, ← hlaw n, hLHS n, measure_empty]
  -- some restart event has positive probability
  have hcover : Nᶜ ⊆ ⋃ n, A n := fun ω hω => by
    obtain ⟨m, hm, -, -⟩ := hhit ω hω
    obtain ⟨n, hn⟩ := exists_nat_gt (m : ℝ)
    refine mem_iUnion.2 ⟨n, hω, ?_⟩
    show Th ω < ((n : ℝ≥0) : ℝ≥0∞)
    rw [hm]
    exact_mod_cast (show m < (n : ℝ≥0) by rw [← NNReal.coe_lt_coe]; exact_mod_cast hn)
  by_contra hK
  have hA0 : ∀ n, P (A n) = 0 := fun n => (mul_eq_zero.1 (hzero n)).resolve_left hK
  have h0 : P Nᶜ = 0 := measure_mono_null hcover (measure_iUnion_null hA0)
  have h1 : P Nᶜ = 1 := by
    rw [prob_compl_eq_one_sub (𝓖.le 0 _ (hNm 0)), hN0, tsub_zero]
  rw [h0] at h1
  exact zero_ne_one h1

end Restart

/-! ### The transfer -/

section Transfer

variable {κ : ℝ}

/-- **The gap-ratio transfer, kernel form** (every `κ > 0`): given the recurrence of the gap ratio and two-seed
transience, if the canonical probability of a non-transient trace is constant (`= K`) along the ray of words
`(−L, r L)`, `L > 0`, then `K = 0`. The two-seed evolution is the canonical one (`Sec2.exists_isIntegratedSLEEvolution_twoSeed`),
taken in the usual augmentation of its filtration so that null sets are measurable at every time. -/
theorem codeLaw_nt_eq_zero_of_ratio (hκ : 0 < κ) (hrec : TwoSeedRatioRecurrenceStatement.{0} κ)
    (htwo : TwoSeedTransienceStatement.{0} κ) {ρL ρR : Fin 1 → ℝ}
    (hadm0 : Sec4.HasAdmissiblePartialSums κ ρL ρR (fun _ => 0) (fun _ => 0)) {r : ℝ} (hr : 0 < r)
    {K : ℝ≥0∞} (hdil : ∀ L : ℝ, 0 < L → codeLaw κ ρL ρR ntCodeSet ((fun _ => -L), fun _ => r * L) = K) :
    K = 0 := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ := Sec2.exists_isIntegratedSLEEvolution_twoSeed hκ
    (xL := fun _ => (0 : ℝ)) (xR := fun _ => (0 : ℝ)) (fun _ => rfl) (fun _ => rfl) ρL ρR
  have hEa := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hgood : ∀ᵐ ω ∂P, GoodRatio r W VL VR ζ ω := by
    filter_upwards [Sec4.aux6Statement hκ _ _ ρL ρR P 𝓕 W VL VR B ζ isOrderedForceWord_zero hadm0 hE,
      hrec ρL ρR hadm0 P 𝓕 W VL VR B ζ hE r hr, htwo ρL ρR hadm0 P 𝓕 W VL VR B ζ hE,
      IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hκ isOrderedForceWord_zero hadm0 hE,
      hE.2.2.2.2] with ω ⟨hζ, hsep⟩ ⟨t₀, ht₀, hz⟩ htr ⟨_, _, η, hη⟩ hp
    have hcont : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < ζ ω} → Continuous f := fun hf =>
      continuousOn_univ.1 (hf.mono fun t _ => by
        show (t : ℝ≥0∞) < ζ ω
        rw [hζ]; exact ENNReal.coe_lt_top)
    refine ⟨hζ, hcont hp.2.2.2.1, hp.1, hcont (hp.2.2.2.2.1 0), hcont (hp.2.2.2.2.2.1 0),
      fun t ht => (hsep t ht).1 0, ⟨t₀, ht₀, ?_⟩, ⟨η, hη⟩, htr⟩
    simp only [ratioGap]
    linarith
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  exact eq_zero_of_restart_ratio hκ hEa (N := N)
    (fun t => Ito.measurableSet_usualAugmentation_of_null hNm hN0 t) hN0
    (fun ω hω => by
      by_contra h
      exact hω (hNsub h)) hdil

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL xR ρL ρR : Fin 1 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **Separated two-force transience** (B.3 L1266–L1279: "This proves all two-force bases, including equality at the
nonhitting threshold"), every `κ > 0`: for marks `x_L < 0 < x_R` with weights `ρ_L, ρ_R ≥ κ/2 − 2` (admissible),
given the recurrence of the two-seed gap ratio and two-seed transience, almost surely every continuous generating
trace on `[0, ∞)` tends to `∞`. -/
theorem IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoForce (hκ : 0 < κ)
    (hrec : TwoSeedRatioRecurrenceStatement.{0} κ) (htwo : TwoSeedTransienceStatement.{0} κ)
    (hxL : xL 0 < 0) (hxR : 0 < xR 0) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  obtain ⟨hwL, hwR⟩ := weights_of_hasAdmissiblePartialSums hadm hxL hxR
  have hadm0 := hasAdmissiblePartialSums_seed hwL hwR
  have hxL' : ∀ i, xL i < 0 := fun i => by rw [Fin.fin_one_eq_zero i]; exact hxL
  have hxR' : ∀ j, 0 < xR j := fun j => by rw [Fin.fin_one_eq_zero j]; exact hxR
  have hF : IsOrderedForceWord xL xR :=
    ⟨fun i j _ => by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j], fun i => (hxL' i).le,
      fun i j _ => by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j], fun j => (hxR' j).le⟩
  have hsep : ∀ i j, xL i < xR j := fun i j => (hxL' i).trans (hxR' j)
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ :=
    (Sec4.aux6Statement hκ xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hE).mono fun _ h => h.1
  set r : ℝ := xR 0 / (-xL 0) with hr
  have hr0 : 0 < r := div_pos hxR (neg_pos.2 hxL)
  have hK := codeLaw_nt_eq_zero_of_ratio hκ hrec htwo hadm0 hr0 (K := codeLaw κ ρL ρR ntCodeSet (xL, xR))
    fun L hL => by
      have hxL0 : 0 < -xL 0 := neg_pos.2 hxL
      have hxne : xL 0 ≠ 0 := hxL.ne
      set c : ℝ≥0 := ⟨((-xL 0) / L) ^ 2, by positivity⟩ with hcdef
      have hc : c ≠ 0 := by
        intro h
        have : ((-xL 0) / L) ^ 2 = 0 := congrArg NNReal.toReal h
        exact (pow_pos (div_pos hxL0 hL) 2).ne' this
      have hsc : (√(c : ℝ))⁻¹ = L / (-xL 0) := by
        rw [show (c : ℝ) = ((-xL 0) / L) ^ 2 from rfl, Real.sqrt_sq (div_pos hxL0 hL).le, inv_div]
      rw [← codeLaw_nt_dilate hκ hsep hE hζ hc]
      congr 1
      refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
      · rw [Fin.fin_one_eq_zero i]
        show -L = (√(c : ℝ))⁻¹ * xL 0
        rw [hsc]
        field_simp
      · rw [Fin.fin_one_eq_zero j]
        show r * L = (√(c : ℝ))⁻¹ * xR 0
        rw [hsc, hr]
        field_simp
  rw [← measure_nonTransient_eq_codeLaw hκ hsep hE] at hK
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hK,
    hE.ae_exists_isGeneratingTrace_top_of_hasAdmissiblePartialSums hκ hF hadm hxL' hxR', hE.2.2.2.2]
    with ω hnt ⟨hζω, η₀, hη₀⟩ hp η hη
  have hwc : Continuous fun t => W t ω := by
    have h := hp.2.2.2.1
    rw [hζω] at h
    exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)
  have hnt' : ¬ NonTransientEvent (fun t => W t ω) ⊤ := by
    rw [← hζω]; exact hnt
  rw [nonTransientEvent_iff hwc hp.1] at hnt'
  obtain ⟨η₁, hη₁, htr₁⟩ : HasTransTrace (fun t => W t ω) := by
    by_contra h
    exact hnt' ⟨⟨η₀, hη₀⟩, h⟩
  refine htr₁.congr fun t => ?_
  rw [hη.eq_of_le hη₁ hwc.continuousOn hp.1 le_top]

/-- Separated two-force transience for `κ ≤ 4`, given only the recurrence of the two-seed gap ratio (two-seed
transience is PROVE-ZHAN-B2's). -/
theorem IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoForce_of_le_four (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hrec : TwoSeedRatioRecurrenceStatement.{0} κ) (hxL : xL 0 < 0) (hxR : 0 < xR 0)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop :=
  IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoForce hκ hrec
    (twoSeedTransienceStatement_of_le_four hκ hκ4) hxL hxR hadm hE

/-- Separated two-force transience for every `κ > 0`, given the recurrence of the two-seed gap ratio and the absence
of real terminal cluster points for separated two-force laws (Lemma 3.4). -/
theorem IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoForce_of_separatedNoCluster (hκ : 0 < κ)
    (hrec : TwoSeedRatioRecurrenceStatement.{0} κ) (hN : SeparatedNoRealClusterStatement.{0} κ)
    (hxL : xL 0 < 0) (hxR : 0 < xR 0) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop :=
  IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoForce hκ hrec
    (twoSeedTransienceStatement_of_separatedNoCluster hκ hN) hxL hxR hadm hE

end Transfer

end InteractingSLE.ZhanGT4
