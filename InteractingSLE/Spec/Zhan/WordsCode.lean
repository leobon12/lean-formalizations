/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb3Random

/-!
# Late returns of a transient canonical trace

Packet PROVE-ZHAN-B4. For the whole-tail comparison, the reference word enters only through its canonical law
(`Sec7.RandRestart.codeLaw`, the Wiener probability of a coded event of the canonical solution). This file defines the
Borel set `lateSet k R` of solution codes with infinite lifetime whose trace (read by the measurable evaluation
`LP.traceAt`) is in the closed disc of radius `R` at some rational time `≥ k`, and proves:

* `codeLaw_lateSet_tendsto_zero`: if an integrated evolution of a separated word has, almost surely, the trace event
  (a continuous generating trace, transient when the lifetime is infinite), then the canonical probability of a late
  return to the disc tends to `0` as `k → ∞`;
* `codeLaw_lifetime_eq_top`: if its lifetime is almost surely infinite, the canonical probability of an infinite
  lifetime is one.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Zhan

open Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart

variable {nL nR : ℕ}

/-- The decoded driver is a measurable function of the code. -/
theorem measurable_cw : Measurable (cw : XCode nL nR → ℝ≥0 → ℝ) :=
  measurable_pi_iff.2 fun t => measurable_dec_at measurable_code_w t

/-- **Late returns**: codes with infinite lifetime whose trace is within `R` of `0` at a rational time `≥ k`. -/
def lateSet (k : ℕ) (R : ℝ) : Set (XCode nL nR) :=
  {x | cζ x = ⊤ ∧ ∃ p : ℚ≥0, (k : ℚ≥0) ≤ p ∧ ‖LP.traceAt (p : ℝ≥0) (cw x)‖ ≤ R}

theorem measurableSet_lateSet (k : ℕ) (R : ℝ) : MeasurableSet (lateSet (nL := nL) (nR := nR) k R) := by
  have h1 : MeasurableSet {x : XCode nL nR | cζ x = ⊤} := measurable_cζ (measurableSet_singleton ⊤)
  have h2 : ∀ p : ℚ≥0, MeasurableSet {x : XCode nL nR | ‖LP.traceAt (p : ℝ≥0) (cw x)‖ ≤ R} := fun p =>
    measurableSet_le ((LP.measurable_traceAt _).comp measurable_cw).norm measurable_const
  have e : lateSet (nL := nL) (nR := nR) k R =
      {x | cζ x = ⊤} ∩ ⋃ p : ℚ≥0, ⋃ (_ : (k : ℚ≥0) ≤ p), {x | ‖LP.traceAt (p : ℝ≥0) (cw x)‖ ≤ R} := by
    ext x; simp [lateSet]
  rw [e]
  exact h1.inter (MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun _ => h2 p)

theorem antitone_lateSet (R : ℝ) : Antitone fun k : ℕ => lateSet (nL := nL) (nR := nR) k R := by
  intro k k' hk x ⟨hζ, p, hp, hR⟩
  exact ⟨hζ, p, le_trans (by exact_mod_cast hk) hp, hR⟩

/-- The law set of an intersection is the intersection of the law sets (codes from separated starts are
determined by the start and the driving code). -/
theorem lawSetS_iInter {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (S : ℕ → Set (XCode nL nR)) :
    lawSetS a ρL ρR (⋂ k, S k) = ⋂ k, lawSetS a ρL ρR (S k) := by
  unfold lawSetS
  rw [← (injOn_startOf_fst a ρL ρR).mono (iUnion_subset fun k => inter_subset_left) |>.image_iInter_eq,
    inter_iInter]

/-- The canonical law of an intersection of a decreasing sequence of Borel code events is the limit. -/
theorem tendsto_codeLaw_of_antitone {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {S : ℕ → Set (XCode nL nR)} (hS : ∀ k, MeasurableSet (S k)) (hanti : Antitone S)
    (s : (Fin nL → ℝ) × (Fin nR → ℝ)) :
    Tendsto (fun k => codeLaw a ρL ρR (S k) s) atTop (𝓝 (codeLaw a ρL ρR (⋂ k, S k) s)) := by
  have e : Prod.mk s ⁻¹' restartSetS a ρL ρR (⋂ k, S k) =
      ⋂ k, Prod.mk s ⁻¹' restartSetS a ρL ρR (S k) := by
    ext f
    simp only [restartSetS, mem_preimage, mem_ofPred_eq, lawSetS_iInter, mem_iInter]
  unfold codeLaw
  rw [e]
  exact tendsto_measure_iInter_atTop
    (fun k => ((measurableSet_restartSetS (hS k)).preimage measurable_prodMk_left).nullMeasurableSet)
    (fun k k' hk => preimage_mono fun p hp => by
      simp only [restartSetS, mem_ofPred_eq] at hp ⊢
      unfold lawSetS at hp ⊢
      exact image_mono (inter_subset_inter_right _ (hanti hk)) hp)
    ⟨0, measure_ne_top _ _⟩

/-- **Late returns of a transient trace are rare.** If an integrated evolution of a separated word has, almost
surely, the trace event, the canonical probability of a late return to the disc of radius `R` tends to `0`. -/
theorem codeLaw_lateSet_tendsto_zero {a : ℝ} (ha : 0 < a) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hsep : ∀ i j, xL i < xR j) {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (htr : ∀ᵐ ω ∂P, TraceEvent (fun t => W t ω) (ζ ω)) (R : ℝ) :
    Tendsto (fun k => codeLaw a ρL ρR (lateSet k R) (xL, xR)) atTop (𝓝 0) := by
  have hlim := tendsto_codeLaw_of_antitone (a := a) (ρL := ρL) (ρR := ρR)
    (fun k => measurableSet_lateSet (nL := nL) (nR := nR) k R) (antitone_lateSet R) (xL, xR)
  convert hlim using 2
  set Φ : (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop := fun w τ =>
    τ = ⊤ ∧ ∀ k : ℕ, ∃ p : ℚ≥0, (k : ℚ≥0) ≤ p ∧ ‖LP.traceAt (p : ℝ≥0) w‖ ≤ R with hΦ
  have hmeas : MeasurableSet (⋂ k, lateSet (nL := nL) (nR := nR) k R) :=
    MeasurableSet.iInter fun k => measurableSet_lateSet k R
  have hcode := measure_eventOf_eq_codeLaw ha hsep hE (Φ := Φ) hmeas
    (fun x _ _ => by
      simp only [mem_iInter, lateSet, mem_ofPred_eq, hΦ]
      exact ⟨fun h => ⟨(h 0).1, fun k => (h k).2⟩, fun h k => ⟨h.1, h.2 k⟩⟩)
    (fun w w' τ hww' h => by
      obtain ⟨hτ, hk⟩ := h
      refine ⟨hτ, fun k => ?_⟩
      obtain ⟨p, hp, hpR⟩ := hk k
      refine ⟨p, hp, ?_⟩
      rwa [← LP.traceAt_congr fun r _ => hww' r (by rw [hτ]; exact ENNReal.coe_lt_top)])
  rw [← hcode, eq_comm]
  refine measure_eq_zero_iff_ae_notMem.2 ?_
  filter_upwards [htr, hE.2.2.2.2] with ω hω hpath
  rintro ⟨hζ, hk⟩
  obtain ⟨η, hη, htend⟩ := hω
  have htend' := htend hζ
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((tendsto_atTop.1 htend') (R + 1))
  obtain ⟨p, hp, hpR⟩ := hk ⌈(K : ℝ)⌉₊
  have hwc : ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < ζ ω} := hpath.2.2.2.1
  have heq := LP.traceAt_eq_of_isGeneratingTrace hη hwc hpath.1 (s := (p : ℝ≥0))
    (by rw [hζ]; exact ENNReal.coe_lt_top)
  have hKp : K ≤ (p : ℝ≥0) := by
    have h1 : (K : ℝ) ≤ ⌈(K : ℝ)⌉₊ := Nat.le_ceil _
    have h2 : ((⌈(K : ℝ)⌉₊ : ℚ≥0) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have : (K : ℝ) ≤ (p : ℝ) := h1.trans (by exact_mod_cast h2)
    exact_mod_cast this
  have := hK _ hKp
  rw [← heq] at this
  linarith

/-- **Infinite canonical lifetime.** If an integrated evolution of a separated word has almost surely infinite
lifetime, the canonical probability of an infinite lifetime is one. -/
theorem codeLaw_lifetime_eq_top {a : ℝ} (ha : 0 < a) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hsep : ∀ i j, xL i < xR j) {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    codeLaw a ρL ρR {x | cζ x = ⊤} (xL, xR) = 1 := by
  have hcode := measure_eventOf_eq_codeLaw ha hsep hE (Φ := fun _ τ => τ = ⊤)
    (measurable_cζ (measurableSet_singleton ⊤)) (fun x _ _ => Iff.rfl) (fun _ _ _ _ h => h)
  change codeLaw a ρL ρR (cζ ⁻¹' {⊤}) (xL, xR) = 1
  rw [← hcode]
  have h0 : P {ω | ζ ω = ⊤}ᶜ = 0 := by
    rw [compl_ofPred]; exact ae_iff.1 hζ
  exact (measure_congr (ae_eq_univ.2 h0)).trans measure_univ

end InteractingSLE.Zhan
