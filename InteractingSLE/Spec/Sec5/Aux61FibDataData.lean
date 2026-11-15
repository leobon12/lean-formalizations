/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61FibDataGood

/-!
# The glued-space fibre objects, VIII: fibre data with the window's clearance and a history-dependent correction

Packet PROVE-AUX61-FIBDATA (piece (W) of `planning/handoffs/PROVE-AUX61-FIB.md`).

* **`fibDataOfWindow`**: the fibre data of a reference word, a window `V ∋ 0` (open) inside a buffer with compact
  closure, a correction `q` harmonic on `ℍ` with zero boundary values on `O₀`, whose clearance is **`clr V`**
  (`ofWindow_ℓ`, `ofWindow_V`) — the form `Aux61FibDataCover.hasDyActFibreCover_of_restart` consumes.
* **`withQ d q`**: `d` with its correction replaced by `q` when `q` is admissible (`ValidQ d q`: harmonic on
  `ℍ`, zero boundary values on `d.O₀`), and `d` otherwise; it keeps the word, window, clearance, `O₀` and buffer
  (`withQ_V`, `withQ_ℓ`, …, `withQ_q_of_valid`). With a history-dependent `Q z`, **`measurable_withQ_q`** gives the
  joint measurability `(z, w) ↦ (withQ d (Q z)).q w` (the `hqm` input of the cover) from a measurable admissibility
  event and a jointly measurable `Q`.

Generic. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec5.Aux61FibData

open Aux61Fib

/-- A set with compact closure has nonempty complement. -/
theorem compl_nonempty_of_isCompact_closure {A : Set ℂ} (hA : IsCompact (closure A)) : Aᶜ.Nonempty := by
  by_contra hemp
  rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hemp
  have hb := hA.isBounded.subset (subset_closure (s := A))
  rw [hemp] at hb
  exact NormedSpace.unbounded_univ ℝ ℂ hb

/-- **Fibre data whose clearance is that of the window.** -/
def fibDataOfWindow (κ : ℝ) (hκ : 0 < κ) (bR : ℝ → ℝ) (JR : Finset ℝ)
    (hpc : IsPiecewiseConstantBoundaryData bR JR)
    (hseed : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ bR JR 0 0) (flowLineRhoR κ bR JR 0 0) 0
      (flowLineXL bR JR 0) (flowLineXR bR JR 0))
    (V : Set ℂ) (hVo : IsOpen V) (hV0 : (0 : ℂ) ∈ V) (q : ℂ → ℝ) (hq : InnerProductSpace.HarmonicOnNhd q H)
    (O₀ : Set ℝ) (hO₀ : IsOpen O₀) (hq0 : ∀ x ∈ O₀, Tendsto q (𝓝[H] (x : ℂ)) (𝓝 0)) (buffer : Set ℂ)
    (hbo : IsOpen buffer) (hbc : IsCompact (closure buffer))
    (hbr : ∀ z ∈ closure buffer, z.im = 0 → z.re ∈ O₀) (hVb : V ⊆ buffer) : FibData where
  κ := κ
  κ_pos := hκ
  bR := bR
  JR := JR
  bR_pc := hpc
  seed := hseed
  V := V
  ℓ := clr V
  ℓ_cont := continuous_clr V
  ℓ_zero := (clr_pos_iff hVo (compl_nonempty_of_isCompact_closure
    (hbc.of_isClosed_subset isClosed_closure (closure_mono hVb)))).2 hV0
  q := q
  q_harm := hq
  O₀ := O₀
  O₀_open := hO₀
  q_zero := hq0
  buffer := buffer
  buffer_open := hbo
  zero_mem := hVb hV0
  buffer_compact := hbc
  buffer_real := hbr
  V_sub := hVb

/-- **An admissible correction** for the data `d`: harmonic on `ℍ`, zero boundary values on `d.O₀`. -/
def ValidQ (d : FibData) (q : ℂ → ℝ) : Prop :=
  InnerProductSpace.HarmonicOnNhd q H ∧ ∀ x ∈ d.O₀, Tendsto q (𝓝[H] (x : ℂ)) (𝓝 0)

open scoped Classical in
/-- **The data with the correction `q`** when it is admissible (`d` otherwise). -/
def withQ (d : FibData) (q : ℂ → ℝ) : FibData :=
  if hq : ValidQ d q then { d with q := q, q_harm := hq.1, q_zero := hq.2 } else d

section WithQ

variable (d : FibData) (q : ℂ → ℝ)

theorem withQ_V : (withQ d q).V = d.V := by unfold withQ; split_ifs <;> rfl
theorem withQ_ℓ : (withQ d q).ℓ = d.ℓ := by unfold withQ; split_ifs <;> rfl
theorem withQ_κ : (withQ d q).κ = d.κ := by unfold withQ; split_ifs <;> rfl
theorem withQ_bR : (withQ d q).bR = d.bR := by unfold withQ; split_ifs <;> rfl
theorem withQ_JR : (withQ d q).JR = d.JR := by unfold withQ; split_ifs <;> rfl
theorem withQ_O₀ : (withQ d q).O₀ = d.O₀ := by unfold withQ; split_ifs <;> rfl
theorem withQ_buffer : (withQ d q).buffer = d.buffer := by unfold withQ; split_ifs <;> rfl

theorem withQ_q_of_valid (hq : ValidQ d q) : (withQ d q).q = q := by
  unfold withQ; simp only [hq, ↓reduceDIte]

theorem withQ_q_of_not_valid (hq : ¬ ValidQ d q) : (withQ d q).q = d.q := by
  unfold withQ; simp only [hq, ↓reduceDIte]

end WithQ

/-- **Joint measurability of a history-dependent correction** (the input `hqm` of the cover): if the corrections
`Q z` are jointly measurable in `(z, w)`, the fallback correction `d.q` is measurable and the admissibility event is
measurable, then `(z, w) ↦ (withQ d (Q z)).q w` is measurable. -/
theorem measurable_withQ_q {β : Type*} [MeasurableSpace β] (d : FibData) {Q : β → ℂ → ℝ}
    (hQ : Measurable fun p : β × ℂ => Q p.1 p.2) (hd : Measurable d.q)
    (hval : MeasurableSet {z | ValidQ d (Q z)}) :
    Measurable fun p : β × ℂ => (withQ d (Q p.1)).q p.2 := by
  classical
  have e : (fun p : β × ℂ => (withQ d (Q p.1)).q p.2) =
      fun p => if p.1 ∈ {z | ValidQ d (Q z)} then Q p.1 p.2 else d.q p.2 := by
    funext p
    by_cases hp : ValidQ d (Q p.1)
    · have hp' : p.1 ∈ {z | ValidQ d (Q z)} := hp
      rw [withQ_q_of_valid d _ hp]; simp only [hp', ↓reduceIte]
    · have hp' : p.1 ∉ {z | ValidQ d (Q z)} := hp
      rw [withQ_q_of_not_valid d _ hp]; simp only [hp', ↓reduceIte]
  rw [e]
  exact Measurable.ite (measurable_fst hval) hQ (hd.comp measurable_snd)

end InteractingSLE.Sec5.Aux61FibData
