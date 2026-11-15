/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TrialsHiBand
import InteractingSLE.WangWu.Continuity2Band
import InteractingSLE.Spec.Supplement.LP8Singleton
import InteractingSLE.Spec.Supplement.LP1Seed

/-!
# Aux. lemma 113's third sector and Lemma LP8's new sector from the trial bounds

Packet PROVE-TRIALS-HI. The three transience statements of the packet, for every `κ` at which their premises are
stated, from Aux. lemma 101 (`Aux101BandClockStatement`) and the uniform trial bound of the sector (the conclusion of
Aux. lemmas 109–111 in trial form):

* `WangWu.LowSide.LPAux113HighTransienceStatement κ` (both side totals `> κ/2 − 4`; at `κ = 4` Wang–Wu's Proposition
  7.3 configuration) from `HighTrialStatement κ` (`lpAux113HighTransienceStatement_of_trials`);
* `WangWu.LowSide.Aux113HighTransienceStatement` (the `κ < 4` form) from the same statements for `κ < 4`
  (`aux113HighTransienceStatement_of_trials`, for PROVE-SEC7-C8);
* `LP.LP8TransienceStatement κ` (Lemma LP8's new sector: a right singleton of weight in `(−2, κ/2 − 4]`) from
  `LP8TrialStatement κ` (`lp8TransienceStatement_of_trials`).

The trial statements are the named inputs that remain: the uniform lower bound of Aux. lemmas 109/111 (and of the
strengthened singleton experiment, p. 485) over the midpoint words (nearest marks `∓1`, marks in `[−M, M]`). The
proofs here need no merger hypothesis: the conclusion holds off a merger too, so the source's restriction to
`{no merger}` is not used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace TrialsHi

open ZhanGT4 Zhan Sec7.RandRestart Sec2 Sec2.Assembly Sec2.Restart

/-! ### The named trial statements -/

/-- **Named input: the uniform trial bound in Aux. lemma 113's third sector** (Specification p. 364, Aux. lemma 111,
and p. 370, "For each deterministic integer `M`, fix in advance the reference event and cutoff choices in Aux. lemma
111 … It gives a positive lower bound `p = p(M)` for transience or a finite whole-side swallow, the same at every
subsequent trial"). For `N ≥ 3`, under the smaller-count hypothesis, the weights of a word with `N` marks, at least one
on each side, whose side totals both exceed `κ/2 − 4` have the uniform trial bound. -/
def HighTrialStatement (κ : ℝ) : Prop :=
  ∀ N : ℕ, 3 ≤ N → LP.DistinctCompleteBelow.{u} κ N →
    ∀ {nL nR : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ), nL + 1 + (nR + 1) = N →
      (κ / 2 - 4 < ∑ i, ρL i ∧ κ / 2 - 4 < ∑ i, ρR i) → UniformTrialBound κ ρL ρR

/-- **Named input: the uniform trial bound of Lemma LP8's strengthened singleton experiment** (supplement p. 485,
LP8's proof: "Now repeat Aux. lemma 113's adapted midpoint trials with this experiment"; Aux. lemma 111, the
strengthened
version with a sole admissible mark). For `N ≥ 3`, under the smaller-count hypothesis, the weights of a word with
`N − 1` left marks of total `> κ/2 − 4` and one right mark of weight in `(−2, κ/2 − 4]` have the uniform trial
bound. -/
def LP8TrialStatement (κ : ℝ) : Prop :=
  ∀ N : ℕ, 3 ≤ N → LP.DistinctCompleteBelow.{u} κ N →
    ∀ {nL : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin 1 → ℝ), nL + 1 + 1 = N → -2 < ρR 0 → ρR 0 ≤ κ / 2 - 4 →
      κ / 2 - 4 < ∑ i, ρL i → UniformTrialBound κ ρL ρR

/-! ### From the trial bound to transience -/

section Word

variable {nL nR : ℕ} {κ : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}

/-- **Transience from the trial bound, for one word** (every `κ > 0`): under the smaller-count hypothesis with
`nL + 1, nR + 1 < N`, Aux. lemma 101 and the uniform trial bound, every evolution of every ordered start with these
weights is almost surely transient on an infinite lifetime. -/
theorem ae_tendsto_of_trialBound (hκ : 0 < κ) {N : ℕ} (hD : LP.DistinctCompleteBelow.{u} κ N)
    (h101 : Aux101BandClockStatement.{u} κ) (hnL : nL + 1 < N) (hnR : nR + 1 < N)
    (hU : UniformTrialBound κ ρL ρR) {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ}
    (hF : IsOrderedForceWord xL xR) {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
    {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ → ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop := by
  have h0 : ∀ (yL : Fin (nL + 1) → ℝ) (yR : Fin (nR + 1) → ℝ), IsOrderedForceWord yL yR →
      (∀ i j, yL i < yR j) → codeLaw κ ρL ρR ntCodeSet (yL, yR) = 0 := by
    intro yL yR hFy hsepy
    obtain ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', hE'⟩ :=
      LP.exists_isIntegratedSLEEvolution_ulift.{u} hκ hFy (ρL := ρL) (ρR := ρR)
    rw [← measure_nonTransient_eq_codeLaw hκ hsepy hE']
    have h := ae_iff.1 (ae_not_nonTransientEvent_sep hκ hD h101 hFy hsepy hnL hnR hU hE')
    simpa only [not_not] using h
  filter_upwards [ae_not_nonTransientEvent_of_codeLaw hκ h0 hF hE, hE.2.2.2.2] with ω h hp hζ η hη
  have hwc : Continuous fun t => W t ω :=
    continuousOn_univ.1 (hp.isForcePath.continuousOn_w.mono fun t _ => by rw [hζ]; exact ENNReal.coe_lt_top)
  rw [hζ, not_nonTransientEvent_iff hwc hp.1] at h
  exact h η hη

end Word

/-! ### The three statements -/

/-- **`WangWu.LowSide.LPAux113HighTransienceStatement κ` from Aux. lemma 101 and the third-sector trial bound**
(every `κ > 0`). -/
theorem lpAux113HighTransienceStatement_of_trials {κ : ℝ} (hκ : 0 < κ)
    (h101 : Aux101BandClockStatement.{u} κ) (hT : HighTrialStatement.{u} κ) :
    WangWu.LowSide.LPAux113HighTransienceStatement.{u} κ := by
  intro N hN hD _ nL nR xL xR ρL ρR hd hc hL hR hs Ω mΩ P _ 𝓕 W VL VR B ζ hE
  obtain ⟨m, rfl⟩ : ∃ m, nL = m + 1 := ⟨nL - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, nR = k + 1 := ⟨nR - 1, by omega⟩
  filter_upwards [ae_tendsto_of_trialBound hκ hD h101 (by omega) (by omega) (hT N hN hD ρL ρR hc hs) hd.1 hE]
    with ω h hζ _ η hη
  exact h hζ η hη

/-- **`WangWu.LowSide.Aux113HighTransienceStatement` (the `κ < 4` form) from Aux. lemma 101 and the third-sector trial
bound for `0 < κ < 4`** (for PROVE-SEC7-C8). -/
theorem aux113HighTransienceStatement_of_trials
    (h101 : ∀ κ : ℝ, 0 < κ → κ < 4 → Aux101BandClockStatement.{u} κ)
    (hT : ∀ κ : ℝ, 0 < κ → κ < 4 → HighTrialStatement.{u} κ) :
    WangWu.LowSide.Aux113HighTransienceStatement.{u} := by
  intro κ hκ hκ4 N hN hbelow nL nR xL xR ρL ρR hd hc hL hR hs Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hD : LP.DistinctCompleteBelow.{u} κ N := fun xL xR ρL ρR hd hlt =>
    hbelow xL xR ρL ρR hd (by omega)
  obtain ⟨m, rfl⟩ : ∃ m, nL = m + 1 := ⟨nL - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, nR = k + 1 := ⟨nR - 1, by omega⟩
  filter_upwards [ae_tendsto_of_trialBound hκ hD (h101 κ hκ hκ4) (by omega) (by omega)
    (hT κ hκ hκ4 N hN hD ρL ρR hc hs) hd.1 hE] with ω h hζ _ η hη
  exact h hζ η hη

/-- **`LP.LP8TransienceStatement κ` from Aux. lemma 101 and the trial bound of LP8's strengthened singleton
experiment** (every `κ > 0`). -/
theorem lp8TransienceStatement_of_trials {κ : ℝ} (hκ : 0 < κ) (h101 : Aux101BandClockStatement.{u} κ)
    (hT : LP8TrialStatement.{u} κ) : LP.LP8TransienceStatement.{u} κ := by
  intro N hN hD _ nL xL xR ρL ρR hd hsum hr hrd hl Ω mΩ P _ 𝓕 W VL VR B ζ hE
  obtain ⟨m, rfl⟩ : ∃ m, nL = m + 1 := ⟨nL - 1, by omega⟩
  filter_upwards [ae_tendsto_of_trialBound (nR := 0) hκ hD h101 (by omega) (by omega)
    (hT N hN hD ρL ρR hsum hr hrd hl) hd.1 hE] with ω h hζ _ η hη
  exact h hζ η hη

end TrialsHi

end Sec7

end InteractingSLE
