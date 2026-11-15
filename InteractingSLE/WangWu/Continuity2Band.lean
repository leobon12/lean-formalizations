/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb6Inputs
import InteractingSLE.Spec.Sec7.ContinuityProb3Steps
import InteractingSLE.Spec.Theorem13Inputs

/-!
# Two-sided words with a side total at most `−2` (Aux. lemma 113's first two sectors, every κ)

Packet PROVE-WW-C2. Aux. lemma 113 (Specification pp. 369–372, `source/spec/p337-384.md` L688–L740): "It remains to
treat `τ = ∞`. […] If `s_L ≤ −2` or `s_R ≤ −2`, the total angular clock is finite by Aux. lemma 102, and the band
comparison with bounded energy on the final infinite band transfers transience" — the same argument as in Aux. lemma
106 (p. 354), which is landed for one mark on each side (`Sec7.Band.ae_tendsto_of_eventualBand`, PROVE-SEC7-C5). In
Wang–Wu's proof of Theorem 7.7 (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, text dump L2945–L2965) these
configurations are retargeted; at `κ = 4` the remaining sector of Aux. lemma 113, both side totals `> κ/2 − 4 = −2`, is
exactly the configuration of Wang–Wu's Proposition 7.3.

This file proves, for every `κ > 0`, under the smaller-count hypothesis and Aux. lemma 102 with its band switches
(`Sec7.Aux102BandStatement`, a named input of Theorem 1.3):

* `isCompleteForceWord_of_lowSide_sep`: an ordered word with marks on both sides, fewer than `N` on each side, strictly
  separated from the seed, with a side total `≤ −2`, is complete: finite-time continuity is Aux. lemma 103
  (`Sec7.ae_isGeneratingTrace_lifetime`, = Wang–Wu Lemma 7.1), transience on infinite lifetime is the final infinite
  band (`Sec7.Band.ae_tendsto_of_eventualBand` with Aux. lemma 102). No distinctness of the positions is needed.
* **`isCompleteForceWord_of_lowSide`**: the same from any start, under the two-seed premise: Aux. lemma 103 with the
  seed entrance (`Sec7.Positive.seedEntranceStatement`) up to time `1`, then the restart at time `1`
  (`Sec7.isCompleteForceWord_of_hasCompletePrefix`), where the realized word is strictly separated (the cross-gap is
  positive at positive times) with the same weights.
* `LPAux113HighTransienceStatement κ`: the named remainder, Aux. lemma 113's transience in its third sector (both
  totals `> κ/2 − 4`); **`lpAux113TransienceStatement_of_high`**: `Sec7.LPAux113TransienceStatement κ` (Theorem 1.3's
  input #14 at `κ > 4`, and its κ = 4 instance) from Aux. lemma 102 and this remainder.

These are conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu.LowSide

open Sec7

/-- **A separated two-sided word with a side total `≤ −2` is complete** (every `κ > 0`), under the smaller-count
hypothesis for each side and Aux. lemma 102 with its band switches. -/
theorem isCompleteForceWord_of_lowSide_sep {κ : ℝ} (hκ : 0 < κ) (h102 : Aux102BandStatement.{u}) {N : ℕ}
    (hD : LP.DistinctCompleteBelow.{u} κ N) {nL nR : ℕ} {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (hF : IsOrderedForceWord xL xR) (hsep : ∀ i j, xL i < xR j)
    (hnL : nL + 1 < N) (hnR : nR + 1 < N) (hlow : (∑ i, ρL i) ≤ -2 ∨ (∑ j, ρR j) ≤ -2) :
    LP.IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hex : ExistsEvolutionStatement := Theorem13.existsEvolutionStatement
  have htrace := ae_isGeneratingTrace_lifetime hκ hex hD hE hF hnL hnR (Or.inl hsep)
  have hband := h102 κ hκ xL xR ρL ρR hF hsep hlow P 𝓕 W VL VR B ζ hE
  have htr := Band.ae_tendsto_of_eventualBand (i₀ := 0) (j₀ := 0) hκ hE hsep
    (ae_mem_lawSetS_zero_right hκ hex hD ρL hnL) (ae_mem_lawSetS_zero_left hκ hex hD ρR hnR)
    (fun i => Fin.zero_le i) (fun j => Fin.zero_le j) htrace hband
  filter_upwards [htrace, htr] with ω ⟨η, hη⟩ ht
  refine ⟨η, hη, fun htop => ?_⟩
  rw [htop] at hη
  exact ht htop η hη

/-- **A two-sided word with a side total `≤ −2` is complete, from any start** (every `κ > 0`), under the
smaller-count hypothesis for each side, the two-seed premise (for the seed entrance) and Aux. lemma 102. -/
theorem isCompleteForceWord_of_lowSide {κ : ℝ} (hκ : 0 < κ) (h102 : Aux102BandStatement.{u}) {N : ℕ}
    (hD : LP.DistinctCompleteBelow.{u} κ N) (h2 : LP.TwoSeedComplete.{u} κ) {nL nR : ℕ}
    {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    (hF : IsOrderedForceWord xL xR) (hnL : nL + 1 < N) (hnR : nR + 1 < N)
    (hlow : (∑ i, ρL i) ≤ -2 ∨ (∑ j, ρR j) ≤ -2) : LP.IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  refine isCompleteForceWord_of_hasCompletePrefix hκ ?_
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hex : ExistsEvolutionStatement := Theorem13.existsEvolutionStatement
  have hstart : (∀ i j, xL i < xR j) ∨ ∀ᵐ ω ∂P, ζ ω = 0 ∨
      ∃ ε : ℝ≥0, 0 < ε ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ε η := by
    by_cases hsep : ∀ i j, xL i < xR j
    · exact Or.inl hsep
    · exact Or.inr (Positive.seedEntranceStatement hκ h2 xL xR ρL ρR hF hsep P 𝓕 W VL VR B ζ hE)
  have htrace := ae_isGeneratingTrace_lifetime hκ hex hD hE hF hnL hnR hstart
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hζ𝓖 : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (ζ ω : WithTop ℝ≥0) :=
    Ito.isStoppingTime_lifetime hE𝓖.2.1
  refine ⟨fun ω => min ((1 : ℝ≥0) : ℝ≥0∞) (ζ ω), (isStoppingTime_const _ (1 : ℝ≥0)).min hζ𝓖, ?_⟩
  filter_upwards [htrace, hE.2.2.2.2] with ω ⟨η, hη⟩ hp
  have hτζ : min ((1 : ℝ≥0) : ℝ≥0∞) (ζ ω) ≤ ζ ω := min_le_right _ _
  refine ⟨hτζ, fun hlt => ?_, η, hη.mono_horizon hτζ, fun htop => ?_, fun hlt => ?_⟩
  · -- the realized word at time `1` is separated, with the same weights
    have h1 : ((1 : ℝ≥0) : ℝ≥0∞) < ζ ω := by
      by_contra hle
      rw [min_eq_right (not_lt.1 hle)] at hlt
      exact lt_irrefl _ hlt
    rw [min_eq_left h1.le, ENNReal.toNNReal_coe]
    have hsep1 : ∀ i j, VL i 1 ω - W 1 ω < VR j 1 ω - W 1 ω := fun i j => by
      have := hp.vL_lt_vR_of_pos hF one_pos h1 i j
      linarith
    intro Ω' mΩ'
    exact isCompleteForceWord_of_lowSide_sep hκ h102 hD (isOrderedForceWord_at hp h1) hsep1 hnL hnR hlow
  · exact absurd htop (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))
  · have hfin : min ((1 : ℝ≥0) : ℝ≥0∞) (ζ ω) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
    have hσ : (((min ((1 : ℝ≥0) : ℝ≥0∞) (ζ ω)).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω := by
      rw [ENNReal.coe_toNNReal hfin]
      exact hlt
    exact IsGeneratingTrace.isGeneratingTraceIcc hη hp.isForcePath.continuousOn_w hp.1 hσ

/-! ### Aux. lemma 113's transience from its third sector -/

/-- **Named statement: transience in Aux. lemma 113's third sector** (both side totals `> κ/2 − 4`; Specification
pp. 370–372, the moving-midpoint trials with the local GFF comparison of Aux. lemmas 108–111; at `κ = 4` the
configuration of Wang–Wu's Proposition 7.3, both side totals `> −2`, whose proof is the escape estimate of §6 and the
repeated trials). `Sec7.LPAux113TransienceStatement κ` restricted to that sector. -/
def LPAux113HighTransienceStatement (κ : ℝ) : Prop :=
  ∀ N : ℕ, 3 ≤ N → LP.DistinctCompleteBelow.{u} κ N → LP.TwoSeedComplete.{u} κ →
    ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      LP.IsDistinctForceWord xL xR → nL + nR = N → 0 < nL → 0 < nR →
      (κ / 2 - 4 < ∑ i, ρL i ∧ κ / 2 - 4 < ∑ i, ρR i) →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
      ∀ᵐ ω ∂P, ζ ω = ⊤ → (∀ t, ¬ SameSideMeet (fun i t => VL i t ω) (fun j t => VR j t ω) t) →
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → Tendsto (fun t => ‖η t‖) atTop atTop

/-- The restriction of `Sec7.LPAux113TransienceStatement κ` to its third sector. -/
theorem lpAux113HighTransienceStatement_of_transience {κ : ℝ} (h : LPAux113TransienceStatement.{u} κ) :
    LPAux113HighTransienceStatement.{u} κ := fun N hN hD h2 _ _ xL xR ρL ρR hd hc hL hR hs =>
  h N hN hD h2 xL xR ρL ρR hd hc hL hR (Or.inr (Or.inr hs))

/-- **`Sec7.LPAux113TransienceStatement κ` from Aux. lemma 102 and the third sector** (every `κ > 0`). A side total
`≤ −2`: the word is complete (`isCompleteForceWord_of_lowSide`), and every generating trace on `[0, ∞)` is its
transient trace (uniqueness of the generating trace). -/
theorem lpAux113TransienceStatement_of_high {κ : ℝ} (hκ : 0 < κ) (h102 : Aux102BandStatement.{u})
    (hhigh : LPAux113HighTransienceStatement.{u} κ) : LPAux113TransienceStatement.{u} κ := by
  intro N hN hD h2 nL nR xL xR ρL ρR hd hc hL hR hs Ω mΩ P _ 𝓕 W VL VR B ζ hE
  rcases hs with hs | hs | hs
  rotate_right
  · exact hhigh N hN hD h2 xL xR ρL ρR hd hc hL hR hs P 𝓕 W VL VR B ζ hE
  all_goals
    obtain ⟨nL, rfl⟩ : ∃ m, nL = m + 1 := ⟨nL - 1, by omega⟩
    obtain ⟨nR, rfl⟩ : ∃ m, nR = m + 1 := ⟨nR - 1, by omega⟩
    have hc : LP.IsCompleteForceWord.{u} κ xL xR ρL ρR :=
      isCompleteForceWord_of_lowSide hκ h102 hD h2 hd.1 (by omega) (by omega) (by tauto)
    filter_upwards [hc P 𝓕 W VL VR B ζ hE, hE.2.2.2.2] with ω ⟨η₀, hη₀, htr₀⟩ hp hζ _ η hη
    rw [hζ] at hη₀ hp
    have hwc : ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < ⊤} := hp.2.2.2.1
    refine (htr₀ hζ).congr fun t => ?_
    rw [hη₀.eq_of_le hη hwc hp.1 le_top]

/-! ### The `κ < 4` form (Theorem 1.3's input #6) -/

/-- **Named statement: transience in Aux. lemma 113's third sector, the `κ < 4` form** (`Sec7.Aux113TransienceStatement`
restricted to words whose side totals both exceed `κ/2 − 4`). -/
def Aux113HighTransienceStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ N : ℕ, 3 ≤ N →
    (∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      LP.IsDistinctForceWord xL xR → nL + nR ≤ N - 1 → LP.IsCompleteForceWord.{u} κ xL xR ρL ρR) →
    ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      LP.IsDistinctForceWord xL xR → nL + nR = N → 1 ≤ nL → 1 ≤ nR →
      (κ / 2 - 4 < ∑ i, ρL i ∧ κ / 2 - 4 < ∑ i, ρR i) →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
      ∀ᵐ ω ∂P, ζ ω = ⊤ → (∀ t, ¬ SameSideMeet (fun i t => VL i t ω) (fun j t => VR j t ω) t) →
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → Tendsto (fun t => ‖η t‖) atTop atTop

/-- **`Sec7.Aux113TransienceStatement` (Theorem 1.3's input #6) from Proposition 7.3's named statement, Aux. lemma
102 and the third sector.** For `0 < κ < 4` every side total is `≤ −2` or `> −2 > κ/2 − 4`; a side total `≤ −2` is
`isCompleteForceWord_of_lowSide` (the two-seed premise from Proposition 7.3, `Sec7.twoSeedComplete_of_prop73`). -/
theorem aux113TransienceStatement_of_high (h73 : Prop73TraceStatement.{u}) (h102 : Aux102BandStatement.{u})
    (hhigh : Aux113HighTransienceStatement.{u}) : Aux113TransienceStatement.{u} := by
  intro κ hκ hκ4 N hN hbelow nL nR xL xR ρL ρR hd hc hL hR Ω mΩ P _ 𝓕 W VL VR B ζ hE
  by_cases hlow : (∑ i, ρL i) ≤ -2 ∨ (∑ j, ρR j) ≤ -2
  · have hD : LP.DistinctCompleteBelow.{u} κ N := distinctCompleteBelow_of_le (by omega) hbelow
    obtain ⟨nL, rfl⟩ : ∃ m, nL = m + 1 := ⟨nL - 1, by omega⟩
    obtain ⟨nR, rfl⟩ : ∃ m, nR = m + 1 := ⟨nR - 1, by omega⟩
    have hcw : LP.IsCompleteForceWord.{u} κ xL xR ρL ρR :=
      isCompleteForceWord_of_lowSide hκ h102 hD (twoSeedComplete_of_prop73 h73 hκ hκ4) hd.1 (by omega)
        (by omega) hlow
    filter_upwards [hcw P 𝓕 W VL VR B ζ hE, hE.2.2.2.2] with ω ⟨η₀, hη₀, htr₀⟩ hp hζ _ η hη
    rw [hζ] at hη₀ hp
    have hwc : ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < ⊤} := hp.2.2.2.1
    refine (htr₀ hζ).congr fun t => ?_
    rw [hη₀.eq_of_le hη hwc hp.1 le_top]
  · rw [not_or, not_le, not_le] at hlow
    exact hhigh κ hκ hκ4 N hN hbelow xL xR ρL ρR hd hc hL hR
      ⟨by linarith [hlow.1], by linarith [hlow.2]⟩ P 𝓕 W VL VR B ζ hE

end InteractingSLE.WangWu.LowSide
