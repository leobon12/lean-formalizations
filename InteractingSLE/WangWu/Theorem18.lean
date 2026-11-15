/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Continuity2OneForce
import InteractingSLE.WangWu.Continuity2Band
import InteractingSLE.Spec.Sec7.ContinuityProb6Inputs
import InteractingSLE.Spec.Sec7.ContinuityProb3Steps
import InteractingSLE.Spec.Supplement.LP6Retarget
import InteractingSLE.Spec.Supplement.LPAmalgamate
import InteractingSLE.Spec.Theorem13Inputs
import InteractingSLE.Spec.Zhan.TwoForceSeed
import InteractingSLE.Spec.ZhanGT4.Prefix

/-!
# Wang–Wu Theorem 1.8 at `κ = 4`: the finite-force induction with its seeds

Packet PROVE-WW-C2. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), Theorem 1.8
(= [WW17] Theorem 1.1.3, p. 3) and its proof, Theorem 7.7 (text dump L2900–L2980): "Induct on `N`. The cases `N ≤ 2`
are the seed propositions of Section 5. Assume the theorem for fewer than `N` marks. […] One-sided configurations with
`N` marks. […] retarget at `q = x_j` […] Arbitrary two-sided configurations. If both side totals exceed `−2`, use
Proposition 7.3. Otherwise choose a side with total at most `−2` […] Retarget at `q`. […] Every global nonterminal
splice thus strictly decreases `N`, so there are only finitely many."

This file proves the κ = 4 input of the frozen Theorem 1.3 (`LP.WWTheorem18DistinctStatement`, Theorem 1.3's
assembly `Spec/Theorem13.lean`) from named statements that are the κ = 4 instances of the statement families the
assembly already uses at the other parameters, by the landed finite-force induction (`LP.isCompleteForceWord_of_
reductions_noLP6`, PROVE-R17; its statements are parameter-free). At `κ = 4` the induction is Wang–Wu's: the sector
condition (TI13.1) of Aux. lemma 113 always holds (`κ/2 − 4 = −2`), so every two-sided configuration is Aux. lemma
113's (Wang–Wu: Proposition 7.3 when both side totals exceed `−2`, retargeting otherwise), Lemma LP8 is a case of it
(`lp8Statement_four`), and one-sided configurations are retargeted (Lemma LP9; Wang–Wu: "retarget at `q = x_j`").

* The seeds `N ≤ 2` (Wang–Wu §5): zero marks (ordinary SLE₄, `Theorem13.zeroForceStatement`); one mark (Lemma 5.1:
  `Lemma51.oneForceStatement_of_twoSeed`, from the two-seed premise and the case `ρ ≤ −2`); one mark on each side
  (Propositions 5.5–5.6: **`aux106Statement_of_oneForce`**, every `κ > 0`, from the one-force base and Aux. lemma 102
  with its band switches; finite-time continuity is Aux. lemma 103 = Wang–Wu Lemma 7.1, transience for weights `> −2`
  the ratio restart `Sec7.Positive.ae_tendsto_of_twoSeed`, and for a weight `≤ −2` the final infinite band); two marks
  on one side (Proposition 5.7, by retargeting: `LP.lp6Statement_of_lp9`).
* The induction step: Aux. lemma 113 from transience without merger (`Sec7.lpAux113PrefixStatement_of_transience`:
  Lemma 7.1 = Aux. lemma 103, the seed entrance, the restart at the merger time) and Lemma LP9 from its prefix part.

## Main results

* **`aux106Statement_of_oneForce`**: `LP.Aux106Statement κ` for every `κ > 0` from `LP.OneForceStatement κ` and
  `Sec7.Aux102BandStatement`.
* `isCompleteForceWord_twoSeed_of_admissible`, **`twoSeedComplete_of_hitting`**: for `0 < κ ≤ 4` the two-seed premise
  holds for weights `≥ κ/2 − 2` unconditionally (landed Zhan results), so only the boundary-hitting weights remain
  (`TwoSeedHittingStatement κ`; at `κ = 4` the weights in `(−2, 0)` of Wang–Wu Proposition 4.24).
* `lp8Statement_four`: `LP.LP8Statement 4` from `LP.Aux113Statement 4`.
* **`wwTheorem18DistinctStatement_of_inputs`**: `LP.WWTheorem18DistinctStatement` from the two-seed premise at `κ = 4`
  (Wang–Wu Proposition 4.24), the case `ρ ≤ −2` of Lemma 5.1, Aux. lemma 102 with its band switches, transience in
  Aux. lemma 113 at `κ = 4`, and the prefix part of Lemma LP9 at `κ = 4`;
  `wwTheorem18DistinctStatement_of_stopped`: the same with the stopped Aux. lemma 99 at `κ = 4` in place of the case
  `ρ ≤ −2`; `wwTheorem18Statement_of_inputs`: the ordered-word form (amalgamation).
* **`wwTheorem18DistinctStatement_of_high`**: the same with Aux. lemma 113's transience needed only in its third sector
  (`LowSide.LPAux113HighTransienceStatement 4`: both side totals `> −2`, the configuration of Wang–Wu's Proposition
  7.3); a side total `≤ −2` is handled by Aux. lemma 102 (`LowSide.lpAux113TransienceStatement_of_high`).
* **`wwTheorem18DistinctStatement_of_open`**, `wwTheorem18Statement_of_open`: the final form, with the two-seed premise
  needed only for the boundary-hitting weights.

These are conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu.Theorem18

open Sec7

/-! ### Propositions 5.5–5.6: one mark on each side, every `κ > 0` -/

/-- **Aux. lemma 106 in LP10's form, for every `κ > 0`, from the one-force base and Aux. lemma 102** (Wang–Wu
Propositions 5.5–5.6: two opposite forces, arbitrary weights). Under the two-seed premise, a word with one mark on each
side is complete. Both marks at the seed: the premise, or lifetime `0` for an inadmissible weight. A positive
cross-gap: continuity through a finite threshold by Aux. lemma 103 with `N = 2` (Wang–Wu Lemma 7.1, deleting the
separated opposite mark and using the one-force base); transience on infinite lifetime by the ratio restart of the
two-seed law (weights `> −2`, `Sec7.Positive.ae_tendsto_of_twoSeed`) or by the final infinite band with whole-tail
Girsanov (a weight `≤ −2`, `Sec7.Band.ae_tendsto_of_eventualBand` with Aux. lemma 102). -/
theorem aux106Statement_of_oneForce {κ : ℝ} (hκ : 0 < κ) (h1 : LP.OneForceStatement.{u} κ)
    (h102 : Sec7.Aux102BandStatement.{u}) : LP.Aux106Statement.{u} κ := by
  intro h2 xL xR ρL ρR hF
  have hL : ρL = fun _ => ρL 0 := funext fun i => by rw [Fin.fin_one_eq_zero i]
  have hR : ρR = fun _ => ρR 0 := funext fun i => by rw [Fin.fin_one_eq_zero i]
  intro Ω mΩ
  by_cases hsep : ∀ i j, xL i < xR j
  · -- a positive cross-gap
    intro P _ 𝓕 W VL VR B ζ hE
    have hex : ExistsEvolutionStatement := Theorem13.existsEvolutionStatement
    have hD : LP.DistinctCompleteBelow.{u} κ 2 :=
      LP.distinctCompleteBelow_two (Theorem13.zeroForceStatement hκ) h1
    have htrace := ae_isGeneratingTrace_lifetime hκ hex hD hE hF (by norm_num) (by norm_num) (Or.inl hsep)
    have htr : ∀ᵐ ω ∂P, ζ ω = ⊤ → ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
        Tendsto (fun t => ‖η t‖) atTop atTop := by
      by_cases hneg : ρL 0 ≤ -2 ∨ ρR 0 ≤ -2
      · have hsum : (∑ i, ρL i) ≤ -2 ∨ (∑ j, ρR j) ≤ -2 := by
          simpa only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] using hneg
        have hband := h102 κ hκ (nL := 0) (nR := 0) xL xR ρL ρR hF hsep hsum P 𝓕 W VL VR B ζ hE
        exact Band.ae_tendsto_of_eventualBand (i₀ := 0) (j₀ := 0) hκ hE hsep
          (ae_mem_lawSetS_zero_right hκ hex hD ρL (by norm_num))
          (ae_mem_lawSetS_zero_left hκ hex hD ρR (by norm_num)) (fun i => Fin.zero_le i)
          (fun j => Fin.zero_le j) htrace hband
      · rw [not_or, not_le, not_le] at hneg
        have h2' : LP.IsCompleteForceWord.{u} κ (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) ρL ρR := by
          rw [hL, hR]
          exact h2 (ρL 0) (ρR 0) hneg.1 hneg.2
        exact Positive.ae_tendsto_of_twoSeed hκ hneg.1 hneg.2 h2' hE
    filter_upwards [htrace, htr] with ω ⟨η, hη⟩ ht
    refine ⟨η, hη, fun htop => ?_⟩
    rw [htop] at hη
    exact ht htop η hη
  · -- both marks at the seed
    have hx : xL 0 = 0 ∧ xR 0 = 0 := by
      have h1' := hF.2.1 0
      have h2' := hF.2.2.2 0
      have h3 : ¬ xL 0 < xR 0 := fun h => hsep fun i j => by
        rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
        exact h
      constructor <;> linarith [not_lt.1 h3]
    have hxL : xL = LP.twoSeedXL := funext fun i => by
      rw [Fin.fin_one_eq_zero i]
      exact hx.1
    have hxR : xR = LP.twoSeedXR := funext fun i => by
      rw [Fin.fin_one_eq_zero i]
      exact hx.2
    by_cases hadm : -2 < ρL 0 ∧ -2 < ρR 0
    · rw [hxL, hxR, hL, hR]
      exact h2 (ρL 0) (ρR 0) hadm.1 hadm.2
    · refine isCompleteForceWord_of_thresholdCondition ?_
      have hfL : Finset.univ.filter (fun i : Fin 1 => xL i = 0) = Finset.univ :=
        Finset.filter_true_of_mem fun i _ => by rw [Fin.fin_one_eq_zero i]; exact hx.1
      have hfR : Finset.univ.filter (fun i : Fin 1 => xR i = 0) = Finset.univ :=
        Finset.filter_true_of_mem fun i _ => by rw [Fin.fin_one_eq_zero i]; exact hx.2
      unfold ForceWord.ThresholdCondition
      rw [hfL, hfR, Fin.sum_univ_one, Fin.sum_univ_one]
      rw [not_and_or, not_lt, not_lt] at hadm
      exact hadm

/-! ### The two-seed premise for `κ ≤ 4`: only the boundary-hitting weights remain -/

/-- The two-seed word with weights `≥ k/2 − 2` has admissible partial sums. -/
theorem hasAdmissiblePartialSums_twoSeed {k rL rR : ℝ} (hL : k / 2 - 2 ≤ rL) (hR : k / 2 - 2 ≤ rR) :
    Sec4.HasAdmissiblePartialSums k (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => (0 : ℝ))
      (fun _ : Fin 1 => (0 : ℝ)) := by
  refine ⟨fun x hx _ => ?_, fun x hx _ => ?_⟩
  · rw [Finset.filter_true_of_mem fun (i : Fin 1) _ => (show x < 0 from hx), Fin.sum_univ_one]
    exact hL
  · rw [Finset.filter_true_of_mem fun (i : Fin 1) _ => (show (0 : ℝ) ≤ x from hx), Fin.sum_univ_one]
    exact hR

/-- **The non-boundary-intersecting two-seed words are complete for `0 < κ ≤ 4`** (weights `≥ κ/2 − 2`; at `κ = 4`
Wang–Wu's non-boundary-intersecting seed, Lemma 4.12 and Corollary 4.13): the trace with infinite lifetime
(`ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible`) and the seed transience
(`Zhan.IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoSeed`), both unconditional. -/
theorem isCompleteForceWord_twoSeed_of_admissible {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {rL rR : ℝ}
    (hL : κ / 2 - 2 ≤ rL) (hR : κ / 2 - 2 ≤ rR) :
    LP.IsCompleteForceWord.{u} κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hE' : IsIntegratedSLEEvolution κ (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) (fun _ => rL)
      (fun _ => rR) P 𝓕 W VL VR B ζ := hE
  have hadm := hasAdmissiblePartialSums_twoSeed hL hR
  filter_upwards [ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hκ
      Zhan.isOrderedForceWord_zero hadm hE',
      Zhan.IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoSeed hκ hκ4 hadm hE']
    with ω ⟨hζ, _, η, hη⟩ htr
  exact ⟨η, hζ ▸ hη, fun _ => htr η hη⟩

/-- **Named statement: the boundary-hitting two-seed words** (both weights `> −2`, at least one `< κ/2 − 2`; at `κ = 4`
the weights in `(−2, 0)` of Wang–Wu's Proposition 4.24, whose proof realizes the chain as the middle seed line in a
chamber between two non-boundary-intersecting seed lines). The two-seed word is complete. -/
def TwoSeedHittingStatement (κ : ℝ) : Prop :=
  ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < κ / 2 - 2 ∨ rR < κ / 2 - 2) →
    LP.IsCompleteForceWord.{u} κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR)

/-- **The two-seed premise for `0 < κ ≤ 4` from its boundary-hitting weights.** -/
theorem twoSeedComplete_of_hitting {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (h : TwoSeedHittingStatement.{u} κ) :
    LP.TwoSeedComplete.{u} κ := by
  intro rL rR hL hR
  by_cases hadm : κ / 2 - 2 ≤ rL ∧ κ / 2 - 2 ≤ rR
  · exact isCompleteForceWord_twoSeed_of_admissible hκ hκ4 hadm.1 hadm.2
  · rw [not_and_or, not_le, not_le] at hadm
    exact h rL rR hL hR hadm

/-- The restriction of the two-seed premise to its boundary-hitting weights. -/
theorem twoSeedHittingStatement_of_twoSeedComplete {κ : ℝ} (h : LP.TwoSeedComplete.{u} κ) :
    TwoSeedHittingStatement.{u} κ := fun rL rR hL hR _ => h rL rR hL hR

/-! ### Lemma LP8 at `κ = 4` -/

/-- **Lemma LP8 at `κ = 4` is a case of Aux. lemma 113**: a singleton side of weight `> −2` and an opposite total
`> κ/2 − 4 = −2` satisfy the third alternative of (TI13.1). -/
theorem lp8Statement_four (h113 : LP.Aux113Statement.{u} 4) : LP.LP8Statement.{u} 4 := by
  intro N hN IH h2 nL xL xR ρL ρR hD hc hr hl
  have hnL : 0 < nL := by omega
  intro Ω mΩ
  refine h113 N hN IH h2 xL xR ρL ρR hD hc hnL one_pos (Or.inr (Or.inr ⟨hl, ?_⟩))
  rw [Fin.sum_univ_one]
  norm_num
  linarith

/-! ### The induction at `κ = 4` -/

/-- **Wang–Wu Theorem 1.8 for distinct positions** (`LP.WWTheorem18DistinctStatement`, the κ = 4 input of the
frozen Theorem 1.3) from: the two-seed premise at `κ = 4` (Wang–Wu Proposition 4.24), the case `ρ ≤ −2` of Lemma 5.1,
Aux. lemma 102 with its band switches (every `κ`), transience without merger in Aux. lemma 113 at `κ = 4`, and the
prefix part of Lemma LP9 at `κ = 4`. Conditional helper; it replaces no source theorem. -/
theorem wwTheorem18DistinctStatement_of_inputs (h2 : LP.TwoSeedComplete.{u} 4)
    (hna : Lemma51.OneRightNonAdmissibleStatement.{u} 4) (h102 : Sec7.Aux102BandStatement.{u})
    (htr : Sec7.LPAux113TransienceStatement.{u} 4) (h9 : Sec7.LP9PrefixStatement.{u} 4) :
    LP.WWTheorem18DistinctStatement.{u} := by
  have h4 : (0 : ℝ) < 4 := by norm_num
  have h0 : LP.ZeroForceStatement.{u} 4 := Theorem13.zeroForceStatement h4
  have h1 : LP.OneForceStatement.{u} 4 := Lemma51.oneForceStatement_of_twoSeed h4 h2 hna
  have h106 : LP.Aux106Statement.{u} 4 := aux106Statement_of_oneForce h4 h1 h102
  have h113 : LP.Aux113Statement.{u} 4 :=
    lpAux113Statement_of_prefix h4 (lpAux113PrefixStatement_of_transience h4 htr)
  have h9' : LP.LP9Statement.{u} 4 := lp9Statement_of_prefix h4 h9
  intro nL nR xL xR ρL ρR hD
  exact LP.isCompleteForceWord_of_reductions_noLP6 h0 h1 h106 h113 (lp8Statement_four h113) h9' h2 xL xR ρL ρR
    hD.1

/-- **Wang–Wu Theorem 1.8 for distinct positions from the stopped Aux. lemma 99 at `κ = 4`** (the statement family
of Theorem 1.3's inputs #2 and #9) in place of the case `ρ ≤ −2` of Lemma 5.1. -/
theorem wwTheorem18DistinctStatement_of_stopped (h2 : LP.TwoSeedComplete.{u} 4)
    (h99 : Sec7.Aux99StoppedStatement.{u} 4) (h102 : Sec7.Aux102BandStatement.{u})
    (htr : Sec7.LPAux113TransienceStatement.{u} 4) (h9 : Sec7.LP9PrefixStatement.{u} 4) :
    LP.WWTheorem18DistinctStatement.{u} :=
  wwTheorem18DistinctStatement_of_inputs h2 (Lemma51.oneRightNonAdmissibleStatement_of_stopped h99) h102 htr h9

/-- **Wang–Wu Theorem 1.8 on the frozen ordered force word** (`LP.WWTheorem18Statement`) from the same inputs, by the
proved amalgamation of coincident marks. -/
theorem wwTheorem18Statement_of_inputs (h2 : LP.TwoSeedComplete.{u} 4)
    (hna : Lemma51.OneRightNonAdmissibleStatement.{u} 4) (h102 : Sec7.Aux102BandStatement.{u})
    (htr : Sec7.LPAux113TransienceStatement.{u} 4) (h9 : Sec7.LP9PrefixStatement.{u} 4) :
    LP.WWTheorem18Statement.{u} :=
  LP.wwTheorem18Statement_of_distinct (wwTheorem18DistinctStatement_of_inputs h2 hna h102 htr h9)

/-- **Wang–Wu Theorem 1.8 for distinct positions, with Aux. lemma 113's transience only in its third sector**: from
the two-seed premise at `κ = 4` (Wang–Wu Proposition 4.24), the case `ρ ≤ −2` of Lemma 5.1, Aux. lemma 102 with its
band switches, transience when both side totals exceed `−2` (Wang–Wu Proposition 7.3's configuration), and the prefix
part of Lemma LP9 at `κ = 4`. Conditional helper; it replaces no source theorem. -/
theorem wwTheorem18DistinctStatement_of_high (h2 : LP.TwoSeedComplete.{u} 4)
    (hna : Lemma51.OneRightNonAdmissibleStatement.{u} 4) (h102 : Sec7.Aux102BandStatement.{u})
    (hhigh : LowSide.LPAux113HighTransienceStatement.{u} 4) (h9 : Sec7.LP9PrefixStatement.{u} 4) :
    LP.WWTheorem18DistinctStatement.{u} :=
  wwTheorem18DistinctStatement_of_inputs h2 hna h102
    (LowSide.lpAux113TransienceStatement_of_high (by norm_num) h102 hhigh) h9

/-- **Wang–Wu Theorem 1.8 for distinct positions from its open inputs** (the κ = 4 input of Theorem 1.3, with every
landed reduction applied): the boundary-hitting two-seed words at `κ = 4` (weights in `(−2, 0)`, Wang–Wu Proposition
4.24), the case `ρ ≤ −2` of Lemma 5.1, Aux. lemma 102 with its band switches, transience when both side totals exceed
`−2` (Wang–Wu Proposition 7.3's configuration), and the prefix part of Lemma LP9 at `κ = 4`. Conditional helper; it
replaces no source theorem. -/
theorem wwTheorem18DistinctStatement_of_open (hseed : TwoSeedHittingStatement.{u} 4)
    (hna : Lemma51.OneRightNonAdmissibleStatement.{u} 4) (h102 : Sec7.Aux102BandStatement.{u})
    (hhigh : LowSide.LPAux113HighTransienceStatement.{u} 4) (h9 : Sec7.LP9PrefixStatement.{u} 4) :
    LP.WWTheorem18DistinctStatement.{u} :=
  wwTheorem18DistinctStatement_of_high (twoSeedComplete_of_hitting (by norm_num) le_rfl hseed) hna h102 hhigh h9

/-- **Wang–Wu Theorem 1.8 on the frozen ordered force word** from the open inputs of
`wwTheorem18DistinctStatement_of_open` (amalgamation). -/
theorem wwTheorem18Statement_of_open (hseed : TwoSeedHittingStatement.{u} 4)
    (hna : Lemma51.OneRightNonAdmissibleStatement.{u} 4) (h102 : Sec7.Aux102BandStatement.{u})
    (hhigh : LowSide.LPAux113HighTransienceStatement.{u} 4) (h9 : Sec7.LP9PrefixStatement.{u} 4) :
    LP.WWTheorem18Statement.{u} :=
  LP.wwTheorem18Statement_of_distinct (wwTheorem18DistinctStatement_of_open hseed hna h102 hhigh h9)

end InteractingSLE.WangWu.Theorem18
