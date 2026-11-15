/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.OneForceTrans
import InteractingSLE.Spec.Zhan.Words

/-!
# The reference word of the whole-tail comparison for `κ > 4` (Part B.5)

Packet PROVE-ZHAN-GT4-B3. Source: Astra, *Follow-up proofs*, §B.5 L1322–L1338 (ruling R38): "For a chordal word, map the
outermost mark on a side to a strip end, collapse the exponentially decaying errors from that side into its total
weight,
and repeat on the other side. This reduces to the one-force or two-force bases above. Each collapsed total is at least
`c_κ`. Empty sides are handled by the genuine one-force theorem; inserting a zero-weight mark would be invalid when
`κ > 4`." (Additional note, Proposition 1.12, L585–L612, ruling R39.)

PROVE-ZHAN-B4's reference word (`Zhan.outerW`: every weight of a side moved onto its outermost mark, positions kept) is
not admissible for `κ > 4` (its inner marks have weight `0 < κ/2 − 2`), so B4's κ ≤ 4 inputs do not apply. Its
evolutions still have infinite lifetime: every colliding group is an initial segment of a side, of weight `0` or the
whole side total `≥ κ/2 − 2`, both `> −2` (`ae_lifetime_eq_top_of_groupEndSums`, Aux. lemma 3). After relabelling every
mark of a side as its outermost mark (`Zhan.IsIntegratedSLEEvolution.relabelOuter`) the processes are an evolution of
the word whose marks of a side all sit at its outermost position, which *is* admissible; merging the groups gives the
one-force (`OneForceTrans.lean`) or two-force (GT4-B2) bases, or the empty word. Hence the reference word is transient,
and the canonical-law inputs of B4's whole-tail comparison hold for `κ > 4`.

## Main results

* `IsIntegratedSLEEvolution.ae_lifetime_eq_top_of_groupEndSums`: Aux. 6's lifetime argument with any level `c > −2`.
* `IsIntegratedSLEEvolution.ae_tendsto_norm_trace_groups_gt_four`: transience of two-group words, `κ > 4`.
* `IsIntegratedSLEEvolution.ae_traceEvent_outerW_gt_four`, `codeLaw_outerW_lifetime_gt_four`,
  `codeLaw_outerW_lateSet_tendsto_zero_gt_four`: the reference word, `κ > 4`.

All transience results take Part A's two geometric outputs as named inputs: (G5) `StoppingInverseBoundaryStatement κ`
and (G2) `SeparatedTwoForceStatement κ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4

open Zhan Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart

/-! ### Infinite lifetime from group-end sums above `−2` -/

section Lifetime

variable {k : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The continuation threshold is infinite** (Aux. lemma 6's lifetime argument, with any level): if both sides have
group-end sums at least some `c > −2`, then almost surely `ζ = ∞`. -/
theorem IsIntegratedSLEEvolution.ae_lifetime_eq_top_of_groupEndSums {c : ℝ} (hc : -2 < c)
    (hword : IsOrderedForceWord xL xR) (hL : Sec4.HasGroupEndSums c ρL (-xL)) (hR : Sec4.HasGroupEndSums c ρR xR)
    (h : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) : ∀ᵐ ω ∂P, ζ ω = ⊤ := by
  obtain ⟨hxL, hxL0, hxR, hxR0⟩ := hword
  have hsL := (Sec4.neg_two_lt_sum_of_hasGroupEndSums hc hL).ne'
  have hsR := (Sec4.neg_two_lt_sum_of_hasGroupEndSums hc hR).ne'
  filter_upwards [h.ae_tendsto_threshold_of_ne hsL hsR, h.ae_isIntegratedSLEPath] with ω hlim hp
  by_contra hne
  obtain ⟨T, hT⟩ : ∃ T : ℝ≥0, (T : ℝ≥0∞) = ζ ω := ⟨(ζ ω).toNNReal, ENNReal.coe_toNNReal hne⟩
  have hfp := hp.isForcePath
  rcases eq_zero_or_pos T with hT0 | hT0
  · have h0 : ζ ω = 0 := by rw [← hT, hT0, ENNReal.coe_zero]
    exact Sec4.not_thresholdCondition_of_hasGroupEndSums hc hxL hxR hL hR hxL hxR hxL0 hxR0
      (fun _ _ h => h) (fun _ _ h => h) (hfp.threshold_of_eq_zero h0)
  · obtain ⟨w₀, vL₀, vR₀, hlim', hth⟩ := hlim T hT0 hT
    have : NeBot (𝓝[<] T) := nhdsLT_neBot_of_exists_lt ⟨0, hT0⟩
    have hev : ∀ᶠ t : ℝ≥0 in 𝓝[<] T, (t : ℝ≥0∞) < ζ ω := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [← hT]; exact_mod_cast ht
    have hw : Tendsto (fun t => W t ω) (𝓝[<] T) (𝓝 w₀) := hlim'.fst_nhds
    have hvL : ∀ i, Tendsto (fun t => VL i t ω) (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
      tendsto_pi_nhds.1 hlim'.snd_nhds.fst_nhds i
    have hvR : ∀ i, Tendsto (fun t => VR i t ω) (𝓝[<] T) (𝓝 (vR₀ i)) := fun i =>
      tendsto_pi_nhds.1 hlim'.snd_nhds.snd_nhds i
    refine Sec4.not_thresholdCondition_of_hasGroupEndSums hc hxL hxR hL hR ?_ ?_ ?_ ?_ ?_ ?_ hth
    · intro i j hij
      exact le_of_tendsto_of_tendsto (hvL j) (hvL i) (hev.mono fun t ht => hfp.antitone_vL ht hij)
    · intro i j hij
      exact le_of_tendsto_of_tendsto (hvR i) (hvR j) (hev.mono fun t ht => hfp.monotone_vR ht hij)
    · intro i
      exact le_of_tendsto_of_tendsto (hvL i) hw (hev.mono fun t ht => hfp.vL_le_w ht i)
    · intro i
      exact le_of_tendsto_of_tendsto hw (hvR i) (hev.mono fun t ht => hfp.w_le_vR ht i)
    · intro i j hij
      exact tendsto_nhds_unique (hvL i)
        ((hvL j).congr' (hev.mono fun t ht => (hp.vL_eq_of_xL_eq ht hij).symm))
    · intro i j hij
      exact tendsto_nhds_unique (hvR i)
        ((hvR j).congr' (hev.mono fun t ht => (hp.vR_eq_of_xR_eq ht hij).symm))

end Lifetime

/-! ### The reference word: lifetime -/

section Reference

variable {n nL nR : ℕ}

/-- The weights moved onto the outermost mark have group-end sums `0` (inner group ends) and the total (the last
mark). -/
theorem hasGroupEndSums_outerW {c : ℝ} (ρ x : Fin n → ℝ) (hc0 : c ≤ 0) (hcS : c ≤ ∑ i, ρ i) :
    Sec4.HasGroupEndSums c (outerW ρ) x := by
  intro j _
  by_cases hj : (j : ℕ) + 1 = n
  · have e : (Finset.univ.filter fun i => i ≤ j) = Finset.univ := by
      refine Finset.filter_true_of_mem fun i _ => Fin.le_def.2 ?_
      have := i.2; omega
    rw [e, sum_outerW]
    exact hcS
  · rw [Finset.sum_eq_zero fun i hi => outerW_of_ne fun hie => ?_]
    · exact hc0
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have h1 := eq_lastOf_iff.1 hie
      have h2 := Fin.le_def.1 hi
      have h3 := j.2
      omega

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **The reference word has infinite lifetime**, every `κ > 0`: its colliding groups weigh `0` or a whole side total
`≥ κ/2 − 2 > −2`. -/
theorem IsIntegratedSLEEvolution.ae_lifetime_eq_top_outerW (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR) (hxL : ∀ i, xL i < 0) (hxR : ∀ j, 0 < xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR (outerW ρL) (outerW ρR) P 𝓕 W VL VR B ζ) : ∀ᵐ ω ∂P, ζ ω = ⊤ := by
  have hSL := neg_two_lt_sum_left hκ hF hadm hxL
  have hSR := neg_two_lt_sum_right hκ hF hadm hxR
  set c : ℝ := min 0 (min (∑ i, ρL i) (∑ j, ρR j)) with hc
  have hc2 : -2 < c := lt_min (by norm_num) (lt_min hSL hSR)
  exact IsIntegratedSLEEvolution.ae_lifetime_eq_top_of_groupEndSums hc2 hF
    (hasGroupEndSums_outerW ρL (-xL) (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _)))
    (hasGroupEndSums_outerW ρR xR (min_le_left _ _) ((min_le_right _ _).trans (min_le_right _ _))) hE

/-- The word with all marks of a side at its outermost position and the side weights on the outermost mark is
admissible, every `κ` (every side prefix is empty or the whole side). -/
theorem hasAdmissiblePartialSums_outerPos (hF : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR) (hxL : ∀ i, xL i < 0) (hxR : ∀ j, 0 < xR j) :
    Sec4.HasAdmissiblePartialSums κ (outerW ρL) (outerW ρR) (outerPos xL) (outerPos xR) := by
  refine ⟨fun x _ ⟨i, hi⟩ => ?_, fun x _ ⟨j, hj⟩ => ?_⟩
  · have e : (Finset.univ.filter fun k => x < outerPos xL k) = Finset.univ :=
      Finset.filter_true_of_mem fun k _ => by
        show x < xL (lastOf k)
        rw [lastOf_eq k i]; exact hi
    rw [e, sum_outerW]
    exact le_sum_left hF hadm hxL i
  · have e : (Finset.univ.filter fun k => outerPos xR k ≤ x) = Finset.univ :=
      Finset.filter_true_of_mem fun k _ => by
        show xR (lastOf k) ≤ x
        rw [lastOf_eq k j]; exact hj
    rw [e, sum_outerW]
    exact le_sum_right hF hadm hxR j

end Reference

/-! ### Two-group words for `κ > 4` -/

section Groups

variable {κ : ℝ} {nL nR : ℕ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Transience for two-group words, `κ > 4`** (B.5): an ordered word with admissible side partial sums, at least one
mark, whose left marks all sit at one point `< 0` and whose right marks all sit at one point `> 0`; given (G5) and (G2),
almost surely every continuous generating trace on `[0, ∞)` tends to `∞`. -/
theorem IsIntegratedSLEEvolution.ae_tendsto_norm_trace_groups_gt_four (hκ4 : 4 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{0} κ) (hG2 : SeparatedTwoForceStatement.{0} κ)
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hF : IsOrderedForceWord xL xR) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hxL : ∀ i, xL i < 0) (hxR : ∀ j, 0 < xR j) (hgL : ∀ i j, xL i = xL j) (hgR : ∀ i j, xR i = xR j)
    (hn : 0 < nL + nR) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop := by
  have hκ : 0 < κ := by linarith
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ :=
    (Sec4.aux6Statement hκ xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hE).mono fun ω h => h.1
  cases nL with
  | zero =>
    cases nR with
    | zero => exact absurd hn (lt_irrefl 0)
    | succ n =>
      have hE' := Zhan.IsIntegratedSLEEvolution.mergeRight (fun i => hgR i 0) hE hζ
      exact IsIntegratedSLEEvolution.ae_tendsto_norm_trace_oneForce_right hκ4 hG5 (hxR 0)
        (le_sum_right_of_group hadm (hxR 0) fun i => hgR i 0) hE'
  | succ m =>
    have hE₁ := Zhan.IsIntegratedSLEEvolution.mergeLeft (fun i => hgL i 0) hE hζ
    have hρL := le_sum_left_of_group hadm (hxL 0) fun i => hgL i 0
    cases nR with
    | zero => exact IsIntegratedSLEEvolution.ae_tendsto_norm_trace_oneForce hκ4 hG5 (hxL 0) hρL hE₁
    | succ n =>
      have hE₂ := Zhan.IsIntegratedSLEEvolution.mergeRight (fun i => hgR i 0) hE₁ hζ
      exact IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoForce_gt_four hκ4 hG5 hG2 (hxL 0) (hxR 0)
        (hasAdmissiblePartialSums_one hρL (le_sum_right_of_group hadm (hxR 0) fun i => hgR i 0)) hE₂

end Groups

/-! ### The reference word is transient for `κ > 4` -/

section RefTrans

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The reference word is transient** (`κ > 4`, given (G5) and (G2)): every evolution of the word with all weights
moved onto the outermost marks has, almost surely, infinite lifetime and the trace event. -/
theorem IsIntegratedSLEEvolution.ae_traceEvent_outerW_gt_four {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hκ4 : 4 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{0} κ) (hG2 : SeparatedTwoForceStatement.{0} κ)
    (hF : IsOrderedForceWord xL xR) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hxL : ∀ i, xL i < 0) (hxR : ∀ j, 0 < xR j) (hn : 0 < nL + nR)
    (hE : IsIntegratedSLEEvolution κ xL xR (outerW ρL) (outerW ρR) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ TraceEvent (fun t => W t ω) (ζ ω) := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hκ : 0 < κ := by linarith
  have hζ := IsIntegratedSLEEvolution.ae_lifetime_eq_top_outerW hκ hF hadm hxL hxR hE
  have hE' := Zhan.IsIntegratedSLEEvolution.relabelOuter hE hζ (neg_two_lt_sum_left hκ hF hadm hxL)
    (neg_two_lt_sum_right hκ hF hadm hxR)
  have hFo := isOrderedForceWord_outerPos hF
  have hadmo := hasAdmissiblePartialSums_outerPos hF hadm hxL hxR
  have h23 := hE'.ae_exists_isGeneratingTrace_top_of_hasAdmissiblePartialSums hκ hFo hadmo
    (fun i => hxL _) (fun j => hxR _)
  have htr := IsIntegratedSLEEvolution.ae_tendsto_norm_trace_groups_gt_four hκ4 hG5 hG2 hFo hadmo
    (fun i => hxL _) (fun j => hxR _) (fun _ _ => rfl) (fun _ _ => rfl) hn hE'
  filter_upwards [h23, htr] with ω h ht
  obtain ⟨hζω, η, hη⟩ := h
  exact ⟨hζω, η, hζω ▸ hη, fun _ => ht η hη⟩

/-- The canonical law of the reference word has infinite lifetime with probability one (every `κ > 0`). -/
theorem codeLaw_outerW_lifetime_of_pos (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR) (hxL : ∀ i, xL i < 0) (hxR : ∀ j, 0 < xR j) :
    codeLaw κ (outerW ρL) (outerW ρR) {x | cζ x = ⊤} (xL, xR) = 1 := by
  obtain ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', hE'⟩ :=
    Sec2.Assembly2.exists_isIntegratedSLEEvolution_of_ordered (ρL := outerW ρL) (ρR := outerW ρR) hκ hF
  exact codeLaw_lifetime_eq_top hκ (fun i j => (hxL i).trans (hxR j)) hE'
    (IsIntegratedSLEEvolution.ae_lifetime_eq_top_outerW hκ hF hadm hxL hxR hE')

/-- Late returns of the canonical reference trace are rare (`κ > 4`, given (G5) and (G2)). -/
theorem codeLaw_outerW_lateSet_tendsto_zero_gt_four (hκ4 : 4 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{0} κ) (hG2 : SeparatedTwoForceStatement.{0} κ)
    (hF : IsOrderedForceWord xL xR) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hxL : ∀ i, xL i < 0) (hxR : ∀ j, 0 < xR j) (hn : 0 < nL + nR) (R : ℝ) :
    Tendsto (fun k => codeLaw κ (outerW ρL) (outerW ρR) (lateSet k R) (xL, xR)) atTop (𝓝 0) := by
  have hκ : 0 < κ := by linarith
  obtain ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', hE'⟩ :=
    Sec2.Assembly2.exists_isIntegratedSLEEvolution_of_ordered (ρL := outerW ρL) (ρR := outerW ρR) hκ hF
  exact codeLaw_lateSet_tendsto_zero hκ (fun i j => (hxL i).trans (hxR j)) hE'
    ((IsIntegratedSLEEvolution.ae_traceEvent_outerW_gt_four hκ4 hG5 hG2 hF hadm hxL hxR hn hE').mono
      fun _ h => h.2) R

end RefTrans

end InteractingSLE.ZhanGT4
