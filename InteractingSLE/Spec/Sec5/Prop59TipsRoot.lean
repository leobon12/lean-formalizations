/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6Contact
import InteractingSLE.Spec.Supplement.GB9Cap
import InteractingSLE.Spec.Sec5.Lemma57Visit

/-!
# Proposition 5.9 at the root `0` (Corollary 5.12): the tip from the unboundedness of the alternating construction

Packet PROVE-PROP59T. Specification §5.2, proof of Proposition 5.9 (`source/spec/p145-192.md` L64–L72,
pp. 147–148) and Corollary 5.12, at the root `0` with no initial flow prefix (proof of Proposition 5.13, p. 150: "We
now use the construction in the proof of Proposition 5.9 with root 0, with no initial flow prefix"):

> Finally, `ψ⁻¹` has a continuous boundary value at the prime end `∞`, equal to `η′(r)`. […] Thus unbounded points of
> the successful image trajectories pull back to points approaching `η′(r)`. The closed accessible set associated
> with the allowed angle set contains every successful finite prefix. It therefore contains `η′(r)` […]. Apply the
> conclusion to positive rational `r` […]. Countability and continuity of the counterflow, including the terminal
> limit, show that the entire stopped counterflow range lies in the closed accessible set.

In the capacity chart of the counterflow (`γ` a generating trace of its driver `w` on `[0, ∞)`, started at `0`; the
flow lines issue from `∞`), the conditional domain chart at the counterflow time `r` with root `0` is the own-component
chart `ψ_r = R ∘ f_r` (`ownComponentChart`, `R(z) = −1/z`, `f_r` the centred Loewner map): it sends the remaining
domain `ℍ ∖ K_r` onto `ℍ`, the flow-line root `∞` to `0` and the counterflow tip `γ(r)` to `∞`, and its inverse tends to
`γ(r)` at `∞` (`Supp8.GB6.tendsto_ownComponentChart_inv_tip`; the [LT06] boundary extension at the tip prime end).

## Main results

* **`mem_closure_of_not_isBounded_ownChart`** (deterministic): a set `A ⊆ ℍ ∖ K_r` whose `ψ_r`-image is unbounded
  accumulates at the tip `γ(r)`;
* **`ae_tip0_of_unbounded`** (`htip0` of `Sec5.prop513_path_of_tips`): if, at every positive rational counterflow time
  `r`, the points of a countable family `{z n}` that lie in `ℍ ∖ K_r` have an almost surely unbounded `ψ_r`-image (the
  conclusion of the alternating extreme-angle construction at the root `0`; `Tip0UnboundedStatement`), then for every
  rational `q ≥ 0`, almost surely `γ(q)` lies in the closure of `{z n}` (positive `q` by the chart, `q = 0` by
  continuity);
* **`ae_tip_of_unbounded`** (`htip` of `Sec5.prop513_path_of_tips` at one root `z`): the same at a root `z` with
  descendant portions `S` and cone `L = closure ({z} ∪ S)`, on `{q < T_z}` (`TipUnboundedStatement`).

`Tip0UnboundedStatement` and `TipUnboundedStatement` are the probabilistic content of the alternating construction
(pp. 143–147); they are not proved here (see the handoff `planning/handoffs/PROVE-PROP59T.md`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE

namespace Sec5

namespace Prop59Tips

/-- **The tip is in the closure of a set with unbounded image in the own-component chart** (deterministic; p. 148).
Let `γ` be a generating trace of the continuous driver `w` (`w 0 = 0`) on `[0, ∞)`. If `A ⊆ ℍ ∖ K_r` and
`ψ_r(A)` is unbounded, then `γ(r) ∈ closure A`. -/
theorem mem_closure_of_not_isBounded_ownChart {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ)
    (hw : Continuous w) (hw0 : w 0 = 0) (r : ℝ≥0) {A : Set ℂ}
    (hA : A ⊆ H \ fwdHull (fun s : ℝ => w s.toNNReal) r)
    (hunb : ¬ Bornology.IsBounded ((ownComponentChart (fun s : ℝ => w s.toNNReal) r).1 '' A)) :
    γ r ∈ closure A := by
  have hW : Continuous fun s : ℝ => w s.toNNReal := hw.comp continuous_real_toNNReal
  have hc := isDomainChart_ownComponentChart hW (by simp [hw0]) r.coe_nonneg
  have htend := Supp8.GB6.tendsto_ownComponentChart_inv_tip hγ hw.continuousOn hw0
    (s := r) ENNReal.coe_lt_top
  have hTD : (ownComponentChart (fun s : ℝ => w s.toNNReal) r).1 '' A ⊆ H := by
    rintro _ ⟨z, hz, rfl⟩
    exact hc.fwd_mem (hA hz)
  have h := Supp8.GB9Cap.mem_closure_image_of_tendsto_cobounded htend hTD hunb
  have himg : (ownComponentChart (fun s : ℝ => w s.toNNReal) r).2.1 ''
      ((ownComponentChart (fun s : ℝ => w s.toNNReal) r).1 '' A) = A := by
    rw [image_image]
    conv_rhs => rw [← image_id A]
    exact image_congr fun z hz => hc.inv_fwd (hA hz)
  rwa [himg] at h

/-- The rational times `1/(m + 1)` tend to `0`. -/
theorem tendsto_toNNReal_one_div : Tendsto (fun m : ℕ => ((1 / ((m : ℚ) + 1) : ℚ) : ℝ).toNNReal) atTop (𝓝 0) := by
  have h1 : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 := (continuous_real_toNNReal.tendsto 0).comp h1
  simp only [Real.toNNReal_zero] at h2
  refine h2.congr fun m => ?_
  simp only [Function.comp_apply]
  push_cast
  rfl

/-- **The named conclusion of the alternating construction at the root `0`** (proof of Proposition 5.9, pp. 143–147,
with the two extreme angles, root `0`, no initial prefix; Corollary 5.12): at every positive rational counterflow time
`r`, almost surely the points of the countable extreme-angle family `{z n}` lying in the remaining domain `ℍ ∖ K_r`
have an unbounded image under the conditional domain chart `ψ_r`. Not proved here. -/
def Tip0UnboundedStatement {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (z : ℕ → Ω → ℂ) : Prop :=
  ∀ r : ℚ, 0 < r → ∀ᵐ ω ∂P, ¬ Bornology.IsBounded
    ((ownComponentChart (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal).1 ''
      (range (fun n => z n ω) ∩ (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal)))

/-- **`htip0` of `Sec5.prop513_path_of_tips` from the alternating construction** (conditional helper, distinct name;
pp. 147–148 and Corollary 5.12). Let `γ ω` be a generating trace on `[0, ∞)` of the continuous driver `W · ω`
(`W 0 = 0`) almost surely, and let the countable family `{z n}` satisfy `Tip0UnboundedStatement`. Then for every
rational `q ≥ 0`, almost surely `γ(q)` lies in the closure of `{z n}`: at positive `q` by the chart
(`mem_closure_of_not_isBounded_ownChart`), at `q = 0` as the limit of the tips at the times `1/(m + 1)`. -/
theorem ae_tip0_of_unbounded {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {z : ℕ → Ω → ℂ}
    (htr : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (hunb : Tip0UnboundedStatement P W z) :
    ∀ q : ℚ, 0 ≤ q → ∀ᵐ ω ∂P, γ ω (q : ℝ).toNNReal ∈ closure (range fun n => z n ω) := by
  have hpos : ∀ᵐ ω ∂P, ∀ r : ℚ, 0 < r → γ ω (r : ℝ).toNNReal ∈ closure (range fun n => z n ω) := by
    rw [ae_all_iff]
    intro r
    by_cases hr : 0 < r
    · filter_upwards [htr, hunb r hr] with ω ⟨hw, hw0, hγ⟩ hu _
      exact closure_mono inter_subset_left
        (mem_closure_of_not_isBounded_ownChart hγ hw hw0 _ inter_subset_right hu)
    · exact Eventually.of_forall fun _ h => absurd h hr
  intro q hq
  filter_upwards [htr, hpos] with ω ⟨_, _, hγ⟩ hω
  rcases hq.lt_or_eq with hq0 | hq0
  · exact hω q hq0
  · -- `q = 0`: the limit of the tips at the times `1/(m + 1)`
    subst hq0
    have hγc : Continuous (γ ω) := continuous_of_isGeneratingTrace_top hγ
    have hmem : ∀ m : ℕ, γ ω ((1 / ((m : ℚ) + 1) : ℚ) : ℝ).toNNReal ∈ closure (range fun n => z n ω) :=
      fun m => hω _ (by positivity)
    have := isClosed_closure.mem_of_tendsto ((hγc.tendsto 0).comp tendsto_toNNReal_one_div) (Eventually.of_forall hmem)
    simpa using this

/-- **The named conclusion of the alternating construction at a root `z`** (proof of Proposition 5.9, pp. 143–147,
two extreme angles, root `z` the terminal point of an allowed stopped prefix): at every positive rational counterflow
time `r` before the first visit `T_z` of `z`, almost surely the post-root portions `S` of the descendants of the
prefix, read in the remaining domain `ℍ ∖ K_r`, have an unbounded image under the chart `ψ_r`. (Mapping out the
prefix as well, as the source does, changes the chart by a hydrodynamically normalized map, which preserves
unboundedness; the chart `ψ_r` suffices for the pull-back.) Not proved here. -/
def TipUnboundedStatement {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (z : Ω → ℂ) (S : Ω → Set ℂ) : Prop :=
  ∀ r : ℚ, 0 < r → ∀ᵐ ω ∂P, (r : ℝ) < traceFirstVisit (γ ω) (z ω) → ¬ Bornology.IsBounded
    ((ownComponentChart (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal).1 ''
      (S ω ∩ (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal)))

/-- **`htip` of `Sec5.prop513_path_of_tips` from the alternating construction** (conditional helper, distinct name;
pp. 147–148). Let `γ ω` be a generating trace on `[0, ∞)` of the continuous driver `W · ω` (`W 0 = 0`) almost surely,
`z` a root with descendant portions `S` and closed cone `L = closure ({z} ∪ S)`, and let `TipUnboundedStatement` hold.
Then for every rational `q ≥ 0`, almost surely, if `q < T_z` then `γ(q) ∈ L`: at positive `q` by the chart, at
`q = 0` as the limit of the tips at the times `1/(m + 1) < T_z`. -/
theorem ae_tip_of_unbounded {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {z : Ω → ℂ} {S L : Ω → Set ℂ}
    (htr : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (hLS : ∀ ω, L ω = closure (insert (z ω) (S ω))) (hunb : TipUnboundedStatement P W γ z S) :
    ∀ q : ℚ, 0 ≤ q → ∀ᵐ ω ∂P, (q : ℝ) < traceFirstVisit (γ ω) (z ω) → γ ω (q : ℝ).toNNReal ∈ L ω := by
  have hpos : ∀ᵐ ω ∂P, ∀ r : ℚ, 0 < r → (r : ℝ) < traceFirstVisit (γ ω) (z ω) →
      γ ω (r : ℝ).toNNReal ∈ L ω := by
    rw [ae_all_iff]
    intro r
    by_cases hr : 0 < r
    · filter_upwards [htr, hunb r hr] with ω ⟨hw, hw0, hγ⟩ hu _ hrT
      rw [hLS ω]
      exact closure_mono (inter_subset_left.trans (subset_insert _ _))
        (mem_closure_of_not_isBounded_ownChart hγ hw hw0 _ inter_subset_right (hu hrT))
    · exact Eventually.of_forall fun _ h => absurd h hr
  intro q hq
  filter_upwards [htr, hpos] with ω ⟨_, _, hγ⟩ hω hqT
  rcases hq.lt_or_eq with hq0 | hq0
  · exact hω q hq0 hqT
  · subst hq0
    have hγc : Continuous (γ ω) := continuous_of_isGeneratingTrace_top hγ
    have hT : (0 : ℝ) < traceFirstVisit (γ ω) (z ω) := by exact_mod_cast hqT
    have hev : ∀ᶠ m : ℕ in atTop, ((1 / ((m : ℚ) + 1) : ℚ) : ℝ) < traceFirstVisit (γ ω) (z ω) := by
      have h1 : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      filter_upwards [h1.eventually (gt_mem_nhds hT)] with m hm
      push_cast
      exact hm
    have hmem : ∀ᶠ m : ℕ in atTop, γ ω ((1 / ((m : ℚ) + 1) : ℚ) : ℝ).toNNReal ∈ L ω := by
      filter_upwards [hev] with m hm
      exact hω _ (by positivity) hm
    have hcl : IsClosed (L ω) := by rw [hLS ω]; exact isClosed_closure
    have := hcl.mem_of_tendsto ((hγc.tendsto 0).comp tendsto_toNNReal_one_div) hmem
    simpa using this

end Prop59Tips

end Sec5

end InteractingSLE
