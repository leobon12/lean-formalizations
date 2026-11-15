/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfAvoidLeftQHit
import InteractingSLE.Spec.Supplement.GB7aB

/-!
# Finite-word barriers for every `κ > 0` (toward the `κ′ = 16/κ > 4` barrier of Proposition 5.1 in chart `Q`)

Packet PROVE-CFBARRIER. The counterflow of Proposition 5.1 (chart `Q`, `Prop51Q`) is an `SLE_{κ′}(ρ)`, `κ′ = 16/κ > 4`.
Read in the chart `R ∘ f_t` of the complement of a flow-line prefix `γ(0, t]`, the left part of `∂(ℍ \ γ(0, t])` (the
left side of `γ` and `ℝ₋`) becomes one real half-line, on which the force word is admissible (heights `≤ −λ′`,
PROVE-CFAVOID "What remains" 1(b)); the other half-line carries the right side of `γ`, which the counterflow *does* hit,
so the word is **not** admissible there. PROVE-SEC5-R's `CfAvoidLeftQ.ae_trace_ne_pos` needs admissible partial sums on
*both* sides (Aux. lemma 6); this file removes that restriction.

## One-sided non-hitting (every `κ > 0`)

* `ae_lifetime_eq_top_of_gt`: the lifetime is infinite when the group-end sums of both sides exceed some `c > −2`
  (Aux. lemma 6's first assertion with `κ/2 − 2` replaced by any `c > −2`);
* **`ae_trace_ne_pos_of_right`**: if only the *right* group-end sums are `≥ κ/2 − 2` (and the lifetime is infinite),
  then almost surely no generating trace ever visits a real point `x > 0` at or beyond a right mark — the left side may
  be hit; **`ae_trace_ne_neg_of_left`** is the reflection; `ae_trace_ne_pos_of_right_of_gt` and
  `ae_trace_ne_neg_of_left_of_gt` take the lifetime from `ae_lifetime_eq_top_of_gt`.

The probabilistic core is Aux. lemma 6's right-gap repulsion (`IsIntegratedSLEEvolution.ae_w_lt_vR`, Aux. lemma 5),
which already needs only the right side; the real-contact collision is PROVE-SEC5-R's `trace_ne_of_lt_of_sep`.

## The Girsanov comparison of Aux. lemmas 62–64 without a second mark (every `κ > 0`)

`GB7a.measure_eq_zero_of_evolution` (PROVE-GB7A2) assumes `κ ≤ 4`. The hypothesis enters only through the drift bound
`GB7a.refWeight_drift_ge`, and only when a second comparison mark `k₂` carries the weight `−S`. With no second mark
(`k₂ = none`, the form GB7a's pathwise input `GB7a.GB7aCmpInput` actually uses) the gap drift is
`(2 + S)/(V_k − W) ≥ κ/(2(V_k − W))` for every `κ` with `S ≥ κ/2 − 2`:

* `refWeightR_none_drift_ge`, **`measure_eq_zero_of_evolution_none`**, **`measure_rightCmp_none_eq_zero`**: the
  comparison picture `GB7a.RightCmp … k none S q` is null for every `κ > 0` (in particular `κ′ = 16/κ > 4`).

This is the probabilistic half of a finite-word local barrier (Remark 5.3 / Lemma GB7a) at `κ′ > 4`; its pathwise half
for non-simple traces is not proved here (see `planning/handoffs/PROVE-CFBARRIER.md`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.CfBarrier

open Sec4

/-! ### One-sided non-hitting -/

section OneSided

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- Group-end sums at least `c'` are at least every `c ≤ c'`. -/
theorem hasGroupEndSums_mono {c c' : ℝ} (hcc : c ≤ c') {n : ℕ} {ρ x : Fin n → ℝ}
    (h : HasGroupEndSums c' ρ x) : HasGroupEndSums c ρ x :=
  fun j hj => hcc.trans (h j hj)

/-- **The continuation threshold is infinite** when the group-end sums of both sides are at least some `c > −2`
(`IsIntegratedSLEEvolution.ae_lifetime_eq_top` with `κ/2 − 2` replaced by any `c > −2`; same proof: a group colliding
with the driver at the seed or at a finite lifetime is a whole initial segment of groups, of weight `≥ c > −2`, and
Aux. lemma 3 for noncritical side totals excludes a finite lifetime). -/
theorem ae_lifetime_eq_top_of_gt {c : ℝ} (hc : -2 < c) (hword : IsOrderedForceWord xL xR)
    (hL : HasGroupEndSums c ρL (-xL)) (hR : HasGroupEndSums c ρR xR)
    (h : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) : ∀ᵐ ω ∂P, ζ ω = ⊤ := by
  obtain ⟨hxL, hxL0, hxR, hxR0⟩ := hword
  have hsL := (neg_two_lt_sum_of_hasGroupEndSums hc hL).ne'
  have hsR := (neg_two_lt_sum_of_hasGroupEndSums hc hR).ne'
  filter_upwards [h.ae_tendsto_threshold_of_ne hsL hsR, h.ae_isIntegratedSLEPath] with ω hlim hp
  by_contra hne
  obtain ⟨T, hT⟩ : ∃ T : ℝ≥0, (T : ℝ≥0∞) = ζ ω := ⟨(ζ ω).toNNReal, ENNReal.coe_toNNReal hne⟩
  have hfp := hp.isForcePath
  rcases eq_zero_or_pos T with hT0 | hT0
  · have h0 : ζ ω = 0 := by rw [← hT, hT0, ENNReal.coe_zero]
    exact not_thresholdCondition_of_hasGroupEndSums hc hxL hxR hL hR hxL hxR hxL0 hxR0
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
    refine not_thresholdCondition_of_hasGroupEndSums hc hxL hxR hL hR ?_ ?_ ?_ ?_ ?_ ?_ hth
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

/-- **One-sided right non-hitting** (every `κ > 0`): if the right group-end sums are at least `κ/2 − 2` and the
lifetime is infinite, then almost surely no generating trace visits a real point `x > 0` at or beyond a right mark,
at any time. Nothing is assumed about the left side (it may be hit). -/
theorem ae_trace_ne_pos_of_right (hκ : 0 < κ) (hword : IsOrderedForceWord xL xR)
    (hR : HasGroupEndSums (κ / 2 - 2) ρR xR) (h : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0,
      ∀ (i : Fin nR) (x : ℝ), 0 < x → xR i ≤ x → γ t ≠ x := by
  rcases Nat.eq_zero_or_pos nR with hn | hn
  · exact Eventually.of_forall fun ω γ _ t i => absurd i.2 (by omega)
  filter_upwards [h.ae_w_lt_vR hκ hword hR hζ hn, hζ, h.ae_isIntegratedSLEPath]
    with ω hsep hζω hp γ hγ t i x hx hix
  rw [hζω] at hp
  have h0i : xR ⟨0, hn⟩ ≤ xR i := hword.2.2.1 (Fin.le_def.2 (Nat.zero_le _))
  exact CfAvoidLeftQ.trace_ne_of_lt_of_sep hp hγ (i := ⟨0, hn⟩) hsep t hx (h0i.trans hix)

/-- **One-sided left non-hitting** (the reflection of `ae_trace_ne_pos_of_right`): if the left group-end sums (read
outward, `-xL`) are at least `κ/2 − 2` and the lifetime is infinite, then almost surely no generating trace visits a
real point `x < 0` at or beyond a left mark. Nothing is assumed about the right side. -/
theorem ae_trace_ne_neg_of_left (hκ : 0 < κ) (hword : IsOrderedForceWord xL xR)
    (hL : HasGroupEndSums (κ / 2 - 2) ρL (-xL)) (h : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0,
      ∀ (i : Fin nL) (x : ℝ), x < 0 → x ≤ xL i → γ t ≠ x := by
  rcases Nat.eq_zero_or_pos nL with hn | hn
  · exact Eventually.of_forall fun ω γ _ t i => absurd i.2 (by omega)
  obtain ⟨hxL, hxL0, hxR, hxR0⟩ := id hword
  have hword' : IsOrderedForceWord (-xR) (-xL) :=
    ⟨fun i j hij => neg_le_neg (hxR hij), fun i => neg_nonpos.2 (hxR0 i),
      fun i j hij => neg_le_neg (hxL hij), fun i => neg_nonneg.2 (hxL0 i)⟩
  filter_upwards [h.reflect.ae_w_lt_vR hκ hword' hL hζ hn, hζ, h.ae_isIntegratedSLEPath]
    with ω hsep hζω hp γ hγ t i x hx hix
  rw [hζω] at hp
  have h0i : xL i ≤ xL ⟨0, hn⟩ := hxL (Fin.le_def.2 (Nat.zero_le _))
  refine CfAvoidLeftQ.trace_ne_of_gt_of_sep hp hγ (i := ⟨0, hn⟩) (fun s hs => ?_) t hx (hix.trans h0i)
  have h2 := hsep s hs
  simp only [Pi.neg_apply, neg_lt_neg_iff] at h2
  exact h2

/-- **One-sided right non-hitting with the lifetime from the group-end sums**: right group-end sums `≥ κ/2 − 2`, left
group-end sums `≥ c` for some `c > −2`. -/
theorem ae_trace_ne_pos_of_right_of_gt (hκ : 0 < κ) (hword : IsOrderedForceWord xL xR) {c : ℝ} (hc : -2 < c)
    (hL : HasGroupEndSums c ρL (-xL)) (hR : HasGroupEndSums (κ / 2 - 2) ρR xR)
    (h : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0,
      ∀ (i : Fin nR) (x : ℝ), 0 < x → xR i ≤ x → γ t ≠ x := by
  have hc' : -2 < min c (κ / 2 - 2) := lt_min hc (by linarith)
  exact ae_trace_ne_pos_of_right hκ hword hR h (ae_lifetime_eq_top_of_gt hc' hword
    (hasGroupEndSums_mono (min_le_left _ _) hL) (hasGroupEndSums_mono (min_le_right _ _) hR) h)

/-- **One-sided left non-hitting with the lifetime from the group-end sums**: left group-end sums `≥ κ/2 − 2`, right
group-end sums `≥ c` for some `c > −2`. -/
theorem ae_trace_ne_neg_of_left_of_gt (hκ : 0 < κ) (hword : IsOrderedForceWord xL xR) {c : ℝ} (hc : -2 < c)
    (hL : HasGroupEndSums (κ / 2 - 2) ρL (-xL)) (hR : HasGroupEndSums c ρR xR)
    (h : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0,
      ∀ (i : Fin nL) (x : ℝ), x < 0 → x ≤ xL i → γ t ≠ x := by
  have hc' : -2 < min c (κ / 2 - 2) := lt_min hc (by linarith)
  exact ae_trace_ne_neg_of_left hκ hword hL h (ae_lifetime_eq_top_of_gt hc' hword
    (hasGroupEndSums_mono (min_le_right _ _) hL) (hasGroupEndSums_mono (min_le_left _ _) hR) h)

end OneSided

/-! ### The Girsanov comparison without a second mark -/

section Comparison

open GB7a Girsanov Sec2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞}

/-- The comparison weights with no second mark: `S` at `k`, `0` elsewhere. -/
theorem sum_refWeightR_none_div (k : Fin nR) (S w : ℝ) (vR : Fin nR → ℝ) :
    ∑ j, refWeightR k none S j / (w - vR j) = -(S / (vR k - w)) := by
  simp only [refWeightR, reduceCtorEq, ↓reduceIte, sub_zero, ite_div, zero_div, Finset.sum_ite_eq',
    Finset.mem_univ]
  rw [← neg_sub, div_neg]

/-- **The repulsion of the comparison weights without a second mark** (pointwise, every `κ`): for `S ≥ κ/2 − 2` and
`w < V_k`, the gap drift `2/(V_k − w) − ∑ⱼ ρ′ⱼ/(w − Vⱼ) = (2 + S)/(V_k − w)` is at least `κ/(2(V_k − w))`.
(`GB7a.refWeight_drift_ge` with `k₂ = none` and without `κ ≤ 4`.) -/
theorem refWeightR_none_drift_ge {S : ℝ} (hS : κ / 2 - 2 ≤ S) {k : Fin nR} {w : ℝ} {vR : Fin nR → ℝ}
    (hle : w ≤ vR k) (hne : w ≠ vR k) :
    0 < vR k - w ∧ κ / (2 * (vR k - w)) ≤ 2 / (vR k - w) - ∑ j, refWeightR k none S j / (w - vR j) := by
  have hY : 0 < vR k - w := sub_pos.2 (lt_of_le_of_ne hle hne)
  refine ⟨hY, ?_⟩
  rw [sum_refWeightR_none_div, sub_neg_eq_add, ← add_div, div_le_div_iff₀ (by positivity) hY]
  nlinarith

/-- **Aux. lemmas 62–64's comparison without a second mark, every `κ > 0`** (`S ≥ κ/2 − 2`): almost surely there is
no time `T > q` such that, on `[q, T)`, the marks of nonzero old or comparison weight (and `k`) stay off the driver with
bounded drift energy, while the gap `V_k − W` tends to `0` at `T`. This is `GB7a.measure_eq_zero_of_evolution` with
`k₂ = none` and without its hypothesis `κ ≤ 4` (which only that proof's drift bound with a second mark used); the proof
is the same, with `refWeightR_none_drift_ge` for the drift bound. -/
theorem measure_eq_zero_of_evolution_none {P : Measure Ω} [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {k : Fin nR} {S : ℝ} (hS : κ / 2 - 2 ≤ S)
    (q : ℝ≥0) {A : Set Ω}
    (hA : ∀ ω ∈ A, ∃ T : ℝ≥0, q < T ∧ (T : ℝ≥0∞) ≤ ζ ω ∧
      (∀ t : ℝ≥0, q ≤ t → t < T → (∀ i, ρL i ≠ 0 → W t ω ≠ VL i t ω) ∧
        ∀ j, (ρR j ≠ 0 ∨ refWeightR k none S j ≠ 0 ∨ j = k) → W t ω ≠ VR j t ω) ∧
      (∃ C : ℝ, ∀ t : ℝ≥0, q ≤ t → t < T →
        (∫ s in (q : ℝ)..t, ((∑ i, -ρL i / (W s.toNNReal ω - VL i s.toNNReal ω)) +
          ∑ j, (refWeightR k none S j - ρR j) / (W s.toNNReal ω - VR j s.toNNReal ω)) ^ 2) ≤ C) ∧
      Tendsto (fun t => VR k t ω - W t ω) (𝓝[<] T) (𝓝 0)) :
    P A = 0 := by
  classical
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  -- the good set
  have hgood : ∀ᵐ ω ∂P, IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (B · ω) (ζ ω) ∧ ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
        ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
          Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
          ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀ :=
    hE.2.2.2.2.and (hE.ae_tendsto_threshold hκ)
  set N := toMeasurable P {ω | ¬ (IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (B · ω) (ζ ω) ∧ ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
        ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
          Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
          ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀)} with hNdef
  have hN0 : P N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact ae_iff.1 hgood
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hG𝓖 : MeasurableSet[𝓖 0] Nᶜ := (Ito.measurableSet_usualAugmentation_of_null hNm hN0 0).compl
  have hgoodG : ∀ ω ∈ Nᶜ, _ := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable P _ h)
  have haeG : ∀ᵐ ω ∂P, ω ∈ Nᶜ := compl_mem_ae_iff.2 hN0
  set ζ' : Ω → ℝ≥0∞ := fun ω => if ω ∈ Nᶜ then ζ ω else 0 with hζ'
  set ρa : Fin (nL + nR) → ℝ := Fin.append ρL ρR with hρa
  set ρb : Fin (nL + nR) → ℝ := Fin.append (fun _ => 0) (refWeightR k none S) with hρb
  set k' : Fin (nL + nR) := Fin.natAdd nL k with hk'
  -- the generic hypotheses
  have hB' : IsFilteredBrownianReal 𝓖 B P := hE𝓖.1
  have hW' : AdaptedBefore 𝓖 ζ' W := adaptedBefore_ite_lifetime hE𝓖.2.1 hG𝓖
  have hU' : ∀ j, AdaptedBefore 𝓖 ζ' (allMarks VL VR j) := fun j => by
    cases j using Fin.addCases with
    | left i => rw [allMarks_castAdd]; exact adaptedBefore_ite_lifetime (hE𝓖.2.2.1 i) hG𝓖
    | right i => rw [allMarks_natAdd]; exact adaptedBefore_ite_lifetime (hE𝓖.2.2.2.1 i) hG𝓖
  have hWc' : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ' ω} := fun ω =>
    continuousOn_ite_lifetime fun hω => ((hgoodG ω hω).1.isSLEPathUpTo le_rfl).continuousOn_w
  have hUc' : ∀ j ω, ContinuousOn (allMarks VL VR j · ω) {t | (t : ℝ≥0∞) < ζ' ω} := fun j ω => by
    cases j using Fin.addCases with
    | left i =>
      rw [allMarks_castAdd]
      exact continuousOn_ite_lifetime fun hω => ((hgoodG ω hω).1.isSLEPathUpTo le_rfl).continuousOn_vL i
    | right i =>
      rw [allMarks_natAdd]
      exact continuousOn_ite_lifetime fun hω => ((hgoodG ω hω).1.isSLEPathUpTo le_rfl).continuousOn_vR i
  have hζ'G : ∀ ω ∈ Nᶜ, ζ' ω = ζ ω := fun ω hω => by simp only [hζ', hω, ↓reduceIte]
  have hpath' : ∀ᵐ ω ∂P, CmpPath κ ρa (W · ω) (B · ω) (fun j t => allMarks VL VR j t ω) (ζ' ω) := by
    filter_upwards [haeG] with ω hω
    rw [hζ'G ω hω]
    exact cmpPath_of_isIntegratedSLEPath (hgoodG ω hω).1 (hgoodG ω hω).2
  have hsumb : ∀ (w : ℝ) (u : Fin (nL + nR) → ℝ), ∑ j, ρb j / (w - u j) =
      ∑ j, refWeightR k none S j / (w - u (Fin.natAdd nL j)) := fun w u => by
    rw [Fin.sum_univ_add]
    simp [hρb]
  have hdrift' : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' ω →
      (∀ j, IsMon ρa ρb k' j → W t ω ≠ allMarks VL VR j t ω) →
      0 < allMarks VL VR k' t ω - W t ω ∧ κ / (2 * (allMarks VL VR k' t ω - W t ω)) ≤
        cmpBeta ρb k' (W · ω) (fun j t => allMarks VL VR j t ω) t := by
    filter_upwards [haeG] with ω hω t ht hne
    rw [hζ'G ω hω] at ht
    have hp := (hgoodG ω hω).1.isSLEPathUpTo le_rfl
    have hk := hne k' (Or.inr (Or.inr rfl))
    rw [hk', allMarks_natAdd] at hk
    simp only [cmpBeta, hk', allMarks_natAdd]
    rw [hsumb]
    simp only [allMarks_natAdd]
    exact refWeightR_none_drift_ge (w := W t ω) (vR := fun j => VR j t ω) hS (hp.w_le_vR ht k) hk
  have hA' : ∀ ω ∈ A ∩ Nᶜ, ∃ T : ℝ≥0, q < T ∧ (T : ℝ≥0∞) ≤ ζ' ω ∧
      (∀ t : ℝ≥0, q ≤ t → t < T → ∀ j, IsMon ρa ρb k' j → W t ω ≠ allMarks VL VR j t ω) ∧
      (∃ C : ℝ, ∀ t : ℝ≥0, q ≤ t → t < T →
        (∫ s in (q : ℝ)..t, (∑ j, (ρb j - ρa j) / (W s.toNNReal ω - allMarks VL VR j s.toNNReal ω)) ^ 2) ≤ C) ∧
      Tendsto (fun t => allMarks VL VR k' t ω - W t ω) (𝓝[<] T) (𝓝 0) := by
    intro ω ⟨hωA, hωG⟩
    obtain ⟨T, hqT, hTζ, hgap, ⟨C, hC⟩, hlim⟩ := hA ω hωA
    refine ⟨T, hqT, by rw [hζ'G ω hωG]; exact hTζ, fun t hqt htT j hj => ?_, ⟨C, fun t hqt htT => ?_⟩, ?_⟩
    · cases j using Fin.addCases with
      | left i =>
        rw [allMarks_castAdd]
        refine (hgap t hqt htT).1 i ?_
        rcases hj with h | h | h
        · simpa [hρa] using h
        · simp [hρb] at h
        · exfalso
          have := congrArg Fin.val h
          simp only [hk', Fin.val_castAdd, Fin.val_natAdd] at this
          omega
      | right i =>
        rw [allMarks_natAdd]
        refine (hgap t hqt htT).2 i ?_
        rcases hj with h | h | h
        · exact Or.inl (by simpa [hρa] using h)
        · exact Or.inr (Or.inl (by simpa [hρb] using h))
        · exact Or.inr (Or.inr ((Fin.natAdd_inj nL).1 h))
    · convert hC t hqt htT using 4
      rw [Fin.sum_univ_add]
      simp [hρa, hρb, allMarks_castAdd, allMarks_natAdd, neg_div]
    · simpa [hk', allMarks_natAdd] using hlim
  have h0 := measure_eq_zero_of_cmp (P' := P) (𝓖 := 𝓖) (ζ := ζ') (W := W) (U := allMarks VL VR) (B := B)
    (ρ := ρa) (ρ' := ρb) (k := k') hκ hB' hW' hU' hWc' hUc' hpath' hdrift' q hA'
  refine measure_mono_null (fun ω hω => ?_) (measure_union_null h0 hN0)
  by_cases hωG : ω ∈ Nᶜ
  · exact Or.inl ⟨hω, hωG⟩
  · exact Or.inr (not_not.1 hωG)

/-- **The comparison picture without a second mark is null, every `κ > 0`** (`S ≥ κ/2 − 2`):
`GB7a.measure_rightCmp_eq_zero` at `k₂ = none` without `κ ≤ 4` — in particular at `κ′ = 16/κ > 4`. -/
theorem measure_rightCmp_none_eq_zero {P : Measure Ω} [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {k : Fin nR} {S : ℝ} (hS : κ / 2 - 2 ≤ S)
    (q : ℝ≥0) : P {ω | RightCmp ρL ρR W VL VR ζ k none S q ω} = 0 :=
  measure_eq_zero_of_evolution_none hκ hE hS q fun _ hω => hω

end Comparison

/-! ### Lemma GB7a above `κ = 4`, from its pathwise half -/

open GB7a

/-- **Named input (not proved in Lean): the pathwise half of Lemma GB7a's proof for `κ > 4`.** The body of
`GB7a.GB7aCmpInput` (proved for `0 < κ < 4` by PROVE-GB7A3 as `GB7a.gb7aCmpInput`, through injectivity of the trace)
with `4 < κ` in place of `κ < 4`: almost surely, a visit of the open interval between a right mark `k` and the next
right mark produces the comparison picture `GB7a.RightCmp … k none S` at some rational restart time, for the
cumulative weight `S = ∑_{xᵢ ≤ x_k} ρᵢ`; symmetrically on the left, for the reflected evolution. For `κ > 4` the
trace is not simple; the route (handoff PROVE-CFBARRIER, "Details") restarts after the last contact with the original
real line before the first visit and runs Aux. lemma 61's drift identity in the restart chart, where the future touches
the real line only inside the image of its own past hull. -/
def GB7aCmpInputAbove4 : Prop :=
  ∀ κ : ℝ, 4 < κ → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
    ∀ η : Ω → ℝ≥0 → ℂ, (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) →
    (∀ (k : Fin nR) (a' : ℝ), xR k < a' → (∀ j, xR k < xR j → a' ≤ xR j) →
      ∀ᵐ ω ∂P, (∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω ∧ ∃ y ∈ Ioo (xR k) a', η ω t = y) →
        ∃ q : ℚ, RightCmp ρL ρR W VL VR ζ k none (∑ i ∈ Finset.univ.filter (fun i => xR i ≤ xR k), ρR i)
          (q : ℝ).toNNReal ω) ∧
    (∀ (k : Fin nL) (a : ℝ), a < xL k → (∀ j, xL j < xL k → xL j ≤ a) →
      ∀ᵐ ω ∂P, (∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω ∧ ∃ y ∈ Ioo a (xL k), η ω t = y) →
        ∃ q : ℚ, RightCmp ρR ρL (fun t ω => -W t ω) (fun i t ω => -VR i t ω) (fun i t ω => -VL i t ω) ζ k
          none (∑ i ∈ Finset.univ.filter (fun i => xL k ≤ xL i), ρL i) (q : ℝ).toNNReal ω)

section Above4

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Lemma GB7a for an evolution above `κ = 4`, right side** (from the named pathwise input
`GB7aCmpInputAbove4` and the comparison `measure_rightCmp_none_eq_zero`): if the cumulative weight up to the mark `k`
is at least `κ/2 − 2`, almost surely the trace does not visit the interval between `k` and the next mark. -/
theorem gb7aEvol_right_of_above4 (hIn : GB7aCmpInputAbove4.{u}) (hκ : 4 < κ) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {k : Fin nR} {a' : ℝ} (hka : xR k < a')
    (hnext : ∀ j, xR k < xR j → a' ≤ xR j)
    (hS : κ / 2 - 2 ≤ ∑ i ∈ Finset.univ.filter (fun i => xR i ≤ xR k), ρR i) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → ∀ y ∈ Ioo (xR k) a', η ω t ≠ y := by
  have hin := (hIn κ hκ xL xR ρL ρR hord P 𝓕 W VL VR B ζ hE η hη).1 k a' hka hnext
  have hnull : P (⋃ q : ℚ, {ω | RightCmp ρL ρR W VL VR ζ k none
      (∑ i ∈ Finset.univ.filter (fun i => xR i ≤ xR k), ρR i) (q : ℝ).toNNReal ω}) = 0 :=
    measure_iUnion_null fun q => measure_rightCmp_none_eq_zero (by linarith) hE hS _
  filter_upwards [hin, measure_eq_zero_iff_ae_notMem.1 hnull] with ω hω hω' t ht y hy he
  exact hω' (mem_iUnion.2 (hω ⟨t, ht, y, hy, he⟩))

/-- **Lemma GB7a for an evolution above `κ = 4`, left side** (through the reflected evolution). -/
theorem gb7aEvol_left_of_above4 (hIn : GB7aCmpInputAbove4.{u}) (hκ : 4 < κ) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {k : Fin nL} {a : ℝ} (hka : a < xL k)
    (hnext : ∀ j, xL j < xL k → xL j ≤ a)
    (hS : κ / 2 - 2 ≤ ∑ i ∈ Finset.univ.filter (fun i => xL k ≤ xL i), ρL i) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → ∀ y ∈ Ioo a (xL k), η ω t ≠ y := by
  have hin := (hIn κ hκ xL xR ρL ρR hord P 𝓕 W VL VR B ζ hE η hη).2 k a hka hnext
  have hER := IsIntegratedSLEEvolution.reflect hE
  have hnull : P (⋃ q : ℚ, {ω | RightCmp ρR ρL (fun t ω => -W t ω) (fun i t ω => -VR i t ω)
      (fun i t ω => -VL i t ω) ζ k none (∑ i ∈ Finset.univ.filter (fun i => xL k ≤ xL i), ρL i)
        (q : ℝ).toNNReal ω}) = 0 :=
    measure_iUnion_null fun q => measure_rightCmp_none_eq_zero (by linarith) hER hS _
  filter_upwards [hin, measure_eq_zero_iff_ae_notMem.1 hnull] with ω hω hω' t ht y hy he
  exact hω' (mem_iUnion.2 (hω ⟨t, ht, y, hy, he⟩))

end Above4

end InteractingSLE.Sec5.CfBarrier
