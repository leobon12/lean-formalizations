/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.GB7aAbove4

/-!
# The junction barrier for finite words, every `κ > 0`

Packet PROVE-CFBARRIER2 (PROVE-CFBARRIER's finding: clause 2 of `CfAvoidLeftQ.FirstContactNotLeft` needs a *junction*
barrier — a boundary point between two barrier arcs must not be visited). For an integrated `SLE_κ(ρ)` evolution of
an ordered word, let `x_k > 0` be a right mark position, `x_{k'} < x_k` the previous distinct right mark position, and
`a'` at most the next one. If both adjacent intervals are GB7a barriers — the cumulative weights
`S' = ∑_{xᵢ ≤ x_{k'}} ρᵢ` and `S = ∑_{xᵢ ≤ x_k} ρᵢ` are at least `κ/2 − 2` — then almost surely the trace never visits
`x_k` itself (`ae_trace_ne_junction_right`; reflected, `ae_trace_ne_junction_left`), and hence avoids the whole interval
`(x_{k'}, a')` (`ae_trace_notMem_junction_right`).

**Proof.** By Lemma GB7a (`GB7aAbove4.gb7aEvol_right_any`) neither adjacent interval is visited. A visit of `x_k` is
then the first visit of `[x_k, ∞)`, approached from `ℍ` (real contacts accumulating at it would visit the left interval;
a first visit beyond `a'` would swallow `x_k` without visiting it, after which it is never visited). Restarting at a
rational time `q` just before, compare with the reference word that keeps the weights of the marks at `x_k` and puts the
cumulative weight `S'` on the mark `k'` (`junctionWeight`): in the chart at `q` the marks between the driver and the
target `x_k` carry comparison weights summing to `S' − S' = 0`, the marks at `x_k` carry `0`, so the drift energy is
bounded (`GB7aAbove4.exists_energy_bound_of_restart_above4`), while the gap of `k'` tends to `0`. Under the reference
the gap `Y' = V_{k'} − W` has drift `(2 + S')/Y' + ρ_G/Y ≥ (2 + min(S', S))/Y' ≥ κ/(2Y')` (`Y = V_k − W ≥ Y'`,
`ρ_G = S − S'`), so it never reaches `0` (`GB7a.measure_eq_zero_of_cmp`, Aux. lemmas 62–64).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec5.CfJunction

open GB7a Girsanov Sec2

/-! ### The comparison picture with general reference weights -/

section General

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞}

/-- **The comparison picture with right reference weights `ρ'`** (one path): `GB7a.RightCmpPath` with the reference
weights `refWeightR k k₂ S` replaced by any `ρ'` (no left reference marks), the repelled mark `k`. -/
def GenCmpPath (ρL : Fin nL → ℝ) (ρR ρ' : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (k : Fin nR) (q : ℝ≥0) : Prop :=
  ∃ T : ℝ≥0, q < T ∧ (T : ℝ≥0∞) ≤ ζ ∧
    (∀ t : ℝ≥0, q ≤ t → t < T → (∀ i, ρL i ≠ 0 → w t ≠ vL i t) ∧
      ∀ j, (ρR j ≠ 0 ∨ ρ' j ≠ 0 ∨ j = k) → w t ≠ vR j t) ∧
    (∃ C : ℝ, ∀ t : ℝ≥0, q ≤ t → t < T →
      (∫ s in (q : ℝ)..t, ((∑ i, -ρL i / (w s.toNNReal - vL i s.toNNReal)) +
        ∑ j, (ρ' j - ρR j) / (w s.toNNReal - vR j s.toNNReal)) ^ 2) ≤ C) ∧
    Tendsto (fun t => vR k t - w t) (𝓝[<] T) (𝓝 0)

/-- **The comparison picture is null when the reference repels the mark `k`** (Aux. lemmas 62–64, every `κ > 0`):
if almost surely, whenever `k` is off the driver, the reference gap drift `2/(V_k − W) − ∑ⱼ ρ′ⱼ/(W − Vⱼ)` is at least
`κ/(2(V_k − W))`, then for each `q` the comparison picture has probability `0`.
(`CfBarrier.measure_eq_zero_of_evolution_none` with general reference weights; the same proof.) -/
theorem measure_genCmp_eq_zero {P : Measure Ω} [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {ρ' : Fin nR → ℝ} {k : Fin nR}
    (hβ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → W t ω ≠ VR k t ω →
      0 < VR k t ω - W t ω ∧
        κ / (2 * (VR k t ω - W t ω)) ≤ 2 / (VR k t ω - W t ω) - ∑ j, ρ' j / (W t ω - VR j t ω))
    (q : ℝ≥0) :
    P {ω | GenCmpPath ρL ρR ρ' (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω) k q} = 0 := by
  classical
  set A := {ω | GenCmpPath ρL ρR ρ' (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω) k q} with hAdef
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hgood : ∀ᵐ ω ∂P, IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (B · ω) (ζ ω) ∧ ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
        ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
          Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
          ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀ :=
    hE.2.2.2.2.and (hE.ae_tendsto_threshold hκ)
  set N := toMeasurable P {ω | ¬ ((IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (B · ω) (ζ ω) ∧ ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
        ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
          Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
          ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → W t ω ≠ VR k t ω →
        0 < VR k t ω - W t ω ∧
          κ / (2 * (VR k t ω - W t ω)) ≤ 2 / (VR k t ω - W t ω) - ∑ j, ρ' j / (W t ω - VR j t ω))}
    with hNdef
  have hN0 : P N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact ae_iff.1 (hgood.and hβ)
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hG𝓖 : MeasurableSet[𝓖 0] Nᶜ := (Ito.measurableSet_usualAugmentation_of_null hNm hN0 0).compl
  have hgoodG : ∀ ω ∈ Nᶜ, _ := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable P _ h)
  have haeG : ∀ᵐ ω ∂P, ω ∈ Nᶜ := compl_mem_ae_iff.2 hN0
  set ζ' : Ω → ℝ≥0∞ := fun ω => if ω ∈ Nᶜ then ζ ω else 0 with hζ'
  set ρa : Fin (nL + nR) → ℝ := Fin.append ρL ρR with hρa
  set ρb : Fin (nL + nR) → ℝ := Fin.append (fun _ => 0) ρ' with hρb
  set k' : Fin (nL + nR) := Fin.natAdd nL k with hk'
  have hB' : IsFilteredBrownianReal 𝓖 B P := hE𝓖.1
  have hW' : AdaptedBefore 𝓖 ζ' W := adaptedBefore_ite_lifetime hE𝓖.2.1 hG𝓖
  have hU' : ∀ j, AdaptedBefore 𝓖 ζ' (allMarks VL VR j) := fun j => by
    cases j using Fin.addCases with
    | left i => rw [allMarks_castAdd]; exact adaptedBefore_ite_lifetime (hE𝓖.2.2.1 i) hG𝓖
    | right i => rw [allMarks_natAdd]; exact adaptedBefore_ite_lifetime (hE𝓖.2.2.2.1 i) hG𝓖
  have hWc' : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ' ω} := fun ω =>
    continuousOn_ite_lifetime fun hω => ((hgoodG ω hω).1.1.isSLEPathUpTo le_rfl).continuousOn_w
  have hUc' : ∀ j ω, ContinuousOn (allMarks VL VR j · ω) {t | (t : ℝ≥0∞) < ζ' ω} := fun j ω => by
    cases j using Fin.addCases with
    | left i =>
      rw [allMarks_castAdd]
      exact continuousOn_ite_lifetime fun hω => ((hgoodG ω hω).1.1.isSLEPathUpTo le_rfl).continuousOn_vL i
    | right i =>
      rw [allMarks_natAdd]
      exact continuousOn_ite_lifetime fun hω => ((hgoodG ω hω).1.1.isSLEPathUpTo le_rfl).continuousOn_vR i
  have hζ'G : ∀ ω ∈ Nᶜ, ζ' ω = ζ ω := fun ω hω => by simp only [hζ', hω, ↓reduceIte]
  have hpath' : ∀ᵐ ω ∂P, CmpPath κ ρa (W · ω) (B · ω) (fun j t => allMarks VL VR j t ω) (ζ' ω) := by
    filter_upwards [haeG] with ω hω
    rw [hζ'G ω hω]
    exact cmpPath_of_isIntegratedSLEPath (hgoodG ω hω).1.1 (hgoodG ω hω).1.2
  have hsumb : ∀ (w : ℝ) (u : Fin (nL + nR) → ℝ), ∑ j, ρb j / (w - u j) =
      ∑ j, ρ' j / (w - u (Fin.natAdd nL j)) := fun w u => by
    rw [Fin.sum_univ_add]
    simp [hρb]
  have hdrift' : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' ω →
      (∀ j, IsMon ρa ρb k' j → W t ω ≠ allMarks VL VR j t ω) →
      0 < allMarks VL VR k' t ω - W t ω ∧ κ / (2 * (allMarks VL VR k' t ω - W t ω)) ≤
        cmpBeta ρb k' (W · ω) (fun j t => allMarks VL VR j t ω) t := by
    filter_upwards [haeG] with ω hω t ht hne
    rw [hζ'G ω hω] at ht
    have hk := hne k' (Or.inr (Or.inr rfl))
    rw [hk', allMarks_natAdd] at hk
    simp only [cmpBeta, hk', allMarks_natAdd]
    rw [hsumb]
    simp only [allMarks_natAdd]
    exact (hgoodG ω hω).2 t ht hk
  have hA' : ∀ ω ∈ A ∩ Nᶜ, ∃ T : ℝ≥0, q < T ∧ (T : ℝ≥0∞) ≤ ζ' ω ∧
      (∀ t : ℝ≥0, q ≤ t → t < T → ∀ j, IsMon ρa ρb k' j → W t ω ≠ allMarks VL VR j t ω) ∧
      (∃ C : ℝ, ∀ t : ℝ≥0, q ≤ t → t < T →
        (∫ s in (q : ℝ)..t, (∑ j, (ρb j - ρa j) / (W s.toNNReal ω - allMarks VL VR j s.toNNReal ω)) ^ 2) ≤ C) ∧
      Tendsto (fun t => allMarks VL VR k' t ω - W t ω) (𝓝[<] T) (𝓝 0) := by
    intro ω ⟨hωA, hωG⟩
    obtain ⟨T, hqT, hTζ, hgap, ⟨C, hC⟩, hlim⟩ := hωA
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

end General

/-! ### The junction reference weights -/

section Weights

variable {nR : ℕ}

/-- **The junction reference weights**: the cumulative weight `S'` on the mark `k'`, the actual weights on the marks at
the junction position `x_k`, `0` elsewhere. -/
def junctionWeight (xR ρR : Fin nR → ℝ) (k' k : Fin nR) (S' : ℝ) (j : Fin nR) : ℝ :=
  (if j = k' then S' else 0) + (if xR j = xR k then ρR j else 0)

/-- The reference gap drift at the junction, pointwise. -/
theorem sum_junctionWeight_div {xR ρR : Fin nR → ℝ} {k' k : Fin nR} (S' w : ℝ) {vR : Fin nR → ℝ}
    (hG : ∀ j, xR j = xR k → vR j = vR k) :
    ∑ j, junctionWeight xR ρR k' k S' j / (w - vR j) =
      S' / (w - vR k') + (∑ j ∈ univ.filter (fun j => xR j = xR k), ρR j) / (w - vR k) := by
  classical
  simp only [junctionWeight, add_div, Finset.sum_add_distrib, ite_div, zero_div, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  congr 1
  rw [← Finset.sum_filter, Finset.sum_div]
  exact Finset.sum_congr rfl fun j hj => by rw [hG j (Finset.mem_filter.1 hj).2]

/-- **The algebra of the junction drift bound.** -/
theorem junction_drift_ge {κ S' ρG Y' Y : ℝ} (hY' : 0 < Y') (hYY : Y' ≤ Y) (h1 : κ / 2 - 2 ≤ S')
    (h2 : κ / 2 - 2 ≤ S' + ρG) : κ / (2 * Y') ≤ 2 / Y' + S' / Y' + ρG / Y := by
  have hY : 0 < Y := hY'.trans_le hYY
  have hbase : κ / (2 * Y') ≤ (2 + min S' (S' + ρG)) / Y' := by
    rw [div_le_div_iff₀ (by positivity) hY']
    have : κ / 2 - 2 ≤ min S' (S' + ρG) := le_min h1 h2
    nlinarith
  rcases le_or_gt 0 ρG with hρ | hρ
  · have h3 : 0 ≤ ρG / Y := div_nonneg hρ hY.le
    have h4 : (2 + min S' (S' + ρG)) / Y' ≤ 2 / Y' + S' / Y' := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by linarith [min_le_left S' (S' + ρG)]) hY'.le
    linarith
  · have h3 : ρG / Y' ≤ ρG / Y := by
      rw [div_le_div_iff₀ hY' hY]
      nlinarith
    have h4 : (2 + min S' (S' + ρG)) / Y' ≤ 2 / Y' + S' / Y' + ρG / Y' := by
      rw [← add_div, ← add_div]
      exact div_le_div_of_nonneg_right (by linarith [min_le_right S' (S' + ρG)]) hY'.le
    linarith

end Weights

section Drift

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞} {P : Measure Ω}

/-- The cumulative weight up to `x_k` splits at the previous distinct position `x_{k'}`. -/
theorem sum_le_eq_sum_le_add_sum_eq (xR ρR : Fin nR → ℝ) {k' k : Fin nR} (hk'k : xR k' < xR k)
    (hprev : ∀ j, xR j < xR k → xR j ≤ xR k') :
    ∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i =
      (∑ i ∈ univ.filter (fun i => xR i ≤ xR k'), ρR i) + ∑ i ∈ univ.filter (fun i => xR i = xR k), ρR i := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (univ.filter (fun i => xR i ≤ xR k)) (fun i => xR i ≤ xR k'),
    Finset.filter_filter, Finset.filter_filter]
  congr 1
  · refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun _ _ => rfl
    exact ⟨fun h => h.2, fun h => ⟨h.trans hk'k.le, h⟩⟩
  · refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun _ _ => rfl
    refine ⟨fun h => ?_, fun h => ⟨h.le, ?_⟩⟩
    · rcases h.1.lt_or_eq with hlt | heq
      · exact absurd (hprev i hlt) h.2
      · exact heq
    · rw [h]; exact not_le.2 hk'k

/-- **The junction reference repels the mark `k'`** (almost surely, whenever `k'` is off the driver), when both
cumulative weights `S' = ∑_{xᵢ ≤ x_{k'}} ρᵢ` and `S = ∑_{xᵢ ≤ x_k} ρᵢ` are at least `κ/2 − 2`. -/
theorem ae_junction_drift_ge (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {k' k : Fin nR} (hk'k : xR k' < xR k)
    (hprev : ∀ j, xR j < xR k → xR j ≤ xR k')
    (h1 : κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => xR i ≤ xR k'), ρR i)
    (h2 : κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → W t ω ≠ VR k' t ω →
      0 < VR k' t ω - W t ω ∧ κ / (2 * (VR k' t ω - W t ω)) ≤ 2 / (VR k' t ω - W t ω) -
        ∑ j, junctionWeight xR ρR k' k (∑ i ∈ univ.filter (fun i => xR i ≤ xR k'), ρR i) j / (W t ω - VR j t ω) := by
  filter_upwards [hE.2.2.2.2] with ω hp t ht hne
  have h := hp.isForcePath
  set S' := ∑ i ∈ univ.filter (fun i => xR i ≤ xR k'), ρR i with hS'
  set ρG := ∑ i ∈ univ.filter (fun i => xR i = xR k), ρR i with hρG
  have hY' : 0 < VR k' t ω - W t ω := sub_pos.2 (lt_of_le_of_ne (h.w_le_vR ht k') hne)
  have hidx : k' ≤ k := by
    by_contra hlt
    push Not at hlt
    exact absurd (hord.2.2.1 hlt.le) (not_le.2 hk'k)
  have hYY : VR k' t ω - W t ω ≤ VR k t ω - W t ω := by linarith [h.monotone_vR ht hidx]
  have hG : ∀ j, xR j = xR k → VR j t ω = VR k t ω := fun j hj =>
    Sec2.Assembly.vR_eq_of_eq h ht (by rw [h.vR_zero j, h.vR_zero k, hj]) ⟨zero_le, le_rfl⟩
  refine ⟨hY', ?_⟩
  rw [sum_junctionWeight_div S' (W t ω) (vR := fun j => VR j t ω) hG]
  have e1 : S' / (W t ω - VR k' t ω) = -(S' / (VR k' t ω - W t ω)) := by rw [← neg_sub, div_neg]
  have e2 : ρG / (W t ω - VR k t ω) = -(ρG / (VR k t ω - W t ω)) := by rw [← neg_sub, div_neg]
  rw [e1, e2]
  have hsplit := sum_le_eq_sum_le_add_sum_eq xR ρR hk'k hprev
  have := junction_drift_ge (κ := κ) (ρG := ρG) hY' hYY h1 (by rw [← hsplit]; exact h2)
  linarith

end Drift

end Sec5.CfJunction

end InteractingSLE
