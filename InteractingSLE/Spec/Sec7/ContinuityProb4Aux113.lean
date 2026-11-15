/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb4Cover
import InteractingSLE.Spec.Sec4.ZeroMarks
import InteractingSLE.Spec.Sec7.ContinuityProb3Steps

/-!
# §7.3: Aux. lemma 103 (finite-time continuity) and the prefix part of Aux. lemma 113

Packet PROVE-SEC7-C4. Specification §7.3, Aux. lemma 103 (`source/spec/p337-384.md` L288–L305, pp. 349–350) and
Aux. lemma 113 (L688–L740, pp. 369–372).

* `ExistsEvolutionStatement`: **named input**, Theorem 2.2's existence (the frozen statement
  `exists_isIntegratedSLEEvolution` for every word; anchor `DRAFT_SORRY`, PROVE-SEC2-PATCH3). The band transfer applies
  the smaller-count completeness to the word with one side deleted, which needs that word to have an evolution.
* `ae_solvable_of_isIntegratedSLEEvolution`: an evolution from a separated start makes Wiener-almost every path
  solvable from it.
* `isCompleteForceWord_zero_right`, `isCompleteForceWord_zero_left`: the word with one side deleted (weights `0`) is
  complete under the smaller-count hypothesis (zero-weight deletion and amalgamation).
* **`ae_isGeneratingTrace_lifetime`** (Aux. lemma 103): almost surely a continuous generating trace on `[0, ζ]`,
  through a finite continuation threshold, for every ordered word with fewer than `N` marks on each side, from a
  separated start or an initial trace.
* `SameSideMeet`, `mergeTime` (the stopping time of Aux. lemma 113), `sameSideMeet_mergeTime`,
  `sameSideMeet_of_le` (merged groups stay merged), `isStoppingTime_mergeTime`, **`exists_countPrefix`**.
* Named inputs `SeedEntranceStatement` (the case `D_0 = 0` of Aux. lemma 103), `Aux113TransienceStatement` and
  `LPAux113TransienceStatement` (Aux. lemma 113, "It remains to treat `τ = ∞`").
* **`aux113PrefixStatement_of_inputs`**, **`lpAux113PrefixStatement_of_inputs`**: PROVE-RANDRESTART2's named prefix
  inputs `Aux113PrefixStatement` and `LPAux113PrefixStatement κ` from these.

These are conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

open Sec2 Sec2.Assembly Sec2.Restart RandRestart Band

variable {nL nR : ℕ}

/-! ### Named input: Theorem 2.2, existence -/

/-- **Named input: Theorem 2.2, existence** — exactly the frozen statement `exists_isIntegratedSLEEvolution`
(Specification p. 21; anchor `spec_exists_isIntegratedSLEEvolution_v1`, `DRAFT_SORRY`, packet PROVE-SEC2-PATCH3),
quantified over all words. The band argument applies the smaller-count induction hypothesis to the word with one
side deleted, which needs an evolution of that word to exist. -/
def ExistsEvolutionStatement : Prop :=
  ∀ {a : ℝ}, 0 < a → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR →
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ

/-- **An evolution from a separated start: Wiener-almost every path drives a solution** (the converse of
`exists_isIntegratedSLEEvolution_of_ae_wienerPath`; canonical law of the sure event). -/
theorem ae_solvable_of_isIntegratedSLEEvolution {κ : ℝ} (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hsep : ∀ i j, xL i < xR j) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ f ∂wienerPath, enc f ∈ Prod.fst '' CRel κ xL xR ρL ρR := by
  have e := measure_eventOf_eq_codeLaw hκ hsep hE (S := univ) (Φ := fun _ _ => True) MeasurableSet.univ
    (fun _ _ _ => by simp only [mem_univ]) (fun _ _ _ _ h => h)
  simp only [ofPred_true, measure_univ] at e
  have hm : MeasurableSet (Prod.mk (xL, xR) ⁻¹' restartSetS κ ρL ρR (univ : Set (XCode nL nR))) :=
    (measurableSet_restartSetS MeasurableSet.univ).preimage measurable_prodMk_left
  have h2 : wienerPath (Prod.mk (xL, xR) ⁻¹' restartSetS κ ρL ρR (univ : Set (XCode nL nR))) =
      wienerPath univ := by rw [measure_univ]; exact e.symm
  filter_upwards [(ae_iff_measure_eq hm.nullMeasurableSet).2 h2] with f hf
  obtain ⟨x, ⟨⟨hxF, -⟩, -⟩, hx⟩ := hf
  simp only [Prod.mk.injEq] at hx
  exact ⟨x, mem_cRelF_iff.1 ⟨hxF, hx.1⟩, hx.2⟩

/-! ### The reduced words are complete -/

/-- **Deleting the right group** (all right weights `0`): complete as soon as the words with fewer than `N` marks
are, when `nL < N` (zero-weight deletion `IsIntegratedSLEEvolution.compEmb` and amalgamation). -/
theorem isCompleteForceWord_zero_right {κ : ℝ} {N : ℕ} (hD : LP.DistinctCompleteBelow.{u} κ N)
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (ρL : Fin nL → ℝ) (hF : IsOrderedForceWord xL xR) (hnL : nL < N) :
    LP.IsCompleteForceWord.{u} κ xL xR ρL (0 : Fin nR → ℝ) := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hsub := hE.compEmb ((RelEmbedding.refl (· ≤ ·) : Fin nL ↪o Fin nL)) (OrderEmbedding.ofIsEmpty : Fin 0 ↪o Fin nR)
    (fun i hi => absurd ⟨i, rfl⟩ hi) (fun _ _ => rfl)
  have hcount : (Finset.univ.image fun j => xL (((RelEmbedding.refl (· ≤ ·) : Fin nL ↪o Fin nL)) j)).card +
      (Finset.univ.image fun j : Fin 0 => xR ((OrderEmbedding.ofIsEmpty : Fin 0 ↪o Fin nR) j)).card < N := by
    have h1 := Finset.card_image_le (s := (Finset.univ : Finset (Fin nL)))
      (f := fun j => xL (((RelEmbedding.refl (· ≤ ·) : Fin nL ↪o Fin nL)) j))
    rw [Finset.card_univ, Fintype.card_fin] at h1
    simp only [Finset.univ_eq_empty, Finset.image_empty, Finset.card_empty, add_zero]
    omega
  exact LP.isCompleteForceWord_of_distinctCompleteBelow hD
    (hF.compEmb ((RelEmbedding.refl (· ≤ ·) : Fin nL ↪o Fin nL)) (OrderEmbedding.ofIsEmpty : Fin 0 ↪o Fin nR)) hcount
    P 𝓕 W _ _ B ζ hsub

/-- **Deleting the left group** (all left weights `0`), when `nR < N`. -/
theorem isCompleteForceWord_zero_left {κ : ℝ} {N : ℕ} (hD : LP.DistinctCompleteBelow.{u} κ N)
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (ρR : Fin nR → ℝ) (hF : IsOrderedForceWord xL xR) (hnR : nR < N) :
    LP.IsCompleteForceWord.{u} κ xL xR (0 : Fin nL → ℝ) ρR := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hsub := hE.compEmb (OrderEmbedding.ofIsEmpty : Fin 0 ↪o Fin nL) ((RelEmbedding.refl (· ≤ ·) : Fin nR ↪o Fin nR))
    (fun _ _ => rfl) (fun i hi => absurd ⟨i, rfl⟩ hi)
  have hcount : (Finset.univ.image fun j : Fin 0 => xL ((OrderEmbedding.ofIsEmpty : Fin 0 ↪o Fin nL) j)).card +
      (Finset.univ.image fun j => xR (((RelEmbedding.refl (· ≤ ·) : Fin nR ↪o Fin nR)) j)).card < N := by
    have h1 := Finset.card_image_le (s := (Finset.univ : Finset (Fin nR)))
      (f := fun j => xR (((RelEmbedding.refl (· ≤ ·) : Fin nR ↪o Fin nR)) j))
    rw [Finset.card_univ, Fintype.card_fin] at h1
    simp only [Finset.univ_eq_empty, Finset.image_empty, Finset.card_empty, zero_add]
    omega
  exact LP.isCompleteForceWord_of_distinctCompleteBelow hD
    (hF.compEmb (OrderEmbedding.ofIsEmpty : Fin 0 ↪o Fin nL) ((RelEmbedding.refl (· ≤ ·) : Fin nR ↪o Fin nR))) hcount
    P 𝓕 W _ _ B ζ hsub

/-! ### Aux. lemma 103: finite-time continuity -/

section FiniteTime

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The reduced word deleting the right group has the full trace event Wiener-almost surely at every separated
ordered start (the induction hypothesis, through Theorem 2.2's existence). -/
theorem ae_mem_lawSetS_zero_right (hκ : 0 < κ) (hex : ExistsEvolutionStatement) {N : ℕ}
    (hD : LP.DistinctCompleteBelow.{u} κ N) (ρL : Fin nL → ℝ) (hnL : nL < N)
    (s : (Fin nL → ℝ) × (Fin nR → ℝ)) (hs : SepStart s) (hord : IsOrderedForceWord s.1 s.2) :
    ∀ᵐ f ∂wienerPath, (s, enc f) ∈ lawSetS κ ρL (0 : Fin nR → ℝ) (fullTraceSet (nL := nL) (nR := nR)) := by
  obtain ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', hE'⟩ := hex hκ s.1 s.2 ρL 0 hord
  exact ae_mem_lawSetS_fullTraceSet hκ (isCompleteForceWord_zero_right hD ρL hord hnL) hs
    (ae_solvable_of_isIntegratedSLEEvolution hκ hs hE')

/-- The reduced word deleting the left group has the full trace event Wiener-almost surely. -/
theorem ae_mem_lawSetS_zero_left (hκ : 0 < κ) (hex : ExistsEvolutionStatement) {N : ℕ}
    (hD : LP.DistinctCompleteBelow.{u} κ N) (ρR : Fin nR → ℝ) (hnR : nR < N)
    (s : (Fin nL → ℝ) × (Fin nR → ℝ)) (hs : SepStart s) (hord : IsOrderedForceWord s.1 s.2) :
    ∀ᵐ f ∂wienerPath, (s, enc f) ∈ lawSetS κ (0 : Fin nL → ℝ) ρR (fullTraceSet (nL := nL) (nR := nR)) := by
  obtain ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', hE'⟩ := hex hκ s.1 s.2 0 ρR hord
  exact ae_mem_lawSetS_fullTraceSet hκ (isCompleteForceWord_zero_left hD ρR hord hnR) hs
    (ae_solvable_of_isIntegratedSLEEvolution hκ hs hE')

/-- **Aux. lemma 103, finite-time continuity** (Specification §7.3, p. 349, `source/spec/p337-384.md` L288–L305):
for `κ > 0`, if every force word with fewer than `N` marks is complete (`LP.DistinctCompleteBelow κ N`) and each side
has fewer than `N` marks, then almost surely the driver of an evolution of an ordered word has a continuous
generating trace on `[0, ζ]`, the finite continuation threshold included (on `[0, ∞)` when `ζ = ∞`; no transience is
asserted). The start is separated (`D_0 > 0`), or an initial trace is given (the case `D_0 = 0`, the last paragraph of
the proof). Inputs: Theorem 2.2's existence (`ExistsEvolutionStatement`), used for the words with one side deleted. -/
theorem ae_isGeneratingTrace_lifetime [IsProbabilityMeasure P] (hκ : 0 < κ) (hex : ExistsEvolutionStatement)
    {N : ℕ} (hD : LP.DistinctCompleteBelow.{u} κ N)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hF : IsOrderedForceWord xL xR)
    (hnL : nL < N) (hnR : nR < N)
    (hstart : (∀ i j, xL i < xR j) ∨
      ∀ᵐ ω ∂P, ζ ω = 0 ∨ ∃ ε : ℝ≥0, 0 < ε ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ε η) :
    ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η := by
  have hb := ae_band_rational hκ hE (ae_mem_lawSetS_zero_right hκ hex hD ρL hnL)
    (ae_mem_lawSetS_zero_left hκ hex hD ρR hnR)
  have hst : ∀ᵐ ω ∂P, ζ ω = 0 ∨ ((∀ i j, xL i < xR j) ∨
      ∃ ε : ℝ≥0, 0 < ε ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ε η) := by
    rcases hstart with hsep | hae
    · exact ae_of_all _ fun _ => Or.inr (Or.inl hsep)
    · filter_upwards [hae] with ω h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  filter_upwards [hb, hE.2.2.2.2, hE.ae_tendsto_threshold hκ, hst] with ω hbω hp hl hstω
  rcases hstω with h0 | hstω
  · refine ⟨fun _ => 0, rfl, continuousOn_const, fun t ht => ?_⟩
    rw [h0] at ht
    exact absurd ht (not_lt.2 bot_le)
  refine exists_isGeneratingTrace_of_bandTraces hp hF hbω hstω fun T hT hTζ => ?_
  obtain ⟨w₀, vL₀, vR₀, htend, -⟩ := hl T hT hTζ
  exact ⟨w₀, vL₀, vR₀, htend⟩

end FiniteTime

/-! ### The first merger of two same-side groups -/

/-- Two marks of the same side are at the same position at time `s`. -/
def SameSideMeet (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (s : ℝ≥0) : Prop :=
  (∃ i i', i ≠ i' ∧ vL i s = vL i' s) ∨ ∃ j j', j ≠ j' ∧ vR j s = vR j' s

/-- **The merger time** of Aux. lemma 113 (p. 369: "when two distinct groups on the same side have been swallowed
and merge"), capped by the lifetime. -/
def mergeTime (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : ℝ≥0∞ :=
  min (hitTime (SameSideMeet vL vR) ζ) ζ

theorem mergeTime_le (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : mergeTime vL vR ζ ≤ ζ :=
  min_le_right _ _

theorem card_lt_of_sameSideMeet {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {t : ℝ≥0}
    (h : SameSideMeet vL vR t) :
    (Finset.univ.image fun i => vL i t - w t).card + (Finset.univ.image fun j => vR j t - w t).card <
      nL + nR := by
  have hL := Finset.card_image_le (s := (Finset.univ : Finset (Fin nL))) (f := fun i => vL i t - w t)
  have hR := Finset.card_image_le (s := (Finset.univ : Finset (Fin nR))) (f := fun j => vR j t - w t)
  rw [Finset.card_univ, Fintype.card_fin] at hL hR
  rcases h with ⟨i, i', hii', he⟩ | ⟨j, j', hjj', he⟩
  · have hne : (Finset.univ.image fun i => vL i t - w t).card ≠ nL := by
      intro heq
      have hinj := Finset.card_image_iff.1 (heq.trans (by rw [Finset.card_univ, Fintype.card_fin]))
      exact hii' (hinj (Finset.mem_coe.2 (Finset.mem_univ i)) (Finset.mem_coe.2 (Finset.mem_univ i'))
        (by simp only [he]))
    omega
  · have hne : (Finset.univ.image fun j => vR j t - w t).card ≠ nR := by
      intro heq
      have hinj := Finset.card_image_iff.1 (heq.trans (by rw [Finset.card_univ, Fintype.card_fin]))
      exact hjj' (hinj (Finset.mem_coe.2 (Finset.mem_univ j)) (Finset.mem_coe.2 (Finset.mem_univ j'))
        (by simp only [he]))
    omega

section Merge

variable {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **At the merger time (before the lifetime) two same-side marks coincide**: otherwise all same-side pairs stay
apart on a neighbourhood, and no rational time there is a hit. -/
theorem sameSideMeet_mergeTime (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (hlt : mergeTime vL vR ζ < ζ) : SameSideMeet vL vR (mergeTime vL vR ζ).toNNReal := by
  have hf := hp.isForcePath
  set τ := mergeTime vL vR ζ with hτ
  have hτhit : τ = hitTime (SameSideMeet vL vR) ζ := by
    rcases min_choice (hitTime (SameSideMeet vL vR) ζ) ζ with h | h
    · exact h
    · exact absurd (hτ.trans h) hlt.ne
  have hfin : τ ≠ ⊤ := ne_top_of_lt hlt
  set t := τ.toNNReal with ht
  have htτ : (t : ℝ≥0∞) = τ := ENNReal.coe_toNNReal hfin
  have htζ : (t : ℝ≥0∞) < ζ := by rw [htτ]; exact hlt
  by_contra hno
  have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hmem : {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} ∈ 𝓝 t := hopen.mem_nhds htζ
  have hca : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {s | (s : ℝ≥0∞) < ζ} → ContinuousAt f t :=
    fun hf' => hf'.continuousAt hmem
  have hL : ∀ᶠ s in 𝓝 t, ∀ i i' : Fin nL, i ≠ i' → vL i s ≠ vL i' s := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun i' => ?_
    by_cases hii : i = i'
    · exact Filter.Eventually.of_forall fun _ h => absurd hii h
    · have hne : vL i t - vL i' t ≠ 0 := fun h =>
        hno (Or.inl ⟨i, i', hii, sub_eq_zero.1 h⟩)
      filter_upwards [(hca ((hf.continuousOn_vL i).sub (hf.continuousOn_vL i'))).eventually
        (isOpen_ne.mem_nhds hne)] with s hs _ he
      exact hs (sub_eq_zero.2 he)
  have hR : ∀ᶠ s in 𝓝 t, ∀ j j' : Fin nR, j ≠ j' → vR j s ≠ vR j' s := by
    refine Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun j' => ?_
    by_cases hjj : j = j'
    · exact Filter.Eventually.of_forall fun _ h => absurd hjj h
    · have hne : vR j t - vR j' t ≠ 0 := fun h =>
        hno (Or.inr ⟨j, j', hjj, sub_eq_zero.1 h⟩)
      filter_upwards [(hca ((hf.continuousOn_vR j).sub (hf.continuousOn_vR j'))).eventually
        (isOpen_ne.mem_nhds hne)] with s hs _ he
      exact hs (sub_eq_zero.2 he)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hL.and hR)
  set e : ℝ≥0 := Real.toNNReal (ε / 2) with he
  have he0 : (e : ℝ) = ε / 2 := Real.coe_toNNReal _ (by positivity)
  have hlt' : hitTime (SameSideMeet vL vR) ζ < ((t + e : ℝ≥0) : ℝ≥0∞) := by
    rw [← hτhit, ← htτ]
    exact_mod_cast lt_add_of_pos_right t (by rw [← NNReal.coe_pos, he0]; positivity)
  obtain ⟨r, hr1, hr2, hr3⟩ := hitTime_lt_iff.1 hlt'
  have htr : t ≤ Real.toNNReal r := by
    have : (t : ℝ≥0∞) ≤ (Real.toNNReal r : ℝ≥0) := by rw [htτ, hτhit]; exact hitTime_le hr2 hr3
    exact_mod_cast this
  have hd : dist (Real.toNNReal r) t < ε := by
    have h1 : Real.toNNReal r < t + e := by exact_mod_cast hr1
    have h2 := NNReal.coe_lt_coe.2 h1
    have h3 := NNReal.coe_le_coe.2 htr
    rw [NNReal.coe_add, he0] at h2
    rw [NNReal.dist_eq, abs_lt]
    constructor <;> linarith
  obtain ⟨hbL, hbR⟩ := hball hd
  rcases hr3 with ⟨i, i', hii, he'⟩ | ⟨j, j', hjj, he'⟩
  · exact hbL i i' hii he'
  · exact hbR j j' hjj he'

/-- **Merged groups stay merged** (`Sec2.UpTo.vR_eq_of_eq`, and its reflection for the left side). -/
theorem sameSideMeet_of_le (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {s t : ℝ≥0} (hst : s ≤ t)
    (ht : (t : ℝ≥0∞) < ζ) (h : SameSideMeet vL vR s) : SameSideMeet vL vR t := by
  have hu := hp.isSLEPathUpTo le_rfl
  rcases h with ⟨i, i', hii, he⟩ | ⟨j, j', hjj, he⟩
  · refine Or.inl ⟨i, i', hii, ?_⟩
    have := UpTo.vR_eq_of_eq hu.reflect ht (j := i) (k := i') (show -vL i s = -vL i' s by rw [he])
      ⟨hst, le_rfl⟩
    exact neg_inj.1 this
  · exact Or.inr ⟨j, j', hjj, UpTo.vR_eq_of_eq hu ht he ⟨hst, le_rfl⟩⟩

/-- **No merger at a rational time: no merger at all** (before an infinite lifetime). -/
theorem not_sameSideMeet_of_hitTime_eq_top (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ⊤)
    (h : hitTime (SameSideMeet vL vR) ⊤ = ⊤) (t : ℝ≥0) : ¬ SameSideMeet vL vR t := by
  intro hm
  obtain ⟨q, hq1, -⟩ := exists_rat_btwn (show (t : ℝ) < t + 1 by linarith)
  have hq0 : (0 : ℝ) ≤ q := (NNReal.coe_nonneg t).trans hq1.le
  have htq : t ≤ Real.toNNReal q := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]; exact hq1.le
  have hm' := sameSideMeet_of_le hp htq ENNReal.coe_lt_top hm
  have := hitTime_le (p := SameSideMeet vL vR) (ζ := ⊤) ENNReal.coe_lt_top hm'
  rw [h] at this
  exact ENNReal.coe_ne_top (top_le_iff.1 this)

end Merge

section MergeProcess

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

theorem measurableSet_lt_and_eq_of_adaptedBefore {X Y : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓕 ζ X)
    (hY : AdaptedBefore 𝓕 ζ Y) (t : ℝ≥0) :
    MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω = Y t ω} := by
  have e : {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω = Y t ω} =
      {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω - Y t ω ≤ 0} ∩ {ω | (t : ℝ≥0∞) < ζ ω ∧ Y t ω - X t ω ≤ 0} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, by rw [h2, sub_self]⟩, ⟨h1, by rw [h2, sub_self]⟩⟩
    · rintro ⟨⟨h1, h2⟩, ⟨-, h3⟩⟩
      exact ⟨h1, by linarith⟩
  rw [e]
  exact (measurableSet_lt_and_le_of_adaptedBefore hX hY t 0).inter
    (measurableSet_lt_and_le_of_adaptedBefore hY hX t 0)

/-- The merger time is a stopping time of the usual augmentation. -/
theorem isStoppingTime_mergeTime (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    IsStoppingTime (usualAugmentation 𝓕 P) fun ω =>
      (mergeTime (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω) : WithTop ℝ≥0) := by
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have h1 : IsStoppingTime (usualAugmentation 𝓕 P) fun ω =>
      (hitTime (SameSideMeet (fun i t => VL i t ω) (fun j t => VR j t ω)) (ζ ω) : WithTop ℝ≥0) := by
    refine isStoppingTime_hitTime fun s => ?_
    have e : {ω | (s : ℝ≥0∞) < ζ ω ∧ SameSideMeet (fun i t => VL i t ω) (fun j t => VR j t ω) s} =
        (⋃ i, ⋃ i', ⋃ (_ : i ≠ i'), {ω | (s : ℝ≥0∞) < ζ ω ∧ VL i s ω = VL i' s ω}) ∪
          ⋃ j, ⋃ j', ⋃ (_ : j ≠ j'), {ω | (s : ℝ≥0∞) < ζ ω ∧ VR j s ω = VR j' s ω} := by
      ext ω
      simp only [SameSideMeet, mem_ofPred_eq, mem_union, mem_iUnion, exists_prop]
      constructor
      · rintro ⟨h0, ⟨i, i', hii, he⟩ | ⟨j, j', hjj, he⟩⟩
        · exact Or.inl ⟨i, i', hii, h0, he⟩
        · exact Or.inr ⟨j, j', hjj, h0, he⟩
      · rintro (⟨i, i', hii, h0, he⟩ | ⟨j, j', hjj, h0, he⟩)
        · exact ⟨h0, Or.inl ⟨i, i', hii, he⟩⟩
        · exact ⟨h0, Or.inr ⟨j, j', hjj, he⟩⟩
    rw [e]
    exact (MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun i' => MeasurableSet.iUnion fun _ =>
      measurableSet_lt_and_eq_of_adaptedBefore (hE𝓖.2.2.1 i) (hE𝓖.2.2.1 i') s).union
      (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun j' => MeasurableSet.iUnion fun _ =>
        measurableSet_lt_and_eq_of_adaptedBefore (hE𝓖.2.2.2.1 j) (hE𝓖.2.2.2.1 j') s)
  have h2 := h1.min (Ito.isStoppingTime_lifetime hE𝓖.2.1)
  exact h2

/-- **The count prefix of Aux. lemma 113 from finite-time continuity and transience without merger.** For an
evolution whose driver almost surely has a continuous generating trace on `[0, ζ]`, and which is almost surely
transient on the event that the lifetime is infinite and no two same-side marks ever merge, the merger time
`τ = mergeTime` is a stopping time of the usual augmentation with the conclusion of `HasCountPrefix`. -/
theorem exists_countPrefix [IsProbabilityMeasure P]
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (htrace : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η)
    (htrans : ∀ᵐ ω ∂P, ζ ω = ⊤ → (∀ t, ¬ SameSideMeet (fun i t => VL i t ω) (fun j t => VR j t ω) t) →
      ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → Tendsto (fun t => ‖η t‖) atTop atTop) :
    ∃ τ : Ω → ℝ≥0∞, IsStoppingTime (usualAugmentation 𝓕 P) (fun ω => (τ ω : WithTop ℝ≥0)) ∧
      ∀ᵐ ω ∂P, τ ω ≤ ζ ω ∧
        (τ ω < ζ ω →
          (Finset.univ.image fun i => VL i (τ ω).toNNReal ω - W (τ ω).toNNReal ω).card +
            (Finset.univ.image fun j => VR j (τ ω).toNNReal ω - W (τ ω).toNNReal ω).card < nL + nR) ∧
        ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (τ ω) η ∧
          (τ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) ∧
          (τ ω < ζ ω → IsGeneratingTraceIcc (fun t => W t ω) (τ ω).toNNReal η) := by
  refine ⟨fun ω => mergeTime (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω), isStoppingTime_mergeTime hE, ?_⟩
  filter_upwards [htrace, htrans, hE.2.2.2.2] with ω ⟨η, hη⟩ htr hp
  have hτζ := mergeTime_le (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω)
  refine ⟨hτζ, fun hlt => card_lt_of_sameSideMeet (w := fun t => W t ω) (sameSideMeet_mergeTime hp hlt), η,
    hη.mono_horizon hτζ, fun htop => ?_, fun hlt => ?_⟩
  · have hζ : ζ ω = ⊤ := top_le_iff.1 (htop ▸ hτζ)
    have hhit : hitTime (SameSideMeet (fun i t => VL i t ω) (fun j t => VR j t ω)) ⊤ = ⊤ := by
      have h1 : mergeTime (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω) ≤
          hitTime (SameSideMeet (fun i t => VL i t ω) (fun j t => VR j t ω)) (ζ ω) := min_le_left _ _
      rw [htop, hζ] at h1
      exact top_le_iff.1 h1
    rw [hζ] at hp hη
    exact htr hζ (not_sameSideMeet_of_hitTime_eq_top hp hhit) η hη
  · have hfin := ne_top_of_lt hlt
    have hσ : (((mergeTime (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω)).toNNReal : ℝ≥0) : ℝ≥0∞) <
        ζ ω := by rw [ENNReal.coe_toNNReal hfin]; exact hlt
    exact IsGeneratingTrace.isGeneratingTraceIcc hη hp.isForcePath.continuousOn_w hp.1 hσ

end MergeProcess

/-! ### Aux. lemma 113: the prefix part from finite-time continuity -/

/-- **Named input (Aux. lemma 103, the case `D_0 = 0`): an initial trace from the two seed groups** (Specification
p. 350, `source/spec/p337-384.md` L305: "If `D_0 = 0`, both nearest groups begin at the seed. An inadmissible
initial group gives an immediate threshold and requires no continuation. Otherwise retain those two admissible seed
groups and delete all other initially separated marks up to a sufficiently small gap cutoff, stopped also at
physical time one. Their drift is bounded, and the assumed seed two-force-point result gives a continuous initial
prefix through this positive stopping time, unless termination occurs earlier."). Under the two-seed premise, an
evolution of an ordered word with a left and a right mark at the seed almost surely has lifetime `0` or a continuous
generating trace on some `[0, ε]`, `ε > 0`. (The band transfer `ContinuityProb4Band` needs a separated start, at
which solutions are pathwise unique; the two-seed entrance is not covered by it.) -/
def SeedEntranceStatement (κ : ℝ) : Prop :=
  LP.TwoSeedComplete.{u} κ →
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR → ¬ (∀ i j, xL i < xR j) →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
      ∀ᵐ ω ∂P, ζ ω = 0 ∨ ∃ ε : ℝ≥0, 0 < ε ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ε η

/-- **Named input: transience in Aux. lemma 113 when no two groups merge** (Specification pp. 370–372,
`source/spec/p337-384.md` L692–L740: "It remains to treat `τ = ∞`": the finite angular clock (Aux. lemma 102) and
bands with bounded-energy Girsanov when a side total is at most `−2`; the moving-midpoint trials with the local GFF
comparison of Aux. lemmas 108–111 and Lévy's upward theorem (TI15.1; the terminal trial principle (D.3.4) of
Astra's follow-up note, lines 2140–2153, ruling R38) when both exceed `d = κ/2 − 4`). For `0 < κ < 4`,
`N ≥ 3`, under the smaller-count hypothesis, for every evolution of a distinct-position word with `N` marks, at least
one on each side: almost surely, if the lifetime is infinite and no two same-side marks ever merge, every continuous
generating trace on `[0, ∞)` tends to infinity. -/
def Aux113TransienceStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ N : ℕ, 3 ≤ N →
    (∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      LP.IsDistinctForceWord xL xR → nL + nR ≤ N - 1 → LP.IsCompleteForceWord.{u} κ xL xR ρL ρR) →
    ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      LP.IsDistinctForceWord xL xR → nL + nR = N → 1 ≤ nL → 1 ≤ nR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
      ∀ᵐ ω ∂P, ζ ω = ⊤ → (∀ t, ¬ SameSideMeet (fun i t => VL i t ω) (fun j t => VR j t ω) t) →
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → Tendsto (fun t => ‖η t‖) atTop atTop

/-- **Named input: transience in Aux. lemma 113, LP10's form** (every `κ > 0`, with the two-seed premise and the
alternatives (TI13.1)). -/
def LPAux113TransienceStatement (κ : ℝ) : Prop :=
  ∀ N : ℕ, 3 ≤ N → LP.DistinctCompleteBelow.{u} κ N → LP.TwoSeedComplete.{u} κ →
    ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      LP.IsDistinctForceWord xL xR → nL + nR = N → 0 < nL → 0 < nR →
      ((∑ i, ρL i) ≤ -2 ∨ (∑ i, ρR i) ≤ -2 ∨ (κ / 2 - 4 < ∑ i, ρL i ∧ κ / 2 - 4 < ∑ i, ρR i)) →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
      ∀ᵐ ω ∂P, ζ ω = ⊤ → (∀ t, ¬ SameSideMeet (fun i t => VL i t ω) (fun j t => VR j t ω) t) →
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → Tendsto (fun t => ‖η t‖) atTop atTop

/-- The two-seed premise for `0 < κ < 4` from Proposition 7.3's named statement. -/
theorem twoSeedComplete_of_prop73 (h73 : Prop73TraceStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    LP.TwoSeedComplete.{u} κ := fun rL rR h1 h2 =>
  h73 κ hκ hκ4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) (fun _ => rfl) (fun _ => rfl)
    (fun _ => h1) (fun _ => h2)

/-- **`Aux113PrefixStatement` from Theorem 2.2's existence, the seed entrance, and transience without merger.**
The finite-time part (Aux. lemma 103 through the merger time) is `ae_isGeneratingTrace_lifetime`. -/
theorem aux113PrefixStatement_of_inputs (hex : ExistsEvolutionStatement) (h73 : Prop73TraceStatement.{u})
    (hseed : ∀ κ : ℝ, 0 < κ → κ < 4 → SeedEntranceStatement.{u} κ) (htr : Aux113TransienceStatement.{u}) :
    Aux113PrefixStatement.{u} := by
  intro κ hκ hκ4 N hN hbelow nL nR xL xR ρL ρR hd hsum hL hR Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hD : LP.DistinctCompleteBelow.{u} κ N := distinctCompleteBelow_of_le (by omega) hbelow
  have hstart : (∀ i j, xL i < xR j) ∨ ∀ᵐ ω ∂P, ζ ω = 0 ∨
      ∃ ε : ℝ≥0, 0 < ε ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ε η := by
    by_cases hsep : ∀ i j, xL i < xR j
    · exact Or.inl hsep
    · exact Or.inr (hseed κ hκ hκ4 (twoSeedComplete_of_prop73 h73 hκ hκ4) xL xR ρL ρR hd.1 hsep P 𝓕 W VL VR
        B ζ hE)
  have htrace := ae_isGeneratingTrace_lifetime hκ hex hD hE hd.1 (by omega) (by omega) hstart
  obtain ⟨τ, hτ, hae⟩ := exists_countPrefix hE htrace
    (htr κ hκ hκ4 N hN hbelow xL xR ρL ρR hd hsum hL hR P 𝓕 W VL VR B ζ hE)
  rw [← hsum]
  exact ⟨τ, hτ, hae⟩

/-- **`LPAux113PrefixStatement κ` from Theorem 2.2's existence, the seed entrance, and transience without merger**
(every `κ > 0`). -/
theorem lpAux113PrefixStatement_of_inputs {κ : ℝ} (hκ : 0 < κ) (hex : ExistsEvolutionStatement)
    (hseed : SeedEntranceStatement.{u} κ) (htr : LPAux113TransienceStatement.{u} κ) :
    LPAux113PrefixStatement.{u} κ := by
  intro N hN hD h2 nL nR xL xR ρL ρR hd hsum hL hR hTI Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hstart : (∀ i j, xL i < xR j) ∨ ∀ᵐ ω ∂P, ζ ω = 0 ∨
      ∃ ε : ℝ≥0, 0 < ε ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ε η := by
    by_cases hsep : ∀ i j, xL i < xR j
    · exact Or.inl hsep
    · exact Or.inr (hseed h2 xL xR ρL ρR hd.1 hsep P 𝓕 W VL VR B ζ hE)
  have htrace := ae_isGeneratingTrace_lifetime hκ hex hD hE hd.1 (by omega) (by omega) hstart
  obtain ⟨τ, hτ, hae⟩ := exists_countPrefix hE htrace
    (htr N hN hD h2 xL xR ρL ρR hd hsum hL hR hTI P 𝓕 W VL VR B ζ hE)
  rw [← hsum]
  exact ⟨τ, hτ, hae⟩

end Sec7

end InteractingSLE
