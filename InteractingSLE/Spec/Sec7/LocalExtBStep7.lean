/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtBGraph
import InteractingSLE.Spec.Sec7.LocalExtACutoff
import InteractingSLE.Spec.Sec7.TwoForceMainDetermine

/-!
# Aux. lemma 55, last paragraphs: the stopped history at the seed is determined by the field

Packet PROVE-LOCEXT-B (step 7 of the split in `planning/handoffs/PROVE-AUX52-55.md`). Specification p. 250:

"*Extending the stopped reference coupling.* Fix one full two-seed reference coupling with weights `(r_−, r_+)` at
`0⁻, 0⁺`, provided by the existence theorem. … Aux. lemma 54 therefore extends `(h₀, W_{·∧S}, V_{·∧S})` to a full
reference pair, using a single disintegration of this fixed coupling. … By the assumed two-seed input the full
reference history is determined by `h₀`. Its determining function is the same for every such reference coupling. …
Its stopped history through `S` is in fact determined by … Hence the history equals a measurable function … The
measures in (HL3) are equivalent, so this identity holds for the original coupling as well."

* `aemeasurable_completedState_apply`, `aemeasurable_stoppedHistory`: the stopped history of the completed driving
  state at a measurable time `σ ≤ ζ` is almost everywhere measurable;
* `isAEDeterminedBy_of_map_fst`: a determination on an extension `Ω × C` of `(Ω, Q)` (first marginal `Q`) descends to
  `(Ω, Q)`;
* `ReferenceExtensionStatement κ` (**named input**: (HL1)–(HL9) of Aux. 55 with Aux. 54, steps 1–6 of the split): for
  every coupling with an admissible seed there are an equivalent measure `Q`, the measurable deterministic recoding
  `T` of (HL8) (`h₀ = h + f − q`) and a full two-seed reference coupling on an extension `Ω × C` of `(Ω, Q)` whose
  field is `T(h)`, whose stopped two-seed history at the local stop determines the original stopped history;
* **`isAEDeterminedBy_stoppedHistory_capStop`**: under the two-seed input and `ReferenceExtensionStatement`, the
  history of every coupling stopped at the local stop of Aux. 55 is a Borel function of the field (with
  `twoSeed_exists_stoppedGraph`, the common stopped graph).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 Determination

/-! ### Almost everywhere measurability of stopped histories -/

section AEMeas

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The killed driving state at a fixed time, with the junk value of `completedState` after the lifetime. -/
def killedStateAt (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (t : ℝ≥0) (ω : Ω) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
  if (t : ℝ≥0∞) < ζ ω then drivingState W VL VR t ω
  else limUnder (𝓝[<] (0 : ℝ≥0)) fun _ => (0 : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))

theorem measurable_killedStateAt (hX : IsMeasurableKilledDriving W VL VR ζ) (t : ℝ≥0) :
    Measurable (killedStateAt W VL VR ζ t) := by
  classical
  intro A hA
  have hlt : MeasurableSet {ω | (t : ℝ≥0∞) < ζ ω} := by
    have := hX t univ MeasurableSet.univ
    simpa only [mem_univ, and_true] using this
  have e : killedStateAt W VL VR ζ t ⁻¹' A = {ω | (t : ℝ≥0∞) < ζ ω ∧ drivingState W VL VR t ω ∈ A} ∪
      ({ω | (t : ℝ≥0∞) < ζ ω}ᶜ ∩ {_ω | (limUnder (𝓝[<] (0 : ℝ≥0)) fun _ =>
        (0 : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) ∈ A}) := by
    ext ω
    simp only [mem_preimage, killedStateAt, mem_union, mem_ofPred_eq, mem_inter_iff, mem_compl_iff]
    by_cases h : (t : ℝ≥0∞) < ζ ω
    · simp [h]
    · simp [h]
  rw [e]
  exact (hX t A hA).union (hlt.compl.inter (MeasurableSet.const _))

/-- **The completed state at a measurable time `s ≤ ζ` is almost everywhere measurable.** -/
theorem aemeasurable_completedState_apply (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => completedState W VL VR ζ t ω)
      {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ (ζ ω : WithTop ℝ≥0)})
    {s : Ω → ℝ≥0} (hs : Measurable s) (hsζ : ∀ᵐ ω ∂P, (s ω : ℝ≥0∞) ≤ ζ ω) :
    AEMeasurable (fun ω => completedState W VL VR ζ (s ω) ω) P := by
  have hY : ∀ n, Measurable fun ω => killedStateAt W VL VR ζ (lowApprox n (s ω)) ω := by
    intro n
    have hk : Measurable fun q : ℕ × Ω => killedStateAt W VL VR ζ ((q.1 : ℝ≥0) / 2 ^ n) q.2 :=
      measurable_from_prod_countable_right fun k => measurable_killedStateAt hX ((k : ℝ≥0) / 2 ^ n)
    have e : (fun ω => killedStateAt W VL VR ζ (lowApprox n (s ω)) ω) =
        (fun q : ℕ × Ω => killedStateAt W VL VR ζ ((q.1 : ℝ≥0) / 2 ^ n) q.2) ∘
          fun ω => (lowIdx n (s ω), ω) := rfl
    rw [e]
    exact hk.comp (((measurable_lowIdx n).comp hs).prodMk measurable_id)
  refine aemeasurable_of_tendsto_metrizable_ae' (fun n => (hY n).aemeasurable) ?_
  filter_upwards [hcont, hsζ] with ω hc hsle
  rcases eq_zero_or_pos (s ω) with hs0 | hs0
  · have hconst : ∀ n, killedStateAt W VL VR ζ (lowApprox n (s ω)) ω =
        completedState W VL VR ζ (s ω) ω := by
      intro n
      rw [hs0, lowApprox_zero, killedStateAt]
      by_cases hζ : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω
      · rw [ite_eq_left hζ, completedState, ite_eq_left hζ]
      · rw [ite_eq_right hζ, completedState_zero_of_not_lt hζ]
    simp_rw [hconst]
    exact tendsto_const_nhds
  · have hlt : ∀ n, ((lowApprox n (s ω) : ℝ≥0) : ℝ≥0∞) < ζ ω := fun n =>
      lt_of_lt_of_le (ENNReal.coe_lt_coe.2 (lowApprox_lt hs0 n)) hsle
    have he : ∀ n, killedStateAt W VL VR ζ (lowApprox n (s ω)) ω =
        completedState W VL VR ζ (lowApprox n (s ω)) ω := by
      intro n
      rw [killedStateAt, ite_eq_left (hlt n), completedState, ite_eq_left (hlt n)]
    simp_rw [he]
    have hmem : ∀ n, lowApprox n (s ω) ∈
        {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ (ζ ω : WithTop ℝ≥0)} := fun n => (hlt n).le
    exact (hc (s ω) hsle).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨tendsto_lowApprox _, Eventually.of_forall hmem⟩)

/-- **The stopped history of the completed state at a measurable time `σ ≤ ζ` is almost everywhere measurable.** -/
theorem aemeasurable_stoppedHistory (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => completedState W VL VR ζ t ω)
      {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ (ζ ω : WithTop ℝ≥0)})
    {σ : Ω → WithTop ℝ≥0} (hσ : Measurable σ) (hσζ : ∀ ω, σ ω ≤ (ζ ω : WithTop ℝ≥0)) :
    AEMeasurable (stoppedHistory (completedState W VL VR ζ) σ) P := by
  refine hσ.aemeasurable.prodMk (AEMeasurable.of_eval fun q => ?_)
  exact aemeasurable_completedState_apply hX hcont
    ((measurable_const.min (WithTop.measurable_untopD (q : ℝ≥0))).comp hσ)
    (ae_of_all _ fun ω => (stopAt_le σ q ω).trans (hσζ ω))

end AEMeas

/-! ### Determination descends from an extension -/

section Descend

/-- Equality of two measurable maps into a product of spaces with measurable equality is a measurable event. -/
theorem measurableSet_eq_prod {α β₁ β₂ : Type*} [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
    [MeasurableEq β₁] [MeasurableEq β₂] {f g : α → β₁ × β₂} (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {x | f x = g x} := by
  have e : {x | f x = g x} = {x | (f x).1 = (g x).1} ∩ {x | (f x).2 = (g x).2} := by
    ext x; simp only [mem_ofPred_eq, mem_inter_iff, Prod.ext_iff]
  rw [e]
  exact (measurableSet_eq_fun hf.fst hg.fst).inter (measurableSet_eq_fun hf.snd hg.snd)

/-- **A determination on an extension descends.** Let `E` be a measure on `Ω × C` with first marginal `Q`. If
`Y ∘ fst` is `E`-almost surely a Borel function of `H ∘ fst`, and `Y` is `Q`-almost everywhere measurable, then `Y` is
`Q`-almost surely the same Borel function of `H`. -/
theorem isAEDeterminedBy_of_map_fst {Ω C γ β₁ β₂ : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace C]
    [MeasurableSpace γ] [MeasurableSpace β₁] [MeasurableSpace β₂] [MeasurableEq β₁] [MeasurableEq β₂]
    {E : Measure (Ω × C)} {Q : Measure Ω} (hEQ : E.map Prod.fst = Q) {H : Ω → γ} (hH : Measurable H)
    {Y : Ω → β₁ × β₂} (hY : AEMeasurable Y Q)
    (hdet : IsAEDeterminedBy E (fun p => H p.1) fun p => Y p.1) : IsAEDeterminedBy Q H Y := by
  obtain ⟨g, hg, hYg⟩ := hdet
  refine ⟨g, hg, ?_⟩
  have hA : MeasurableSet {ω | hY.mk Y ω = g (H ω)} :=
    measurableSet_eq_prod hY.measurable_mk (hg.comp hH)
  have hYE : ∀ᵐ p ∂E, Y p.1 = hY.mk Y p.1 := by
    have h1 : ∀ᵐ ω ∂(E.map Prod.fst), Y ω = hY.mk Y ω := by rw [hEQ]; exact hY.ae_eq_mk
    exact ae_of_ae_map measurable_fst.aemeasurable h1
  have hE : ∀ᵐ p ∂E, p.1 ∈ {ω | hY.mk Y ω = g (H ω)} := by
    filter_upwards [hYg, hYE] with p h1 h2
    show hY.mk Y p.1 = g (H p.1)
    rw [← h2]; exact h1
  have hQ' : ∀ᵐ ω ∂(E.map Prod.fst), ω ∈ {ω | hY.mk Y ω = g (H ω)} :=
    (ae_map_iff measurable_fst.aemeasurable hA).2 hE
  have hQ : ∀ᵐ ω ∂Q, ω ∈ {ω | hY.mk Y ω = g (H ω)} := hEQ ▸ hQ'
  filter_upwards [hQ, hY.ae_eq_mk] with ω h1 h2
  rw [h2]; exact h1

end Descend

/-- **A determination on an extension descends** (`H` almost everywhere measurable). -/
theorem isAEDeterminedBy_of_map_fst' {Ω C γ β₁ β₂ : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace C]
    [MeasurableSpace γ] [MeasurableSpace β₁] [MeasurableSpace β₂] [MeasurableEq β₁] [MeasurableEq β₂]
    {E : Measure (Ω × C)} {Q : Measure Ω} (hEQ : E.map Prod.fst = Q) {H : Ω → γ} (hH : AEMeasurable H Q)
    {Y : Ω → β₁ × β₂} (hY : AEMeasurable Y Q)
    (hdet : IsAEDeterminedBy E (fun p => H p.1) fun p => Y p.1) : IsAEDeterminedBy Q H Y := by
  obtain ⟨g, hg, hYg⟩ := hdet
  have hHE : ∀ᵐ p ∂E, H p.1 = hH.mk H p.1 := by
    have h1 : ∀ᵐ ω ∂(E.map Prod.fst), H ω = hH.mk H ω := by rw [hEQ]; exact hH.ae_eq_mk
    exact ae_of_ae_map measurable_fst.aemeasurable h1
  have hdet' : IsAEDeterminedBy E (fun p => hH.mk H p.1) fun p => Y p.1 := by
    refine ⟨g, hg, ?_⟩
    filter_upwards [hYg, hHE] with p h1 h2
    rw [h1, h2]
  obtain ⟨g', hg', hYg'⟩ := isAEDeterminedBy_of_map_fst hEQ hH.measurable_mk hY hdet'
  refine ⟨g', hg', ?_⟩
  filter_upwards [hYg', hH.ae_eq_mk] with ω h1 h2
  rw [h1, h2]

/-! ### The extended reference pair -/

/-- The stopped histories of the completed driving state of a word with `nL` left and `nR` right marks. -/
abbrev DrivingHist (nL nR : ℕ) : Type := WithTop ℝ≥0 × (ℚ≥0 → ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))

/-- The total weight of the left seed group (the left marks started at `0`; `0` if there is none). -/
def seedSumL {nL : ℕ} (xL ρL : Fin nL → ℝ) : ℝ := ∑ i, seedWtL xL ρL i

/-- The total weight of the right seed group. -/
def seedSumR {nR : ℕ} (xR ρR : Fin nR → ℝ) : ℝ := ∑ i, seedWtR xR ρR i

theorem seedSumL_eq {nL : ℕ} (xL ρL : Fin nL → ℝ) :
    seedSumL xL ρL = ∑ i ∈ Finset.univ.filter (fun i => xL i = 0), ρL i := by
  rw [seedSumL, Finset.sum_filter]
  rfl

theorem seedSumR_eq {nR : ℕ} (xR ρR : Fin nR → ℝ) :
    seedSumR xR ρR = ∑ i ∈ Finset.univ.filter (fun i => xR i = 0), ρR i := by
  rw [seedSumR, Finset.sum_filter]
  rfl

/-- An admissible seed has seed weights `> −2` (Aux. 55, p. 247: "The only possible seed collisions have weights
`r_−, r_+ > −2`"). -/
theorem seedSum_gt_of_not_thresholdCondition {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) : -2 < seedSumL xL ρL ∧ -2 < seedSumR xR ρR := by
  unfold ForceWord.ThresholdCondition at hseed
  rw [not_or, not_le, not_le] at hseed
  rw [seedSumL_eq, seedSumR_eq]
  exact hseed

/-- **The extended reference pair** (Aux. lemma 55, (HL8)–(HL9), with Aux. lemma 54; specification pp. 246–250): on an
extension `Ω × C` of `(Ω, Q)` (first marginal `Q`) there is a full coupling of the two-seed word with weights
`(r_L, r_R)` whose field is a measurable function `T(H)` of `H` ("This deterministic adjustment"; "The extension
preserves the whole initial field"), with a good event `G'`, such that `Y` is a measurable function of `H` and of the
two-seed history stopped at the local stop of radius `r` of that coupling. -/
def HasReferenceExtension (κ rL rR r : ℝ) {Ω : Type u} {mΩ : MeasurableSpace Ω} (Q : Measure Ω)
    {γ β : Type*} [MeasurableSpace γ] [MeasurableSpace β] (H : Ω → γ) (Y : Ω → β) : Prop :=
  ∃ T : γ → LQGMetric.DistOn upperHalfPlaneOpens, Measurable T ∧
  ∃ (C : Type u) (_ : MeasurableSpace C) (E : Measure (Ω × C)) (_ : IsProbabilityMeasure E)
    (𝓕' : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × C))) (W' : ℝ≥0 → Ω × C → ℝ)
    (VL' VR' : Fin 1 → ℝ≥0 → Ω × C → ℝ) (B' : ℝ≥0 → Ω × C → ℝ) (ζ' : Ω × C → ℝ≥0∞),
    E.map Prod.fst = Q ∧
    IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) E 𝓕' W' VL' VR' B' ζ'
      (fun p => T (H p.1)) ∧
    ∃ G' : Set (Ω × C), MeasurableSet G' ∧ E G'ᶜ = 0 ∧
      (∀ p ∈ G', IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) W' VL' VR' B' ζ' p) ∧
      ∃ F : γ × TwoSeedHist → β, Measurable F ∧
        ∀ᵐ p ∂E, Y p.1 = F (H p.1, stoppedHistory (completedState W' VL' VR' ζ') (capStop r G' ζ' W') p)

/-- **The extended reference pair determines** (Aux. lemma 55, p. 250: "By the assumed two-seed input the full
reference history is determined by `h₀`. Its determining function is the same for every such reference coupling …
The measures in (HL3) are equivalent, so this identity holds for the original coupling as well"): under the two-seed
input, if `Y` is recovered from an extended reference pair over `(Ω, Q)` then `Y` is `Q`-almost surely a Borel function
of `H`. -/
theorem HasReferenceExtension.isAEDeterminedBy {κ rL rR r : ℝ} (hκ : 0 < κ) (h2 : LP.TwoSeedGraphInput.{u} κ)
    (hL : -2 < rL) (hR : -2 < rR) {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {γ β₁ β₂ : Type*}
    [MeasurableSpace γ] [MeasurableSpace β₁] [MeasurableSpace β₂] [MeasurableEq β₁] [MeasurableEq β₂]
    {H : Ω → γ} {Y : Ω → β₁ × β₂} (hext : HasReferenceExtension.{u} κ rL rR r Q H Y)
    (hH : AEMeasurable H Q) (hY : AEMeasurable Y Q) : IsAEDeterminedBy Q H Y := by
  obtain ⟨T, hT, C, mC, E, hE, 𝓕', W', VL', VR', B', ζ', hEQ, hC', G', hG'm, hG'0, hG', F, hFm, hagree⟩ := hext
  obtain ⟨g, hg, hgall⟩ := twoSeed_exists_stoppedGraph hκ h2 hL hR r
  have hgE := hgall E 𝓕' W' VL' VR' B' ζ' _ hC' G' hG'm hG'0 hG'
  have hdetE : IsAEDeterminedBy E (fun p => H p.1) fun p => Y p.1 := by
    refine ⟨fun x => F (x, g (T x)), hFm.comp (measurable_id.prodMk (hg.comp hT)), ?_⟩
    filter_upwards [hagree, hgE] with p h1 h1'
    rw [h1, h1']
  exact isAEDeterminedBy_of_map_fst' hEQ hH hY hdetE

/-- **Named input: the extended reference pair of Aux. lemma 55** (specification pp. 247–250, (HL1)–(HL9), with Aux.
lemma 54, p. 246; steps 1–6 of the split in `planning/handoffs/PROVE-AUX52-55.md`). For every coupling of an ordered
force word with an admissible seed and every good event `G` (so that `S = capStop r G ζ W` is the local stop of the
seed radius `r = seedRadius xL xR`): a probability measure `Q` equivalent to `P` ((HL3): `dQ = Z dP`) and an extended
reference pair over `(Ω, Q)` for the seed weights `(r_−, r_+)` (`seedSumL`, `seedSumR`) and the radius `r`, whose field
is the recoded field `h₀ = T(h)` of (HL8) and which recovers the history stopped at `S` (through `S` the two drivers
coincide, the seed marks are the merged original seed marks, the distant marks are the Loewner flows of their
positions under the driver). -/
def ReferenceExtensionStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR → ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h →
      ∀ G : Set Ω, MeasurableSet G → P Gᶜ = 0 → (∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) →
      ∃ Q : Measure Ω, IsProbabilityMeasure Q ∧ P ≪ Q ∧ Q ≪ P ∧
        HasReferenceExtension.{u} κ (seedSumL xL ρL) (seedSumR xR ρR) (seedRadius xL xR) Q h
          (stoppedHistory (completedState W VL VR ζ) (capStop (seedRadius xL xR) G ζ W))

/-! ### Step 7: determination of the stopped history at the seed -/

section Step7

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- **Aux. lemma 55 (determination at the seed)**: under the two-seed input and the extended reference pair, the
history of a coupling stopped at the local stop of its seed radius is almost surely a Borel function of the field
(p. 250: "the full reference history is determined by `h₀` … Its stopped history through `S` is in fact determined …
The measures in (HL3) are equivalent, so this identity holds for the original coupling as well"). -/
theorem isAEDeterminedBy_stoppedHistory_capStop (hκ : 0 < κ) (h2 : LP.TwoSeedGraphInput.{u} κ)
    (href : ReferenceExtensionStatement.{u} κ) (hF : IsOrderedForceWord xL xR)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) [IsProbabilityMeasure P]
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) {G : Set Ω} (hGm : MeasurableSet G)
    (hG0 : P Gᶜ = 0) (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) :
    IsAEDeterminedBy P h (stoppedHistory (completedState W VL VR ζ) (capStop (seedRadius xL xR) G ζ W)) := by
  obtain ⟨Q, hQ, hPQ, hQP, hext⟩ := href xL xR ρL ρR hF hseed P 𝓕 W VL VR B ζ h hC G hGm hG0 hG
  obtain ⟨hL, hR⟩ := seedSum_gt_of_not_thresholdCondition hseed
  obtain ⟨hX, -⟩ := hC.2.2.2
  have haem : AEMeasurable (stoppedHistory (completedState W VL VR ζ) (capStop (seedRadius xL xR) G ζ W)) P :=
    aemeasurable_stoppedHistory hX (ae_continuousOn_completedState hκ hC.1)
      (isStoppingTime_capStop hX hGm hG0 hG _).measurable' (capStop_le _)
  exact Sec7.IsAEDeterminedBy.of_absolutelyContinuous
    (hext.isAEDeterminedBy hκ h2 hL hR hC.2.1.aemeasurable (haem.mono_ac hQP)) hPQ

end Step7

end LocalExt

end InteractingSLE
