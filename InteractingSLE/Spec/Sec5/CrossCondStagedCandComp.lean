/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedCandTree

/-!
# Proposition 5.9: the adaptive stage law in a generic comparison form

Packet PROVE-STAGED7. PROVE-STAGED6 and `CrossCondStagedCandTree` carry the stage law `IsStageLaw` (pieces compared
with integrated evolutions run to their continuation threshold) from the fixed candidates to the adaptive
construction `histSys`. Proposition 5.9's pieces are used only before their first new contact (p. 144; R71, R73), and
the law may have to be stated for pieces killed there (PROVE-PROP59-PIECES §5.2). Every such variant has the same shape:
a pathwise clause almost surely on the reached event, and a comparison of `p P(A)` with `P(A ∩ {obs ∈ S})` for past
events `A`, under a premise on `(S, p)` that does not see the sample space. This file proves the reduction once for
that shape:

* `stageRec`: the sample record of a stage at `ω` (start, driver, marks, noise, lifetime);
* **`IsCompLaw`**: the generic comparison-form law for a pathwise predicate `Φ` and an observable `g` of the record and
  a premise `Prem`; `isStageLaw_iff_isCompLaw` (`IsStageLaw` is the instance with the threshold premise);
* `isCompLaw_of_mix`: the law of a countable mixture (as PROVE-STAGED6's `isStageLaw_of_mix`);
* `IsCandTree`, `inv_hstate_tree`: the tree consistency and the induction along the realized history without the
  law (PROVE-STAGED6's `inv_hstate`), `isCandTree_canon` for the canonical candidate tree;
* **`isCompLaw_histSys_canon`**: every stage of `histSys` obeys `IsCompLaw` with stage-dependent `Φ j`, `g j`,
  `Prem j` if every fixed candidate does for its canonical past, reached event and start.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedCand

open Prop59Stage Prop59System StagedAdapt

/-! ### The generic comparison form -/

section Comp

variable {Ω : Type*} {nL nR : ℕ}

/-- **The sample record of a stage**: start, driver, left and right marks, noise and lifetime at `ω`. -/
abbrev StageRec (nL nR : ℕ) : Type :=
  Start nL nR × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) × ℝ≥0∞

/-- The record of `(y, W, V_L, V_R, B, ζ)` at `ω`. -/
def stageRec (y : Ω → Start nL nR) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : StageRec nL nR :=
  (y ω, (W · ω), (fun i t => VL i t ω), (fun k t => VR k t ω), (B · ω), ζ ω)

variable {𝓠 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

/-- **The generic comparison-form law**: almost surely on `R` the record satisfies `Φ`; and for every measurable
`S` and `p` with `Prem S p`, every past event `A ⊆ R` has `p P(A) ≤ P(A ∩ {g(record) ∈ S})`. -/
def IsCompLaw {X : Type*} [MeasurableSpace X] (P : Measure Ω) (𝓠 : MeasurableSpace Ω) (R : Set Ω)
    (Φ : StageRec nL nR → Prop) (g : StageRec nL nR → X) (Prem : Set X → ℝ≥0∞ → Prop)
    (rec : Ω → StageRec nL nR) : Prop :=
  (∀ᵐ ω ∂P, ω ∈ R → Φ (rec ω)) ∧
  ∀ S : Set X, MeasurableSet S → ∀ p : ℝ≥0∞, Prem S p → ∀ A : Set Ω, MeasurableSet[𝓠] A → A ⊆ R →
    p * P A ≤ P (A ∩ {ω | g (rec ω) ∈ S})

/-- The pathwise clause of `IsStageLaw`. -/
def stagePath (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (x : StageRec nL nR) : Prop :=
  IsOrderedForceWord x.1.2.1 x.1.2.2 ∧ StrictAnti x.1.2.1 ∧ StrictMono x.1.2.2 ∧
    IsIntegratedSLEPath κ x.1.2.1 x.1.2.2 ρL ρR x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2

/-- The observable of `IsStageLaw`: the start and the samples. -/
def stageObsRec (x : StageRec nL nR) : Start nL nR × Samp nL nR :=
  (x.1, samp x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.2)

/-- The premise of `IsStageLaw` (every integrated evolution from every start, run to its continuation threshold). -/
def stagePrem (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (S : Set (Start nL nR × Samp nL nR)) (p : ℝ≥0∞) :
    Prop :=
  ∀ (y₀ : Start nL nR) (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕' : Filtration ℝ≥0 mΩ') (W' : ℝ≥0 → Ω' → ℝ) (VL' : Fin nL → ℝ≥0 → Ω' → ℝ)
    (VR' : Fin nR → ℝ≥0 → Ω' → ℝ) (B' : ℝ≥0 → Ω' → ℝ) (ζ' : Ω' → ℝ≥0∞),
    IsIntegratedSLEEvolution κ y₀.2.1 y₀.2.2 ρL ρR P' 𝓕' W' VL' VR' B' ζ' →
    (∀ᵐ ω' ∂P', ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω') (ζ' ω') η) →
    p ≤ P' {ω' | (y₀, samp (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω') (ζ' ω')) ∈ S}

/-- **`IsStageLaw` is a generic comparison-form law.** -/
theorem isStageLaw_iff_isCompLaw {κ : ℝ} {P : Measure Ω} {R : Set Ω} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {y : Ω → Start nL nR} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} :
    @IsStageLaw κ Ω mΩ P 𝓠 R nL nR ρL ρR y W VL VR B ζ ↔
      IsCompLaw P 𝓠 R (stagePath κ ρL ρR) stageObsRec (stagePrem κ ρL ρR) (stageRec y W VL VR B ζ) :=
  Iff.rfl

end Comp

/-! ### The law of a countable mixture -/

section Mix

variable {Ω : Type*} {𝓠 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {K : Type*} [Countable K]
  {nL nR : ℕ}
  {X : Type*} [MeasurableSpace X] {Φ : StageRec nL nR → Prop} {g : StageRec nL nR → X}
  {Prem : Set X → ℝ≥0∞ → Prop}

/-- **The generic comparison-form law of a countable mixture** (PROVE-STAGED6's `isStageLaw_of_mix` for
`IsCompLaw`): if each component obeys the law for its past and reached event, almost surely on `R ∩ {I = k}` the
`k`-th component's event is reached and the records agree, and past events of the mixture restricted to `{I = k}`
are a.e. past events of the `k`-th component, then the mixture obeys the law. -/
theorem isCompLaw_of_mix {R : Set Ω} {rec : Ω → StageRec nL nR} (I : Ω → K)
    (hI : ∀ k, MeasurableSet[mΩ] {ω | I ω = k}) (𝓠k : K → MeasurableSpace Ω) (Rk : K → Set Ω)
    (reck : K → Ω → StageRec nL nR) (hlaw : ∀ k, IsCompLaw P (𝓠k k) (Rk k) Φ g Prem (reck k))
    (hRk : ∀ k, MeasurableSet[𝓠k k] (Rk k))
    (hRy : ∀ k, ∀ᵐ ω ∂P, ω ∈ R → I ω = k → ω ∈ Rk k ∧ rec ω = reck k ω)
    (htr : ∀ k A, MeasurableSet[𝓠] A → A ⊆ R →
      ∃ A', MeasurableSet[𝓠k k] A' ∧ A ∩ {ω | I ω = k} =ᵐ[P] A') :
    IsCompLaw P 𝓠 R Φ g Prem rec := by
  refine ⟨?_, ?_⟩
  · have h1 := ae_all_iff.2 fun k => (hRy k).and (hlaw k).1
    filter_upwards [h1] with ω hω hωR
    obtain ⟨hRy', hp⟩ := hω (I ω)
    obtain ⟨hR', hy'⟩ := hRy' hωR rfl
    rw [hy']
    exact hp hR'
  · intro S hS p hprem A hA hAR
    have hk : ∀ k, p * P (A ∩ {ω | I ω = k}) ≤ P ((A ∩ {ω | g (rec ω) ∈ S}) ∩ {ω | I ω = k}) := by
      intro k
      obtain ⟨A', hA', he⟩ := htr k A hA hAR
      have he'' : A ∩ {ω | I ω = k} =ᵐ[P] (A' ∩ Rk k : Set Ω) := by
        filter_upwards [he, hRy k] with ω h1 h2
        refine propext ⟨fun h => ⟨?_, (h2 (hAR h.1) h.2).1⟩, fun h => ?_⟩
        · have : (ω ∈ A') := by rw [← h1]; exact h
          exact this
        · have : ω ∈ A ∩ {ω | I ω = k} := by
            have h' : (ω ∈ A') := h.1
            rw [← h1] at h'
            exact h'
          exact this
      have hle := (hlaw k).2 S hS p hprem (A' ∩ Rk k) (hA'.inter (hRk k)) inter_subset_right
      calc p * P (A ∩ {ω | I ω = k}) = p * P (A' ∩ Rk k) := by rw [measure_congr he'']
        _ ≤ P ((A' ∩ Rk k) ∩ {ω | g (reck k ω) ∈ S}) := hle
        _ = P ((A ∩ {ω | g (rec ω) ∈ S}) ∩ {ω | I ω = k}) := by
            refine measure_congr ?_
            filter_upwards [he'', hRy k] with ω h1 h2
            by_cases hω : ω ∈ A ∩ {ω | I ω = k}
            · have hω' : ω ∈ A' ∩ Rk k := by
                have h' : (ω ∈ A ∩ {ω | I ω = k}) := hω
                rw [h1] at h'
                exact h'
              have e := (h2 (hAR hω.1) hω.2).2
              refine propext ⟨fun h => ⟨⟨hω.1, ?_⟩, hω.2⟩, fun h => ⟨hω', ?_⟩⟩
              · show g (rec ω) ∈ S
                rw [e]; exact h.2
              · show g (reck k ω) ∈ S
                rw [← e]; exact h.1.2
            · have hω' : ω ∉ A' ∩ Rk k := by
                intro h'
                have h'' : (ω ∈ A' ∩ Rk k) := h'
                rw [← h1] at h''
                exact hω h''
              refine propext ⟨fun h => absurd h.1 hω', fun h => absurd ⟨h.1.1, h.2⟩ hω⟩
    calc p * P A = p * ∑' k, P (A ∩ {ω | I ω = k}) := by rw [← @measure_eq_tsum_inter_fiber Ω mΩ K _ P I hI A]
      _ = ∑' k, p * P (A ∩ {ω | I ω = k}) := ENNReal.tsum_mul_left.symm
      _ ≤ ∑' k, P ((A ∩ {ω | g (rec ω) ∈ S}) ∩ {ω | I ω = k}) := ENNReal.tsum_le_tsum hk
      _ = P (A ∩ {ω | g (rec ω) ∈ S}) := (@measure_eq_tsum_inter_fiber Ω mΩ K _ P I hI _).symm

end Mix

/-! ### The tree consistency without the law -/

section TreeDef

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL₀ nR₀ : ℕ}

/-- **The candidate tree consistency** (PROVE-STAGED6's `IsCandLawTree` without the law clause): the reached events
are past events; past events, the switch event, the switching time and the next start are past events of the child;
at a switch the child's event is reached and its start is the next start. -/
structure IsCandTree (P : Measure Ω) (cand : CandFam Ω nL₀ nR₀) (G : ℕ → ℕ → ℝ≥0) (hnL : 0 < nL₀) (hnR : 0 < nR₀)
    (𝓠c : (j : ℕ) → (Fin j → ℝ≥0) → MeasurableSpace Ω) (Rc : (j : ℕ) → (Fin j → ℝ≥0) → Set Ω)
    (yc : (j : ℕ) → (Fin j → ℝ≥0) → Ω → Start (nL₀ + j) (nR₀ + j)) : Prop where
  /-- The candidate reached events are past events. -/
  R_meas : ∀ j t, MeasurableSet[𝓠c j t] (Rc j t)
  /-- Past events of a list, the switch event, the switching time and the next start are past events of the child. -/
  step_meas : ∀ j (t : Fin j → ℝ≥0) (n m : ℕ) (A : Set Ω), MeasurableSet[𝓠c j t] A →
    ∀ S : Set (ℝ≥0 × Start (nL₀ + (j + 1)) (nR₀ + (j + 1))), MeasurableSet S →
      MeasurableSet[𝓠c (j + 1) (Fin.snoc (α := fun _ => ℝ≥0) t (G n m))]
        (A ∩ swEv G hnL hnR j (candStage cand yc j t) n m ∩
          {ω | (swT G hnL hnR j (candStage cand yc j t) n ω, nextStart G hnL hnR j (candStage cand yc j t) n ω) ∈ S})
  /-- At a switch the child's event is reached and its start is the next start. -/
  step_start : ∀ j (t : Fin j → ℝ≥0) (n m : ℕ), ∀ᵐ ω ∂P, ω ∈ Rc j t →
    ω ∈ swEv G hnL hnR j (candStage cand yc j t) n m →
      ω ∈ Rc (j + 1) (Fin.snoc (α := fun _ => ℝ≥0) t (G n m)) ∧
        nextStart G hnL hnR j (candStage cand yc j t) n ω = yc (j + 1) (Fin.snoc (α := fun _ => ℝ≥0) t (G n m)) ω

/-- `IsCandLawTree` gives the tree consistency. -/
theorem IsCandLawTree.toIsCandTree {κ : ℝ} {P : Measure Ω} {ρL₀ : Fin nL₀ → ℝ} {ρR₀ : Fin nR₀ → ℝ}
    {cand : CandFam Ω nL₀ nR₀} {G : ℕ → ℕ → ℝ≥0} {hnL : 0 < nL₀} {hnR : 0 < nR₀}
    {𝓠c : (j : ℕ) → (Fin j → ℝ≥0) → MeasurableSpace Ω} {Rc : (j : ℕ) → (Fin j → ℝ≥0) → Set Ω}
    {yc : (j : ℕ) → (Fin j → ℝ≥0) → Ω → Start (nL₀ + j) (nR₀ + j)}
    (h : IsCandLawTree κ P ρL₀ ρR₀ cand G hnL hnR 𝓠c Rc yc) : IsCandTree P cand G hnL hnR 𝓠c Rc yc :=
  ⟨h.R_meas, h.step_meas, h.step_start⟩

end TreeDef

section Canon

variable {Ω : Type*} {𝓑 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL₀ nR₀ : ℕ}
  {cand : CandFam Ω nL₀ nR₀} {G : ℕ → ℕ → ℝ≥0} {hnL : 0 < nL₀} {hnR : 0 < nR₀}
  {y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)} {R₀ : Set Ω}

/-- **The canonical candidate tree is consistent** (at every sample). -/
theorem isCandTree_canon (hfam : IsRegFam cand) (hy₀ : Measurable y₀) (hR₀ : MeasurableSet[𝓑] R₀) :
    IsCandTree P cand G hnL hnR (canonQ 𝓑 cand G hnL hnR y₀) (canonR cand G hnL hnR y₀ R₀) (canonY cand y₀) where
  R_meas := measurableSet_canonR hR₀
  step_meas j t n m A hA S hS := by
    rw [canonQ_snoc, inter_assoc]
    exact (le_sup_left (a := canonQ 𝓑 cand G hnL hnR y₀ j t) _ hA).inter
      (le_sup_right (a := canonQ 𝓑 cand G hnL hnR y₀ j t) _ (measurableSet_swSigma _ hS))
  step_start j t n m := Eventually.of_forall fun _ hR hsw => canon_step_start hfam hy₀ j t n m hR hsw

end Canon

/-! ### The induction along the realized history (law-free) -/

section Induction

variable {Ω : Type*} {𝓑 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL₀ nR₀ : ℕ}
  {cand : CandFam Ω nL₀ nR₀} {G : ℕ → ℕ → ℝ≥0} {hnL : 0 < nL₀}
  {hnR : 0 < nR₀} {y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)} {R₀ : Set Ω}
  {𝓠c : (j : ℕ) → (Fin j → ℝ≥0) → MeasurableSpace Ω} {Rc : (j : ℕ) → (Fin j → ℝ≥0) → Set Ω}
  {yc : (j : ℕ) → (Fin j → ℝ≥0) → Ω → Start (nL₀ + j) (nR₀ + j)}

/-- **The invariant along the realized history** (PROVE-STAGED6's `inv_hstate`, which uses only the tree
consistency): almost surely on `{stage j reached with indices k}` the candidate event of the realized list is reached
and the realized start is the candidate start; past events of the realized stage restricted to that event are a.e.
past events of the candidate. -/
theorem inv_hstate_tree (hT : IsCandTree P cand G hnL hnR 𝓠c Rc yc)
    (h𝓑 : 𝓑 ≤ 𝓠c 0 Fin.elim0) (hR₀ : MeasurableSet[𝓑] R₀)
    (hbase : ∀ᵐ ω ∂P, ω ∈ R₀ → ω ∈ Rc 0 Fin.elim0 ∧ y₀ ω = yc 0 Fin.elim0 ω) (r : ℕ → ℕ) :
    ∀ j, (∀ k : Fin j → ℕ, ∀ᵐ ω ∂P, ω ∈ reachEv cand G hnL hnR y₀ R₀ 𝓑 r j k →
        ω ∈ Rc j (times G r k) ∧ (hstate cand G hnL hnR y₀ R₀ 𝓑 r j).y ω = yc j (times G r k) ω) ∧
      ∀ k : Fin j → ℕ, ∀ A, MeasurableSet[(hstate cand G hnL hnR y₀ R₀ 𝓑 r j).past] A →
        ∃ A', MeasurableSet[𝓠c j (times G r k)] A' ∧ A ∩ reachEv cand G hnL hnR y₀ R₀ 𝓑 r j k =ᵐ[P] A'
  | 0 => by
    have htk : ∀ k : Fin 0 → ℕ, times G r k = Fin.elim0 := fun k => Subsingleton.elim _ _
    have hreach : ∀ k : Fin 0 → ℕ, reachEv cand G hnL hnR y₀ R₀ 𝓑 r 0 k = R₀ := by
      intro k
      ext ω
      simp only [reachEv, mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun h => h.1, fun h => ⟨h, Subsingleton.elim _ _⟩⟩
    refine ⟨fun k => ?_, fun k A hA => ?_⟩
    · rw [hreach, htk]
      exact hbase
    · refine ⟨A ∩ R₀, ?_, ?_⟩
      · rw [htk]
        exact h𝓑 _ (hA.inter hR₀)
      · rw [hreach]
  | j + 1 => by
    obtain ⟨hi, hii⟩ := inv_hstate_tree hT h𝓑 hR₀ hbase r j
    -- the candidate data of the realized list `init k'`
    have hiy : ∀ k' : Fin (j + 1) → ℕ, ∀ᵐ ω ∂P, ω ∈ reachEv cand G hnL hnR y₀ R₀ 𝓑 r j (Fin.init k') →
        (hstate cand G hnL hnR y₀ R₀ 𝓑 r j).y ω = yc j (times G r (Fin.init k')) ω := fun k' => by
      filter_upwards [hi (Fin.init k')] with ω h hω using (h hω).2
    -- traces of past events of stage `j`, jointly with the switch data
    have htrace : ∀ k' : Fin (j + 1) → ℕ, ∀ A, MeasurableSet[(hstate cand G hnL hnR y₀ R₀ 𝓑 r j).past] A →
        ∀ S : Set (ℝ≥0 × Start (nL₀ + (j + 1)) (nR₀ + (j + 1))), MeasurableSet S →
          ∃ A'', MeasurableSet[𝓠c (j + 1) (times G r k')] A'' ∧
            A ∩ reachEv cand G hnL hnR y₀ R₀ 𝓑 r (j + 1) k' ∩
              {ω | (swT G hnL hnR j (histSys cand G hnL hnR y₀ R₀ 𝓑 r j) (r j) ω,
                nextStart G hnL hnR j (histSys cand G hnL hnR y₀ R₀ 𝓑 r j) (r j) ω) ∈ S} =ᵐ[P] A'' := by
      intro k' A hA S hS
      obtain ⟨A', hA', he⟩ := hii (Fin.init k') A hA
      refine ⟨A' ∩ swEv G hnL hnR j (candStage cand yc j (times G r (Fin.init k'))) (r j) (k' (Fin.last j)) ∩
        {ω | (swT G hnL hnR j (candStage cand yc j (times G r (Fin.init k'))) (r j) ω,
          nextStart G hnL hnR j (candStage cand yc j (times G r (Fin.init k'))) (r j) ω) ∈ S}, ?_, ?_⟩
      · rw [times_eq_snoc r k']
        exact hT.step_meas j _ (r j) (k' (Fin.last j)) A' hA' S hS
      · exact (ae_step_eq r j k' (hiy k') A S).trans ((he.inter EventuallyEqSet.rfl).inter EventuallyEqSet.rfl)
    refine ⟨fun k' => ?_, fun k' A hA => ?_⟩
    · -- (i) at stage `j + 1`
      filter_upwards [hi (Fin.init k'), hT.step_start j (times G r (Fin.init k')) (r j) (k' (Fin.last j))]
        with ω h1 h2 hω
      rw [reachEv_succ] at hω
      obtain ⟨⟨h0, hsucc⟩, hidx⟩ := hω
      obtain ⟨hRc, hy⟩ := h1 h0
      have hfrz := frz_stageOf_eq cand yc r (hstate cand G hnL hnR y₀ R₀ 𝓑 r j) h0.2 hy
      obtain ⟨hs, hidx', -, hN⟩ := switch_congr_of_frz G hnL hnR j hfrz (r j)
      have hsw : ω ∈ swEv G hnL hnR j (candStage cand yc j (times G r (Fin.init k'))) (r j) (k' (Fin.last j)) := by
        refine ⟨hs.1 hsucc, ?_⟩
        have : swIdx G hnL hnR j (stageOf cand G r j (hstate cand G hnL hnR y₀ R₀ 𝓑 r j)) (r j) ω =
            k' (Fin.last j) := hidx
        rw [hidx'] at this
        exact this
      obtain ⟨hR', hy'⟩ := h2 hRc hsw
      rw [times_eq_snoc r k']
      exact ⟨hR', hN.trans hy'⟩
    · -- (ii) at stage `j + 1`: the a.e. trace σ-algebra contains the new past
      have hE : ∃ E', MeasurableSet[𝓠c (j + 1) (times G r k')] E' ∧
          reachEv cand G hnL hnR y₀ R₀ 𝓑 r (j + 1) k' =ᵐ[P] E' := by
        obtain ⟨A'', h1, h2⟩ := htrace k' univ MeasurableSet.univ univ MeasurableSet.univ
        refine ⟨A'', h1, EventuallyEqSet.trans (EventuallyEqSet.of_eq ?_) h2⟩
        ext ω
        simp only [mem_inter_iff, mem_univ, true_and, mem_ofPred_eq, and_true]
      have hle : (hstate cand G hnL hnR y₀ R₀ 𝓑 r (j + 1)).past ≤
          aeTrace P (𝓠c (j + 1) (times G r k')) (reachEv cand G hnL hnR y₀ R₀ 𝓑 r (j + 1) k') hE := by
        refine sup_le (fun A hA => ?_) (sup_le (MeasurableSpace.generateFrom_le ?_) ?_)
        · obtain ⟨A'', h1, h2⟩ := htrace k' A hA univ MeasurableSet.univ
          refine ⟨A'', h1, EventuallyEqSet.trans (EventuallyEqSet.of_eq ?_) h2⟩
          ext ω
          simp only [mem_inter_iff, mem_univ, mem_ofPred_eq, and_true]
        · intro B hB
          rcases hB with rfl | rfl
          · obtain ⟨A'', h1, h2⟩ := htrace k' univ MeasurableSet.univ univ MeasurableSet.univ
            refine ⟨A'', h1, EventuallyEqSet.trans (EventuallyEqSet.of_eq ?_) h2⟩
            ext ω
            simp only [mem_inter_iff, mem_univ, true_and, mem_ofPred_eq, and_true]
            exact ⟨fun h => h.2, fun h => ⟨reachEv_succ_subset r j k' h, h⟩⟩
          · obtain ⟨A'', h1, h2⟩ := htrace k' univ MeasurableSet.univ {p | (1 : ℝ≥0) ≤ p.1}
              (measurableSet_le measurable_const measurable_fst)
            refine ⟨A'', h1, EventuallyEqSet.trans (EventuallyEqSet.of_eq ?_) h2⟩
            ext ω
            simp only [mem_inter_iff, mem_univ, true_and, mem_ofPred_eq]
            exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨reachEv_succ_subset r j k' h.1, h.2⟩, h.1⟩⟩
        · intro B hB
          obtain ⟨S'', hS'', rfl⟩ := hB
          obtain ⟨A'', h1, h2⟩ := htrace k' univ MeasurableSet.univ
            {p : ℝ≥0 × Start (nL₀ + (j + 1)) (nR₀ + (j + 1)) | (k', p.2) ∈ S''}
            ((measurable_prodMk_left.comp measurable_snd) hS'')
          refine ⟨A'', h1, EventuallyEqSet.trans (EventuallyEqSet.of_eq ?_) h2⟩
          ext ω
          simp only [mem_inter_iff, mem_univ, true_and, mem_ofPred_eq, mem_preimage]
          refine ⟨fun h => ⟨h.2, ?_⟩, fun h => ⟨?_, h.1⟩⟩
          · have e : nextHist G hnL hnR j (stageOf cand G r j (hstate cand G hnL hnR y₀ R₀ 𝓑 r j)) (r j)
                (hstate cand G hnL hnR y₀ R₀ 𝓑 r j).hist ω = k' := h.2.2
            have := h.1
            rw [e] at this
            exact this
          · have e : nextHist G hnL hnR j (stageOf cand G r j (hstate cand G hnL hnR y₀ R₀ 𝓑 r j)) (r j)
                (hstate cand G hnL hnR y₀ R₀ 𝓑 r j).hist ω = k' := h.1.2
            show (nextHist G hnL hnR j (stageOf cand G r j (hstate cand G hnL hnR y₀ R₀ 𝓑 r j)) (r j)
                (hstate cand G hnL hnR y₀ R₀ 𝓑 r j).hist ω, _) ∈ S''
            rw [e]
            exact h.2
      exact hle A hA

end Induction

/-! ### The adaptive law from the per-candidate laws (generic form) -/

section Law

variable {Ω : Type*} {𝓑 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL₀ nR₀ : ℕ}
  {cand : CandFam Ω nL₀ nR₀} {G : ℕ → ℕ → ℝ≥0} {hnL : 0 < nL₀}
  {hnR : 0 < nR₀} {y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)} {R₀ : Set Ω}
  {𝓠c : (j : ℕ) → (Fin j → ℝ≥0) → MeasurableSpace Ω} {Rc : (j : ℕ) → (Fin j → ℝ≥0) → Set Ω}
  {yc : (j : ℕ) → (Fin j → ℝ≥0) → Ω → Start (nL₀ + j) (nR₀ + j)}
  {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)] {Φ : (j : ℕ) → StageRec (nL₀ + j) (nR₀ + j) → Prop}
  {g : (j : ℕ) → StageRec (nL₀ + j) (nR₀ + j) → X j} {Prem : (j : ℕ) → Set (X j) → ℝ≥0∞ → Prop}

/-- **The adaptive law from the candidate laws along a consistent tree** (generic comparison form). -/
theorem isCompLaw_histSys (hT : IsCandTree P cand G hnL hnR 𝓠c Rc yc)
    (hlaw : ∀ j t, IsCompLaw P (𝓠c j t) (Rc j t) (Φ j) (g j) (Prem j)
      (stageRec (yc j t) (cand j t).W (cand j t).VL (cand j t).VR (cand j t).B (cand j t).ζ))
    (h𝓑 : 𝓑 ≤ 𝓠c 0 Fin.elim0) (hR₀ : MeasurableSet[𝓑] R₀)
    (hbase : ∀ᵐ ω ∂P, ω ∈ R₀ → ω ∈ Rc 0 Fin.elim0 ∧ y₀ ω = yc 0 Fin.elim0 ω)
    (hhist : ∀ r j, Measurable (hstate cand G hnL hnR y₀ R₀ 𝓑 r j).hist) (r : ℕ → ℕ) (j : ℕ) :
    IsCompLaw P (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).past (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).R (Φ j) (g j)
      (Prem j) (stageRec (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).y (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).W
        (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).VL (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).VR
        (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).B (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).ζ) := by
  obtain ⟨hi, hii⟩ := inv_hstate_tree hT h𝓑 hR₀ hbase r j
  refine isCompLaw_of_mix (hstate cand G hnL hnR y₀ R₀ 𝓑 r j).hist
    (fun k => hhist r j (measurableSet_singleton k)) (fun k => 𝓠c j (times G r k)) (fun k => Rc j (times G r k))
    (fun k => stageRec (yc j (times G r k)) (cand j (times G r k)).W (cand j (times G r k)).VL
      (cand j (times G r k)).VR (cand j (times G r k)).B (cand j (times G r k)).ζ)
    (fun k => hlaw j _) (fun k => hT.R_meas j _) ?_ ?_
  · intro k
    filter_upwards [hi k] with ω h hR hk
    obtain ⟨h1, h2⟩ := h ⟨hR, hk⟩
    refine ⟨h1, ?_⟩
    subst hk
    show (_, _, _, _, _, _) = (_, _, _, _, _, _)
    rw [show (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).y ω = (hstate cand G hnL hnR y₀ R₀ 𝓑 r j).y ω from rfl, h2]
    rfl
  · intro k A hA hAR
    obtain ⟨A', h1, h2⟩ := hii k A hA
    refine ⟨A', h1, EventuallyEqSet.trans (EventuallyEqSet.of_eq ?_) h2⟩
    ext ω
    simp only [reachEv, mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun h => ⟨h.1, hAR h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

/-- **The adaptive law from the per-candidate laws on the canonical candidate tree** (generic comparison form): if
every fixed candidate obeys `IsCompLaw` (with the stage-`j` clause `Φ j`, observable `g j` and premise `Prem j`) for
its canonical past, reached event and start, then every stage of `histSys` does. With `Φ, g, Prem` those of
`IsStageLaw` (`isStageLaw_iff_isCompLaw`) this is `prop59StageLawStatement_histSys_canon`; any killed variant of the
stage law with the same shape is covered as well. -/
theorem isCompLaw_histSys_canon (hfam : IsRegFam cand) (hy₀ : Measurable y₀) (hR₀ : MeasurableSet[𝓑] R₀)
    (hlaw : ∀ j t, IsCompLaw P (canonQ 𝓑 cand G hnL hnR y₀ j t) (canonR cand G hnL hnR y₀ R₀ j t) (Φ j) (g j)
      (Prem j) (stageRec (canonY cand y₀ j t) (cand j t).W (cand j t).VL (cand j t).VR (cand j t).B (cand j t).ζ))
    (r : ℕ → ℕ) (j : ℕ) :
    IsCompLaw P (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).past (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).R (Φ j) (g j)
      (Prem j) (stageRec (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).y (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).W
        (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).VL (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).VR
        (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).B (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).ζ) :=
  isCompLaw_histSys (isCandTree_canon hfam hy₀ hR₀) hlaw le_rfl hR₀ (Eventually.of_forall fun _ h => ⟨h, rfl⟩)
    (fun r j => (measurable_hstate hfam hy₀ r j).2) r j

end Law

end InteractingSLE.Sec5.CrossCond.StagedCand
