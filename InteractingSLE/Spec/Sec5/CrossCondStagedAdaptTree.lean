/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedAdaptMix

/-!
# Proposition 5.9: the adaptive stage law from candidate laws along the tree of switching histories

Packet PROVE-STAGED6 (R73: Astra's follow-up 5, correction L8–L14 and §2.3, equation (2.2)). PROVE-PROP59T4's
adaptive construction `histSys cand G …` runs, at stage `j`, the candidate `cand j t` of the realized list `t` of
original switching times (`histSys_piece`): the realized adaptive prefix **is** the canonical member of the countable
candidate family at its realized index, which is (2.2). The adaptive switching rule depends on the revealed history
(e.g. the retained counterflow) only through the countably valued realized grid indices `hist`.

This file carries the stage law over that countable index:

* `frz`: a stage frozen at a sample; the switching data (`succSet`, `swIdx`, `swT`, `nextStart`) at `ω` only see the
  stage's values at `ω` (`swT_frz`, …), so on `{hist = k}` they are the candidate's (`frz_stageOf_eq`);
* `aeTrace`: the σ-algebra of sets whose trace on `E` is, up to a null set, a set of a given σ-algebra;
* **`IsCandLawTree`**: every candidate `cand j t` obeys `IsStageLaw` with the deterministic stage word for its own
  past `𝓠c j t`, reached event `Rc j t` and start `yc j t`, and the candidate tree is consistent at the switches (on
  the event that `cand j t` switches at the grid point `G n m`, the parent's past, the switching time and the next
  start are measurable for the child's past, the child's event is reached and its start is the next start);
* **`prop59StageLawStatement_histSys`**: `Prop59StageLawStatement` for `histSys` from `IsCandLawTree` and the root
  conditions (by induction along the realized history, `inv_hstate`, and `isStageLaw_of_mix`).

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedAdapt

open Prop59Stage Prop59System

/-! ### Frozen stages -/

section Frz

variable {Ω : Type*} {nL₀ nR₀ : ℕ}

/-- **The stage `d` frozen at `ω`**: every field evaluated at `ω` (constant in the sample), past `⊥`, no reached
event. -/
def frz {nL nR : ℕ} (d : StageData Ω nL nR) (ω : Ω) : StageData Ω nL nR :=
  ⟨⊥, ∅, fun _ => d.y ω, fun u _ => d.W u ω, fun i u _ => d.VL i u ω, fun k u _ => d.VR k u ω,
    fun u _ => d.B u ω, fun _ => d.ζ ω, fun _ => d.clk ω⟩

theorem frz_congr {nL nR : ℕ} {d d' : StageData Ω nL nR} {ω : Ω} (hy : d.y ω = d'.y ω)
    (hW : ∀ u, d.W u ω = d'.W u ω) (hVL : ∀ i u, d.VL i u ω = d'.VL i u ω)
    (hVR : ∀ k u, d.VR k u ω = d'.VR k u ω) (hB : ∀ u, d.B u ω = d'.B u ω) (hζ : d.ζ ω = d'.ζ ω)
    (hc : d.clk ω = d'.clk ω) : frz d ω = frz d' ω := by
  simp only [frz, hy, hW, hVL, hVR, hB, hζ, hc]

variable (G : ℕ → ℕ → ℝ≥0) (hnL : 0 < nL₀) (hnR : 0 < nR₀) (j : ℕ)

theorem mem_succSet_frz (d : StageData Ω (nL₀ + j) (nR₀ + j)) (n : ℕ) (ω : Ω) :
    ω ∈ succSet G hnL hnR j d n ↔ ω ∈ succSet G hnL hnR j (frz d ω) n := Iff.rfl

theorem swT_frz (d : StageData Ω (nL₀ + j) (nR₀ + j)) (n : ℕ) (ω : Ω) :
    swT G hnL hnR j d n ω = swT G hnL hnR j (frz d ω) n ω := rfl

theorem swIdx_frz (d : StageData Ω (nL₀ + j) (nR₀ + j)) (n : ℕ) (ω : Ω) :
    swIdx G hnL hnR j d n ω = swIdx G hnL hnR j (frz d ω) n ω := rfl

theorem nextStart_frz (d : StageData Ω (nL₀ + j) (nR₀ + j)) (n : ℕ) (ω : Ω) :
    nextStart G hnL hnR j d n ω = nextStart G hnL hnR j (frz d ω) n ω := rfl

/-- The switching data of two stages agree at a sample where their frozen stages agree. -/
theorem switch_congr_of_frz {d d' : StageData Ω (nL₀ + j) (nR₀ + j)} {ω : Ω} (h : frz d ω = frz d' ω) (n : ℕ) :
    (ω ∈ succSet G hnL hnR j d n ↔ ω ∈ succSet G hnL hnR j d' n) ∧
      swIdx G hnL hnR j d n ω = swIdx G hnL hnR j d' n ω ∧ swT G hnL hnR j d n ω = swT G hnL hnR j d' n ω ∧
      nextStart G hnL hnR j d n ω = nextStart G hnL hnR j d' n ω := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem_succSet_frz, h, ← mem_succSet_frz]
  · rw [swIdx_frz, h, ← swIdx_frz]
  · rw [swT_frz, h, ← swT_frz]
  · rw [nextStart_frz, h, ← nextStart_frz]

/-- **The candidate stage** of the list `t` at depth `j`: the candidate piece with the candidate start `yc j t`. -/
def candStage (cand : CandFam Ω nL₀ nR₀) (yc : (j : ℕ) → (Fin j → ℝ≥0) → Ω → Start (nL₀ + j) (nR₀ + j))
    (j : ℕ) (t : Fin j → ℝ≥0) : StageData Ω (nL₀ + j) (nR₀ + j) :=
  (cand j t).toStage ⊥ ∅ (yc j t)

/-- **The switch event at the grid point `G n m`**: the stage succeeds and `m` is its least successful grid index. -/
def swEv (d : StageData Ω (nL₀ + j) (nR₀ + j)) (n m : ℕ) : Set Ω :=
  succSet G hnL hnR j d n ∩ {ω | swIdx G hnL hnR j d n ω = m}

variable {G hnL hnR j}

/-- **On `{hist = k}` the realized stage is the candidate of the realized list** (frozen at the sample), when the
start is the candidate start. -/
theorem frz_stageOf_eq (cand : CandFam Ω nL₀ nR₀)
    (yc : (j : ℕ) → (Fin j → ℝ≥0) → Ω → Start (nL₀ + j) (nR₀ + j)) (r : ℕ → ℕ) (st : HState Ω nL₀ nR₀ j)
    {ω : Ω} {k : Fin j → ℕ} (hk : st.hist ω = k) (hy : st.y ω = yc j (times G r k) ω) :
    frz (stageOf cand G r j st) ω = frz (candStage cand yc j (times G r k)) ω := by
  subst hk
  exact frz_congr hy (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) rfl rfl

end Frz

/-! ### Traces up to null sets -/

section Trace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The a.e. trace σ-algebra**: the sets `A` whose trace `A ∩ E` agrees `P`-a.e. with a `𝓒`-measurable set (given
that `E` itself does). -/
@[instance_reducible]
def aeTrace (P : Measure Ω) (𝓒 : MeasurableSpace Ω) (E : Set Ω)
    (hE : ∃ E', MeasurableSet[𝓒] E' ∧ E =ᵐ[P] E') : MeasurableSpace Ω where
  MeasurableSet' A := ∃ A', MeasurableSet[𝓒] A' ∧ A ∩ E =ᵐ[P] A'
  measurableSet_empty := ⟨∅, MeasurableSet.empty, EventuallyEqSet.of_eq (empty_inter E)⟩
  measurableSet_compl A := by
    rintro ⟨A', hA', h⟩
    obtain ⟨E', hE', hEE'⟩ := hE
    refine ⟨E' \ A', hE'.diff hA', ?_⟩
    have e : Aᶜ ∩ E = E \ (A ∩ E) := by
      ext ω
      simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]
      tauto
    rw [e]
    exact hEE'.diff h
  measurableSet_iUnion f hf := by
    choose A' hA' h using hf
    refine ⟨⋃ i, A' i, @MeasurableSet.iUnion Ω _ 𝓒 _ A' hA', ?_⟩
    rw [iUnion_inter]
    exact EventuallyEqSet.countable_iUnion h

theorem measurableSet_aeTrace_iff {P : Measure Ω} {𝓒 : MeasurableSpace Ω} {E : Set Ω}
    {hE : ∃ E', MeasurableSet[𝓒] E' ∧ E =ᵐ[P] E'} {A : Set Ω} :
    MeasurableSet[aeTrace P 𝓒 E hE] A ↔ ∃ A', MeasurableSet[𝓒] A' ∧ A ∩ E =ᵐ[P] A' := Iff.rfl

end Trace

/-! ### Candidate laws along the tree of switching histories -/

section TreeDef

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL₀ nR₀ : ℕ}

/-- **Candidate stage laws along the tree of switching histories.** For every list `t : Fin j → ℝ≥0` of original
switching times, the candidate `cand j t` obeys `IsStageLaw` with the deterministic stage word for its own past
`𝓠c j t`, reached event `Rc j t ∈ 𝓠c j t` and start `yc j t`; and the tree is consistent at the switches: on the
event `swEv … n m` that the candidate stage of `t` switches at the grid point `G n m`, (`step_meas`) every past event
of `t`, jointly with any Borel condition on the switching time and the next start, is a past event of the child list
`snoc t (G n m)`, and (`step_start`) almost surely on `Rc j t` the child's event is reached and its start is the
next start. -/
structure IsCandLawTree (κ : ℝ) (P : Measure Ω) (ρL₀ : Fin nL₀ → ℝ) (ρR₀ : Fin nR₀ → ℝ)
    (cand : CandFam Ω nL₀ nR₀) (G : ℕ → ℕ → ℝ≥0) (hnL : 0 < nL₀) (hnR : 0 < nR₀)
    (𝓠c : (j : ℕ) → (Fin j → ℝ≥0) → MeasurableSpace Ω) (Rc : (j : ℕ) → (Fin j → ℝ≥0) → Set Ω)
    (yc : (j : ℕ) → (Fin j → ℝ≥0) → Ω → Start (nL₀ + j) (nR₀ + j)) : Prop where
  /-- The candidate stage laws. -/
  law : ∀ j t, @IsStageLaw κ Ω mΩ P (𝓠c j t) (Rc j t) (nL₀ + j) (nR₀ + j) (stageρL κ ρL₀ j) (stageρR κ ρR₀ j)
    (yc j t) (cand j t).W (cand j t).VL (cand j t).VR (cand j t).B (cand j t).ζ
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

end TreeDef

section Reach

variable {Ω : Type*} {nL₀ nR₀ : ℕ}

/-- **The event that stage `j` is reached with the realized grid indices `k`.** -/
def reachEv (cand : CandFam Ω nL₀ nR₀) (G : ℕ → ℕ → ℝ≥0) (hnL : 0 < nL₀) (hnR : 0 < nR₀)
    (y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)) (R₀ : Set Ω) (𝓑 : MeasurableSpace Ω) (r : ℕ → ℕ) (j : ℕ)
    (k : Fin j → ℕ) : Set Ω :=
  (hstate cand G hnL hnR y₀ R₀ 𝓑 r j).R ∩ {ω | (hstate cand G hnL hnR y₀ R₀ 𝓑 r j).hist ω = k}

variable {cand : CandFam Ω nL₀ nR₀} {G : ℕ → ℕ → ℝ≥0} {hnL : 0 < nL₀} {hnR : 0 < nR₀}
  {y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)} {R₀ : Set Ω} {𝓑 : MeasurableSpace Ω}

/-- The original switching times of a list of `j + 1` grid indices: those of its first `j`, then the last switch. -/
theorem times_eq_snoc (r : ℕ → ℕ) {j : ℕ} (k' : Fin (j + 1) → ℕ) :
    times G r k' = Fin.snoc (α := fun _ => ℝ≥0) (times G r (Fin.init k')) (G (r j) (k' (Fin.last j))) := by
  funext i
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simp only [times, Fin.snoc_last, Fin.val_last]
  · simp only [times, Fin.snoc_castSucc, Fin.init, Fin.val_castSucc]

theorem snoc_eq_iff {j : ℕ} (a : Fin j → ℕ) (x : ℕ) (b : Fin (j + 1) → ℕ) :
    Fin.snoc (α := fun _ => ℕ) a x = b ↔ a = Fin.init b ∧ x = b (Fin.last j) := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨h1, h2⟩ => ?_⟩
  · rw [← h, Fin.init_snoc]
  · rw [← h, Fin.snoc_last]
  · rw [h1, h2, Fin.snoc_init_self]

/-- **The reached events along the realized history**: stage `j + 1` is reached with indices `k'` iff stage `j` is
reached with `init k'`, it succeeds, and its least successful grid index is the last entry of `k'`. -/
theorem reachEv_succ (r : ℕ → ℕ) (j : ℕ) (k' : Fin (j + 1) → ℕ) :
    reachEv cand G hnL hnR y₀ R₀ 𝓑 r (j + 1) k' =
      reachEv cand G hnL hnR y₀ R₀ 𝓑 r j (Fin.init k') ∩
        succSet G hnL hnR j (histSys cand G hnL hnR y₀ R₀ 𝓑 r j) (r j) ∩
          {ω | swIdx G hnL hnR j (histSys cand G hnL hnR y₀ R₀ 𝓑 r j) (r j) ω = k' (Fin.last j)} := by
  ext ω
  have e : (hstate cand G hnL hnR y₀ R₀ 𝓑 r (j + 1)).hist ω = Fin.snoc (α := fun _ => ℕ)
      ((hstate cand G hnL hnR y₀ R₀ 𝓑 r j).hist ω)
      (swIdx G hnL hnR j (histSys cand G hnL hnR y₀ R₀ 𝓑 r j) (r j) ω) := rfl
  have eR : (hstate cand G hnL hnR y₀ R₀ 𝓑 r (j + 1)).R = (hstate cand G hnL hnR y₀ R₀ 𝓑 r j).R ∩
      succSet G hnL hnR j (histSys cand G hnL hnR y₀ R₀ 𝓑 r j) (r j) := rfl
  simp only [reachEv, mem_inter_iff, mem_ofPred_eq, e, eR, snoc_eq_iff]
  tauto

theorem reachEv_succ_subset (r : ℕ → ℕ) (j : ℕ) (k' : Fin (j + 1) → ℕ) :
    reachEv cand G hnL hnR y₀ R₀ 𝓑 r (j + 1) k' ⊆ succSet G hnL hnR j (histSys cand G hnL hnR y₀ R₀ 𝓑 r j) (r j) := by
  rw [reachEv_succ]
  exact fun ω h => h.1.2

end Reach

/-! ### The induction along the realized history -/

section Induction

variable {κ : ℝ} {Ω : Type*} {𝓑 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL₀ nR₀ : ℕ}
  {ρL₀ : Fin nL₀ → ℝ} {ρR₀ : Fin nR₀ → ℝ} {cand : CandFam Ω nL₀ nR₀} {G : ℕ → ℕ → ℝ≥0} {hnL : 0 < nL₀}
  {hnR : 0 < nR₀} {y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)} {R₀ : Set Ω}
  {𝓠c : (j : ℕ) → (Fin j → ℝ≥0) → MeasurableSpace Ω} {Rc : (j : ℕ) → (Fin j → ℝ≥0) → Set Ω}
  {yc : (j : ℕ) → (Fin j → ℝ≥0) → Ω → Start (nL₀ + j) (nR₀ + j)}

/-- **One switch, up to null sets.** If almost surely on `{stage j reached with indices k}` the realized start is the
candidate start, then (with `d` the candidate stage of the realized list) the trace of any set on
`{stage j + 1 reached with indices k'}`, jointly with a condition on the realized switching time and next start, is
a.e. its trace on `{stage j reached with init k'}` intersected with the candidate's switch event and condition. -/
theorem ae_step_eq (r : ℕ → ℕ) (j : ℕ) (k' : Fin (j + 1) → ℕ)
    (hi : ∀ᵐ ω ∂P, ω ∈ reachEv cand G hnL hnR y₀ R₀ 𝓑 r j (Fin.init k') →
      (hstate cand G hnL hnR y₀ R₀ 𝓑 r j).y ω = yc j (times G r (Fin.init k')) ω)
    (A : Set Ω) (S : Set (ℝ≥0 × Start (nL₀ + (j + 1)) (nR₀ + (j + 1)))) :
    A ∩ reachEv cand G hnL hnR y₀ R₀ 𝓑 r (j + 1) k' ∩
        {ω | (swT G hnL hnR j (histSys cand G hnL hnR y₀ R₀ 𝓑 r j) (r j) ω,
          nextStart G hnL hnR j (histSys cand G hnL hnR y₀ R₀ 𝓑 r j) (r j) ω) ∈ S} =ᵐ[P]
      A ∩ reachEv cand G hnL hnR y₀ R₀ 𝓑 r j (Fin.init k') ∩
        swEv G hnL hnR j (candStage cand yc j (times G r (Fin.init k'))) (r j) (k' (Fin.last j)) ∩
        {ω | (swT G hnL hnR j (candStage cand yc j (times G r (Fin.init k'))) (r j) ω,
          nextStart G hnL hnR j (candStage cand yc j (times G r (Fin.init k'))) (r j) ω) ∈ S} := by
  filter_upwards [hi] with ω hω
  rw [reachEv_succ]
  by_cases h0 : ω ∈ reachEv cand G hnL hnR y₀ R₀ 𝓑 r j (Fin.init k')
  · have hfrz := frz_stageOf_eq cand yc r (hstate cand G hnL hnR y₀ R₀ 𝓑 r j) h0.2 (hω h0)
    obtain ⟨hs, hidx, hT, hN⟩ := switch_congr_of_frz G hnL hnR j hfrz (r j)
    have e1 : histSys cand G hnL hnR y₀ R₀ 𝓑 r j = stageOf cand G r j (hstate cand G hnL hnR y₀ R₀ 𝓑 r j) := rfl
    rw [e1]
    simp only [swEv, mem_inter_iff, mem_ofPred_eq, hs, hidx, hT, hN, h0, true_and, and_true]
  · have h1 : ω ∉ reachEv cand G hnL hnR y₀ R₀ 𝓑 r j (Fin.init k') ∩
        succSet G hnL hnR j (histSys cand G hnL hnR y₀ R₀ 𝓑 r j) (r j) ∩
          {ω | swIdx G hnL hnR j (histSys cand G hnL hnR y₀ R₀ 𝓑 r j) (r j) ω = k' (Fin.last j)} :=
      fun h => h0 h.1.1
    refine propext ⟨fun h => absurd h.1.2 h1, fun h => absurd h.1.1.2 h0⟩

/-- **The invariant along the realized history.** Under `IsCandLawTree` and the root conditions, for every rule `r`,
depth `j` and realized indices `k`: (i) almost surely on `{stage j reached with indices k}`, the candidate event of
the realized list is reached and the realized start is the candidate start; (ii) every past event of the realized
stage, restricted to that event, agrees up to a null set with a past event of the candidate. -/
theorem inv_hstate (hT : IsCandLawTree κ P ρL₀ ρR₀ cand G hnL hnR 𝓠c Rc yc)
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
    obtain ⟨hi, hii⟩ := inv_hstate hT h𝓑 hR₀ hbase r j
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

/-- **The stage law of the adaptive construction from the candidate laws** (R73's (2.2) and the countable mixture):
if the candidates obey their stage laws along the tree of switching histories (`IsCandLawTree`), the root past `𝓑`
is contained in the root candidate's past, `R₀ ∈ 𝓑`, almost surely on `R₀` the root candidate's event is reached
with the root start, and the realized grid indices are measurable, then every stage of `histSys` obeys
`IsStageLaw` with the deterministic stage word. -/
theorem prop59StageLawStatement_histSys (hT : IsCandLawTree κ P ρL₀ ρR₀ cand G hnL hnR 𝓠c Rc yc)
    (h𝓑 : 𝓑 ≤ 𝓠c 0 Fin.elim0) (hR₀ : MeasurableSet[𝓑] R₀)
    (hbase : ∀ᵐ ω ∂P, ω ∈ R₀ → ω ∈ Rc 0 Fin.elim0 ∧ y₀ ω = yc 0 Fin.elim0 ω)
    (hhist : ∀ r j, Measurable (hstate cand G hnL hnR y₀ R₀ 𝓑 r j).hist) :
    Prop59StageLawStatement κ P ρL₀ ρR₀ (histSys cand G hnL hnR y₀ R₀ 𝓑) := by
  intro r j
  obtain ⟨hi, hii⟩ := inv_hstate hT h𝓑 hR₀ hbase r j
  refine isStageLaw_of_mix (hstate cand G hnL hnR y₀ R₀ 𝓑 r j).hist
    (fun k => hhist r j (measurableSet_singleton k)) (fun k => 𝓠c j (times G r k)) (fun k => Rc j (times G r k))
    (fun k => yc j (times G r k)) (fun k => (cand j (times G r k)).W) (fun k => (cand j (times G r k)).VL)
    (fun k => (cand j (times G r k)).VR) (fun k => (cand j (times G r k)).B) (fun k => (cand j (times G r k)).ζ)
    (fun k => hT.law j _) (fun k => hT.R_meas j _) ?_ ?_ ?_
  · intro k ω hk
    subst hk
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intro k
    filter_upwards [hi k] with ω h hR hk
    exact h ⟨hR, hk⟩
  · intro k A hA hAR
    obtain ⟨A', h1, h2⟩ := hii k A hA
    refine ⟨A', h1, EventuallyEqSet.trans (EventuallyEqSet.of_eq ?_) h2⟩
    ext ω
    simp only [reachEv, mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun h => ⟨h.1, hAR h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

/-- `prop59StageLawStatement_histSys` for a regular candidate family with a measurable root start (the realized grid
indices are then measurable, `Prop59System.measurable_hstate`). -/
theorem prop59StageLawStatement_histSys_of_reg (hT : IsCandLawTree κ P ρL₀ ρR₀ cand G hnL hnR 𝓠c Rc yc)
    (h𝓑 : 𝓑 ≤ 𝓠c 0 Fin.elim0) (hR₀ : MeasurableSet[𝓑] R₀)
    (hbase : ∀ᵐ ω ∂P, ω ∈ R₀ → ω ∈ Rc 0 Fin.elim0 ∧ y₀ ω = yc 0 Fin.elim0 ω) (hfam : IsRegFam cand)
    (hy₀ : Measurable y₀) : Prop59StageLawStatement κ P ρL₀ ρR₀ (histSys cand G hnL hnR y₀ R₀ 𝓑) :=
  prop59StageLawStatement_histSys hT h𝓑 hR₀ hbase fun r j => (measurable_hstate hfam hy₀ r j).2

end Induction

end InteractingSLE.Sec5.CrossCond.StagedAdapt
