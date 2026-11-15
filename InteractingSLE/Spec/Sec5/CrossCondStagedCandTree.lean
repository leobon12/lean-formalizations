/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedAdaptTree

/-!
# Proposition 5.9: the canonical candidate tree (starts, reached events and pasts of the fixed candidates)

Packet PROVE-STAGED7 (R73: Astra's follow-up 5, §2.3 and the correction L8–L14). PROVE-STAGED6 reduced
`Prop59StageLawStatement` for PROVE-PROP59T4's adaptive construction `histSys` to `IsCandLawTree`: a stage law for
every **fixed** candidate `cand j t` (with a past `𝓠c j t`, a reached event `Rc j t` and a start `yc j t`) and the
consistency of these data at the switches. This file constructs the data canonically, for **every** regular candidate
family, and proves the consistency, so that only the per-candidate laws remain:

* `canonY`: the candidate starts — the root start, and at a switch at the original time `q` the next-start formula
  of the parent candidate at the piece time where its clock reads `q` (one new mark on each side at the driver);
* `canonR`: the reached events — the root event, then the parent's event intersected with the event that the parent
  switches at `q` for some grid `G n` (`swEv … n m` with `G n m = q`);
* `canonQ`: the pasts — the root past, then the parent's past joined with the **switch σ-algebra** `swSigma` at `q`
  (the traces on the switch events at `q` of the switching time and the next start). These are the revealed
  histories of Proposition 5.9 along a fixed list of switching times: the base, and each earlier piece read up to its
  switch.

Main results: `isCandTree_canon` (the tree consistency clauses of `IsCandLawTree`, at every sample) and
**`prop59StageLawStatement_histSys_canon`**: `Prop59StageLawStatement` for `histSys` from the per-candidate stage
laws `IsStageLaw … (canonQ … j t) (canonR … j t) … (canonY … j t) (cand j t)…` alone.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedCand

open Prop59Stage Prop59System StagedAdapt

/-! ### The canonical starts -/

section Starts

variable {Ω : Type*} {nL₀ nR₀ : ℕ}

/-- **The start after a switch at the piece time `s`**: the absolute driver at `s`, and the relative positions at
`s` with one new mark on each side at the driver (index `0`) — PROVE-PROP59T2's `nextStart` formula at a given time. -/
def startAt (j : ℕ) (d : StageData Ω (nL₀ + j) (nR₀ + j)) (s : Ω → ℝ≥0) (ω : Ω) :
    Start (nL₀ + (j + 1)) (nR₀ + (j + 1)) :=
  ((d.y ω).1 + d.W (s ω) ω, Fin.cons 0 fun i => d.VL i (s ω) ω - d.W (s ω) ω,
    Fin.cons 0 fun k => d.VR k (s ω) ω - d.W (s ω) ω)

theorem nextStart_eq_startAt [MeasurableSpace Ω] (G : ℕ → ℕ → ℝ≥0) (hnL : 0 < nL₀) (hnR : 0 < nR₀) (j : ℕ)
    (d : StageData Ω (nL₀ + j) (nR₀ + j)) (n : ℕ) :
    nextStart G hnL hnR j d n = startAt j d (swT G hnL hnR j d n) := rfl

/-- **The canonical candidate starts**: `y₀` at the root; after the switch of the list `t` at the original time `q`,
the start formula of the candidate stage of `t` at the piece time where its clock reads `q`. -/
def canonY (cand : CandFam Ω nL₀ nR₀) (y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)) :
    (j : ℕ) → (Fin j → ℝ≥0) → Ω → Start (nL₀ + j) (nR₀ + j)
  | 0, _ => y₀
  | j + 1, t => startAt j ((cand j (Fin.init t)).toStage ⊥ ∅ (canonY cand y₀ j (Fin.init t)))
      (clkInv ((cand j (Fin.init t)).toStage ⊥ ∅ fun _ => 0) (t (Fin.last j)))

theorem canonY_zero (cand : CandFam Ω nL₀ nR₀) (y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)) (t : Fin 0 → ℝ≥0) :
    canonY cand y₀ 0 t = y₀ := rfl

theorem canonY_snoc (cand : CandFam Ω nL₀ nR₀) (y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)) (j : ℕ) (t : Fin j → ℝ≥0)
    (q : ℝ≥0) :
    canonY cand y₀ (j + 1) (Fin.snoc (α := fun _ => ℝ≥0) t q) =
      startAt j (candStage cand (canonY cand y₀) j t) (clkInv ((cand j t).toStage ⊥ ∅ fun _ => 0) q) := by
  simp only [canonY, Fin.init_snoc, Fin.snoc_last]
  rfl

/-- The clock inverse sees only the clock. -/
theorem clkInv_candStage (cand : CandFam Ω nL₀ nR₀) (yc : (j : ℕ) → (Fin j → ℝ≥0) → Ω → Start (nL₀ + j) (nR₀ + j))
    (j : ℕ) (t : Fin j → ℝ≥0) (q : ℝ≥0) :
    clkInv (candStage cand yc j t) q = clkInv ((cand j t).toStage ⊥ ∅ fun _ => 0) q := rfl

end Starts

/-! ### Regularity of the candidate stages -/

section RegStage

variable {Ω : Type*} {nL₀ nR₀ : ℕ}

/-- A regular piece with a measurable start is a regular stage. -/
theorem isRegStage_toStage {past : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {hnL : 0 < nL₀} {hnR : 0 < nR₀}
    {j : ℕ} {p : Piece Ω (nL₀ + j) (nR₀ + j)} (hp : IsRegPiece p) {R : Set Ω} {y : Ω → Start (nL₀ + j) (nR₀ + j)}
    (hy : Measurable y) : IsRegStage hnL hnR j (p.toStage past R y) where
  y := hy
  W := hp.W
  VL := hp.VL
  VR := hp.VR
  ζ := hp.ζ
  clk := hp.clk
  clk_cont := hp.clk_cont
  clk_mono := hp.clk_mono
  gap ω := by
    unfold farGap
    by_cases hj : Even j
    · simp only [hj, ↓reduceIte]
      exact (hp.W_cont ω).sub (hp.VL_cont ω _)
    · simp only [hj, ↓reduceIte]
      exact (hp.VR_cont ω _).sub (hp.W_cont ω)

end RegStage

section Reg

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL₀ nR₀ : ℕ}

/-- The start formula at a measurable time of a regular stage is measurable. -/
theorem measurable_startAt {j : ℕ} {d : StageData Ω (nL₀ + j) (nR₀ + j)} (hy : Measurable d.y)
    (hW : Measurable (Function.uncurry d.W)) (hVL : ∀ i, Measurable (Function.uncurry (d.VL i)))
    (hVR : ∀ k, Measurable (Function.uncurry (d.VR k))) {s : Ω → ℝ≥0} (hs : Measurable s) :
    Measurable (startAt j d s) := by
  have hpair : Measurable fun ω => (s ω, ω) := hs.prodMk measurable_id
  have hW' : Measurable fun ω => d.W (s ω) ω := hW.comp hpair
  refine ((measurable_fst.comp hy).add hW').prodMk ((measurable_pi_iff.2 fun i => ?_).prodMk
    (measurable_pi_iff.2 fun k => ?_))
  · refine Fin.cases ?_ (fun i => ?_) i
    · exact measurable_const
    · exact ((hVL i).comp hpair).sub hW'
  · refine Fin.cases ?_ (fun k => ?_) k
    · exact measurable_const
    · exact ((hVR k).comp hpair).sub hW'

/-- **The canonical starts are measurable** for a regular family with a measurable root start. -/
theorem measurable_canonY {cand : CandFam Ω nL₀ nR₀} (hfam : IsRegFam cand) {y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)}
    (hy₀ : Measurable y₀) : ∀ j t, Measurable (canonY cand y₀ j t)
  | 0, _ => hy₀
  | j + 1, t => by
    have hp := hfam j (Fin.init t)
    have hd : ∀ ω, Continuous (((cand j (Fin.init t)).toStage ⊥ ∅ fun _ => 0).clk ω) ∧
        StrictMono (((cand j (Fin.init t)).toStage ⊥ ∅ fun _ => 0).clk ω) :=
      fun ω => ⟨hp.clk_cont ω, hp.clk_mono ω⟩
    exact measurable_startAt (measurable_canonY hfam hy₀ j (Fin.init t)) hp.W hp.VL hp.VR
      (measurable_clkInv hd hp.clk _)

theorem isRegStage_candStage {cand : CandFam Ω nL₀ nR₀} (hfam : IsRegFam cand) {hnL : 0 < nL₀} {hnR : 0 < nR₀}
    {y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)} (hy₀ : Measurable y₀) (j : ℕ) (t : Fin j → ℝ≥0) :
    IsRegStage hnL hnR j (candStage cand (canonY cand y₀) j t) :=
  isRegStage_toStage (hfam j t) (measurable_canonY hfam hy₀ j t)

end Reg

/-! ### The canonical reached events and pasts -/

section Tree

variable {Ω : Type*} (𝓑 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {nL₀ nR₀ : ℕ}

/-- **The switch σ-algebra at the original time `q`**: generated by the traces, on the events `swEv … n m` that the
stage `d` switches at the grid point `G n m = q`, of Borel conditions on the switching time and the next start. -/
@[instance_reducible]
def swSigma (G : ℕ → ℕ → ℝ≥0) (hnL : 0 < nL₀) (hnR : 0 < nR₀) (j : ℕ) (d : StageData Ω (nL₀ + j) (nR₀ + j))
    (q : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom {B | ∃ (n m : ℕ) (S : Set (ℝ≥0 × Start (nL₀ + (j + 1)) (nR₀ + (j + 1)))),
    G n m = q ∧ MeasurableSet S ∧
      B = swEv G hnL hnR j d n m ∩ {ω | (swT G hnL hnR j d n ω, nextStart G hnL hnR j d n ω) ∈ S}}

/-- **The canonical candidate pasts**: `𝓑` at the root; after the switch of `t` at `q`, the past of `t` joined with
the switch σ-algebra of the candidate stage of `t` at `q`. -/
@[instance_reducible]
def canonQ (cand : CandFam Ω nL₀ nR₀) (G : ℕ → ℕ → ℝ≥0) (hnL : 0 < nL₀) (hnR : 0 < nR₀)
    (y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)) : (j : ℕ) → (Fin j → ℝ≥0) → MeasurableSpace Ω
  | 0, _ => 𝓑
  | j + 1, t => canonQ cand G hnL hnR y₀ j (Fin.init t) ⊔
      swSigma G hnL hnR j (candStage cand (canonY cand y₀) j (Fin.init t)) (t (Fin.last j))

/-- **The canonical reached events**: `R₀` at the root; after `t` the switch at `q` for some grid. -/
def canonR (cand : CandFam Ω nL₀ nR₀) (G : ℕ → ℕ → ℝ≥0) (hnL : 0 < nL₀) (hnR : 0 < nR₀)
    (y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)) (R₀ : Set Ω) : (j : ℕ) → (Fin j → ℝ≥0) → Set Ω
  | 0, _ => R₀
  | j + 1, t => canonR cand G hnL hnR y₀ R₀ j (Fin.init t) ∩
      ⋃ (n : ℕ) (m : ℕ) (_ : G n m = t (Fin.last j)),
        swEv G hnL hnR j (candStage cand (canonY cand y₀) j (Fin.init t)) n m

variable {𝓑} {cand : CandFam Ω nL₀ nR₀} {G : ℕ → ℕ → ℝ≥0} {hnL : 0 < nL₀} {hnR : 0 < nR₀}
  {y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)} {R₀ : Set Ω}

omit mΩ in
theorem canonQ_snoc (j : ℕ) (t : Fin j → ℝ≥0) (q : ℝ≥0) :
    canonQ 𝓑 cand G hnL hnR y₀ (j + 1) (Fin.snoc (α := fun _ => ℝ≥0) t q) =
      canonQ 𝓑 cand G hnL hnR y₀ j t ⊔ swSigma G hnL hnR j (candStage cand (canonY cand y₀) j t) q := by
  simp only [canonQ, Fin.init_snoc, Fin.snoc_last]

omit mΩ in
theorem canonR_snoc (j : ℕ) (t : Fin j → ℝ≥0) (q : ℝ≥0) :
    canonR cand G hnL hnR y₀ R₀ (j + 1) (Fin.snoc (α := fun _ => ℝ≥0) t q) =
      canonR cand G hnL hnR y₀ R₀ j t ∩
        ⋃ (n : ℕ) (m : ℕ) (_ : G n m = q), swEv G hnL hnR j (candStage cand (canonY cand y₀) j t) n m := by
  simp only [canonR, Fin.init_snoc, Fin.snoc_last]

omit mΩ in
/-- The switch events at `q` are switch-σ-algebra events. -/
theorem measurableSet_swSigma_swEv {j : ℕ} (d : StageData Ω (nL₀ + j) (nR₀ + j)) {n m : ℕ} :
    MeasurableSet[swSigma G hnL hnR j d (G n m)] (swEv G hnL hnR j d n m) := by
  refine MeasurableSpace.measurableSet_generateFrom ⟨n, m, univ, rfl, MeasurableSet.univ, ?_⟩
  ext ω
  simp only [mem_inter_iff, mem_univ, mem_ofPred_eq, and_true]

omit mΩ in
/-- The traces of the switch data on a switch event at `q` are switch-σ-algebra events. -/
theorem measurableSet_swSigma {j : ℕ} (d : StageData Ω (nL₀ + j) (nR₀ + j)) {n m : ℕ}
    {S : Set (ℝ≥0 × Start (nL₀ + (j + 1)) (nR₀ + (j + 1)))} (hS : MeasurableSet S) :
    MeasurableSet[swSigma G hnL hnR j d (G n m)]
      (swEv G hnL hnR j d n m ∩ {ω | (swT G hnL hnR j d n ω, nextStart G hnL hnR j d n ω) ∈ S}) :=
  MeasurableSpace.measurableSet_generateFrom ⟨n, m, S, rfl, hS, rfl⟩

omit mΩ in
/-- **The canonical reached events are past events.** -/
theorem measurableSet_canonR (hR₀ : MeasurableSet[𝓑] R₀) :
    ∀ j t, MeasurableSet[canonQ 𝓑 cand G hnL hnR y₀ j t] (canonR cand G hnL hnR y₀ R₀ j t)
  | 0, _ => hR₀
  | j + 1, t => by
    rw [← Fin.snoc_init_self t, canonQ_snoc, canonR_snoc]
    refine MeasurableSet.inter (le_sup_left (a := canonQ 𝓑 cand G hnL hnR y₀ j (Fin.init t)) _
      (measurableSet_canonR hR₀ j (Fin.init t))) ?_
    refine @MeasurableSet.iUnion Ω _ _ _ _ fun n => @MeasurableSet.iUnion Ω _ _ _ _ fun m =>
      @MeasurableSet.iUnion Ω _ _ _ _ fun hnm => ?_
    refine le_sup_right (a := canonQ 𝓑 cand G hnL hnR y₀ j (Fin.init t)) _ ?_
    rw [← hnm]
    exact measurableSet_swSigma_swEv _

/-- **The tree consistency at a switch, at every sample**: on the canonical event of `t` and the event that the
candidate stage of `t` switches at the grid point `G n m`, the child's canonical event is reached and the next start
is the child's canonical start (the switching time is the clock inverse at `G n m`, `swT_eq`). -/
theorem canon_step_start (hfam : IsRegFam cand) (hy₀ : Measurable y₀) (j : ℕ) (t : Fin j → ℝ≥0) (n m : ℕ)
    {ω : Ω} (hR : ω ∈ canonR cand G hnL hnR y₀ R₀ j t)
    (hsw : ω ∈ swEv G hnL hnR j (candStage cand (canonY cand y₀) j t) n m) :
    ω ∈ canonR cand G hnL hnR y₀ R₀ (j + 1) (Fin.snoc (α := fun _ => ℝ≥0) t (G n m)) ∧
      nextStart G hnL hnR j (candStage cand (canonY cand y₀) j t) n ω =
        canonY cand y₀ (j + 1) (Fin.snoc (α := fun _ => ℝ≥0) t (G n m)) ω := by
  refine ⟨?_, ?_⟩
  · rw [canonR_snoc]
    exact ⟨hR, mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨m, mem_iUnion.2 ⟨rfl, hsw⟩⟩⟩⟩
  · have hr := isRegStage_candStage (hnL := hnL) (hnR := hnR) hfam hy₀ j t
    have e := swT_eq (G := G) hr hsw.1
    have hidx : swIdx G hnL hnR j (candStage cand (canonY cand y₀) j t) n ω = m := hsw.2
    rw [hidx] at e
    rw [canonY_snoc, nextStart_eq_startAt]
    unfold startAt
    rw [e]
    rfl

end Tree

/-! ### The adaptive stage law from the per-candidate laws -/

section Law

variable {κ : ℝ} {Ω : Type*} {𝓑 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL₀ nR₀ : ℕ}
  {ρL₀ : Fin nL₀ → ℝ} {ρR₀ : Fin nR₀ → ℝ} {cand : CandFam Ω nL₀ nR₀} {G : ℕ → ℕ → ℝ≥0} {hnL : 0 < nL₀}
  {hnR : 0 < nR₀} {y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)} {R₀ : Set Ω}

/-- **The canonical candidate tree is consistent**: PROVE-STAGED6's `IsCandLawTree` for the canonical pasts, events
and starts, from the per-candidate stage laws alone. -/
theorem isCandLawTree_canon (hfam : IsRegFam cand) (hy₀ : Measurable y₀) (hR₀ : MeasurableSet[𝓑] R₀)
    (hlaw : ∀ j t, IsStageLaw κ P (canonQ 𝓑 cand G hnL hnR y₀ j t) (canonR cand G hnL hnR y₀ R₀ j t)
      (stageρL κ ρL₀ j) (stageρR κ ρR₀ j) (canonY cand y₀ j t) (cand j t).W (cand j t).VL (cand j t).VR
      (cand j t).B (cand j t).ζ) :
    IsCandLawTree κ P ρL₀ ρR₀ cand G hnL hnR (canonQ 𝓑 cand G hnL hnR y₀) (canonR cand G hnL hnR y₀ R₀)
      (canonY cand y₀) where
  law := hlaw
  R_meas := measurableSet_canonR hR₀
  step_meas j t n m A hA S hS := by
    rw [canonQ_snoc, inter_assoc]
    exact (le_sup_left (a := canonQ 𝓑 cand G hnL hnR y₀ j t) _ hA).inter
      (le_sup_right (a := canonQ 𝓑 cand G hnL hnR y₀ j t) _ (measurableSet_swSigma _ hS))
  step_start j t n m := Eventually.of_forall fun _ hR hsw => canon_step_start hfam hy₀ j t n m hR hsw

/-- **`Prop59StageLawStatement` for the adaptive construction from the per-candidate stage laws** (R73 (2.2) and
the countable mixture, PROVE-STAGED6, with the canonical candidate tree): if every fixed candidate `cand j t` obeys
`IsStageLaw` with the deterministic stage word for its canonical past, reached event and start, then every stage
of `histSys cand G … y₀ R₀ 𝓑` does. -/
theorem prop59StageLawStatement_histSys_canon (hfam : IsRegFam cand) (hy₀ : Measurable y₀)
    (hR₀ : MeasurableSet[𝓑] R₀)
    (hlaw : ∀ j t, IsStageLaw κ P (canonQ 𝓑 cand G hnL hnR y₀ j t) (canonR cand G hnL hnR y₀ R₀ j t)
      (stageρL κ ρL₀ j) (stageρR κ ρR₀ j) (canonY cand y₀ j t) (cand j t).W (cand j t).VL (cand j t).VR
      (cand j t).B (cand j t).ζ) :
    Prop59StageLawStatement κ P ρL₀ ρR₀ (histSys cand G hnL hnR y₀ R₀ 𝓑) :=
  prop59StageLawStatement_histSys_of_reg (isCandLawTree_canon hfam hy₀ hR₀ hlaw) le_rfl hR₀
    (Eventually.of_forall fun _ h => ⟨h, rfl⟩) hfam hy₀

end Law

end InteractingSLE.Sec5.CrossCond.StagedCand
