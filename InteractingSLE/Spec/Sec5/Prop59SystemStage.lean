/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59SystemHist

/-!
# The structural facts of Proposition 5.9's alternating construction

Packet PROVE-PROP59T4. For the stage system `histSys` of the alternating construction along the countable tree of
switching histories (`Prop59SystemHist`), this file proves PROVE-PROP59T2's `IsStageSystem` from facts about the
**fixed** candidate pieces only (one piece per finite list of original switching times; no adaptive object appears in
the hypotheses):

* `IsRegPiece`, `IsRegFam`: every candidate has a jointly measurable driver and marks, a measurable lifetime, a
  continuous strictly increasing original clock (measurable at every time) and continuous paths before its lifetime;
* `IsChainFam`: every candidate comes with its absolute joint-chart chain (`drv`, `trc`, lifetime `life`) and the
  joint-chart capacity time `start` of its first point; the start of the piece launched at the switch of a candidate
  is that candidate's start plus the switch time (`step`); before its first far contact the chain lies in the closure of
  the node images (`trace`) — the source's "the realized prefix is one of the trajectories used to define the
  prescribed light cone" (p. 146).

## Main results

* `isRegStage_stageOf`: every realized stage is regular (`IsRegStage`), so its switching decisions are measurable;
* `capT_eq_start`: almost surely on the event that stage `j` is reached, the realized total capacity time of the
  first `j` stages is the start of the realized candidate;
* **`isStageSystem_histSys`**: `IsStageSystem` for `histSys`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop59System

open Prop59Stage

variable {Ω : Type*} {𝓑 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {nL₀ nR₀ : ℕ}

/-! ### Regular candidates -/

/-- **A regular candidate piece.** -/
structure IsRegPiece {nL nR : ℕ} (p : Piece Ω nL nR) : Prop where
  W : Measurable (Function.uncurry p.W)
  VL : ∀ i, Measurable (Function.uncurry (p.VL i))
  VR : ∀ k, Measurable (Function.uncurry (p.VR k))
  ζ : Measurable p.ζ
  clk : ∀ s, Measurable fun ω => p.clk ω s
  clk_cont : ∀ ω, Continuous (p.clk ω)
  clk_mono : ∀ ω, StrictMono (p.clk ω)
  W_cont : ∀ ω, ContinuousOn (p.W · ω) {u | (u : ℝ≥0∞) < p.ζ ω}
  VL_cont : ∀ ω i, ContinuousOn (p.VL i · ω) {u | (u : ℝ≥0∞) < p.ζ ω}
  VR_cont : ∀ ω k, ContinuousOn (p.VR k · ω) {u | (u : ℝ≥0∞) < p.ζ ω}

/-- **A regular candidate family.** -/
def IsRegFam (cand : CandFam Ω nL₀ nR₀) : Prop := ∀ j t, IsRegPiece (cand j t)

/-- A countable mixture of measurable maps is measurable. -/
theorem measurable_mix {ι β : Type*} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace β] {f : ι → Ω → β} (hf : ∀ k, Measurable (f k)) {h : Ω → ι} (hh : Measurable h) :
    Measurable fun ω => f (h ω) ω :=
  (measurable_from_prod_countable_left (f := fun p : Ω × ι => f p.2 p.1) hf).comp (measurable_id.prodMk hh)

/-- A countable mixture of jointly measurable processes is jointly measurable. -/
theorem measurable_mix_uncurry {ι β : Type*} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace β] {f : ι → ℝ≥0 → Ω → β} (hf : ∀ k, Measurable (Function.uncurry (f k))) {h : Ω → ι}
    (hh : Measurable h) : Measurable (Function.uncurry fun u ω => f (h ω) u ω) :=
  (measurable_from_prod_countable_left (f := fun p : (ℝ≥0 × Ω) × ι => f p.2 p.1.1 p.1.2) hf).comp
    (measurable_id.prodMk (hh.comp measurable_snd))

/-- The samples of jointly measurable processes with a measurable lifetime are measurable. -/
theorem measurable_samp_of_joint {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hW : Measurable (Function.uncurry W))
    (hVL : ∀ i, Measurable (Function.uncurry (VL i))) (hVR : ∀ k, Measurable (Function.uncurry (VR k)))
    (hζ : Measurable ζ) :
    Measurable fun ω => samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω) := by
  refine hζ.prodMk (measurable_pi_iff.2 fun q => ?_)
  have hlt : MeasurableSet {ω | ((q : ℝ≥0) : ℝ≥0∞) < ζ ω} := measurableSet_lt measurable_const hζ
  show Measurable fun ω => (if ((q : ℝ≥0) : ℝ≥0∞) < ζ ω then
      ((W q ω, fun i => VL i q ω, fun k => VR k q ω) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) else 0)
  exact Measurable.ite hlt (hW.of_uncurry_left.prodMk ((measurable_pi_iff.2 fun i => (hVL i).of_uncurry_left).prodMk
    (measurable_pi_iff.2 fun k => (hVR k).of_uncurry_left))) measurable_const

variable {cand : CandFam Ω nL₀ nR₀} {G : ℕ → ℕ → ℝ≥0} {hnL : 0 < nL₀} {hnR : 0 < nR₀}

/-- **Every realized stage is regular.** -/
theorem isRegStage_stageOf (hfam : IsRegFam cand) (r : ℕ → ℕ) {j : ℕ} {st : HState Ω nL₀ nR₀ j}
    (hy : Measurable st.y) (hh : Measurable st.hist) : IsRegStage hnL hnR j (stageOf cand G r j st) where
  y := hy
  W := measurable_mix_uncurry (fun k => (hfam j (times G r k)).W) hh
  VL i := measurable_mix_uncurry (fun k => (hfam j (times G r k)).VL i) hh
  VR k := measurable_mix_uncurry (fun k' => (hfam j (times G r k')).VR k) hh
  ζ := measurable_mix (fun k => (hfam j (times G r k)).ζ) hh
  clk s := measurable_mix (fun k => (hfam j (times G r k)).clk s) hh
  clk_cont ω := (hfam j (times G r (st.hist ω))).clk_cont ω
  clk_mono ω := (hfam j (times G r (st.hist ω))).clk_mono ω
  gap ω := by
    have hp := hfam j (times G r (st.hist ω))
    unfold farGap
    by_cases hj : Even j
    · simp only [hj, ↓reduceIte]
      exact (hp.W_cont ω).sub (hp.VL_cont ω _)
    · simp only [hj, ↓reduceIte]
      exact (hp.VR_cont ω _).sub (hp.W_cont ω)

variable {y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)} {R₀ : Set Ω}

/-- The realized starts and histories are measurable, and every realized stage is regular. -/
theorem measurable_hstate (hfam : IsRegFam cand) (hy₀ : Measurable y₀) (r : ℕ → ℕ) :
    ∀ j, Measurable (hstate cand G hnL hnR y₀ R₀ 𝓑 r j).y ∧ Measurable (hstate cand G hnL hnR y₀ R₀ 𝓑 r j).hist
  | 0 => ⟨hy₀, measurable_const⟩
  | j + 1 => by
    obtain ⟨hy, hh⟩ := measurable_hstate hfam hy₀ r j
    have hreg := isRegStage_stageOf (G := G) (hnL := hnL) (hnR := hnR) hfam r hy hh
    refine ⟨measurable_nextStart hreg (r j), measurable_pi_iff.2 fun i => ?_⟩
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · simp only [hstate_succ, HState.next, nextHist, Fin.snoc_last]
      exact measurable_swIdx hreg (r j)
    · simp only [hstate_succ, HState.next, nextHist, Fin.snoc_castSucc]
      exact (measurable_pi_apply i').comp hh

theorem isRegStage_histSys (hfam : IsRegFam cand) (hy₀ : Measurable y₀) (r : ℕ → ℕ) (j : ℕ) :
    IsRegStage hnL hnR j (histSys cand G hnL hnR y₀ R₀ 𝓑 r j) :=
  isRegStage_stageOf hfam r (measurable_hstate hfam hy₀ r j).1 (measurable_hstate hfam hy₀ r j).2

/-! ### Chain data -/

/-- **The chain data of a candidate family**: for every candidate its absolute joint-chart chain (driver `drv`, trace
`trc`, horizon `life`) and the capacity time `start` of its first point. The root candidate starts at `0`; the
candidate launched at the switch of a candidate at original time `q` (piece time `s`) starts at `start + s`; and
before its first far contact a candidate's chain lies in the closure of `C`. -/
structure IsChainFam (P : Measure Ω) (cand : CandFam Ω nL₀ nR₀) (hnL : 0 < nL₀) (hnR : 0 < nR₀) (C : Ω → Set ℂ)
    (start : (j : ℕ) → (Fin j → ℝ≥0) → Ω → ℝ) (drv : (j : ℕ) → (Fin j → ℝ≥0) → Ω → ℝ → ℝ)
    (trc : (j : ℕ) → (Fin j → ℝ≥0) → Ω → ℝ → ℂ) (life : (j : ℕ) → (Fin j → ℝ≥0) → Ω → ℝ) : Prop where
  start_zero : ∀ᵐ ω ∂P, start 0 Fin.elim0 ω = 0
  step : ∀ j (t : Fin j → ℝ≥0) (q : ℝ≥0), ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (cand j t).clk ω s = q →
    (s : ℝ≥0∞) < (cand j t).ζ ω → start (j + 1) (Fin.snoc (α := fun _ => ℝ≥0) t q) ω = start j t ω + s
  trace : ∀ j (t : Fin j → ℝ≥0), ∀ᵐ ω ∂P, Continuous (drv j t ω) ∧ drv j t ω 0 = 0 ∧
    IsLoewnerTraceLT (drv j t ω) (life j t ω) (trc j t ω) ∧
    ∀ s : ℝ≥0, (s : ℝ≥0∞) < (cand j t).ζ ω → (∀ u ≤ s, 0 < pGap hnL hnR j (cand j t) ω u) →
      start j t ω + s < life j t ω ∧ trc j t ω '' Icc 0 (start j t ω + s) ⊆ closure (C ω)

section Chain

variable {P : Measure Ω} {C : Ω → Set ℂ} {start : (j : ℕ) → (Fin j → ℝ≥0) → Ω → ℝ}
  {drv : (j : ℕ) → (Fin j → ℝ≥0) → Ω → ℝ → ℝ} {trc : (j : ℕ) → (Fin j → ℝ≥0) → Ω → ℝ → ℂ}
  {life : (j : ℕ) → (Fin j → ℝ≥0) → Ω → ℝ}

/-- On a successful stage the original clock at the switching time is the grid point of the switch. -/
theorem clk_swT_histSys (hfam : IsRegFam cand) (hy₀ : Measurable y₀) (r : ℕ → ℕ) (j : ℕ) {ω : Ω}
    (h : ω ∈ succSet G hnL hnR j (histSys cand G hnL hnR y₀ R₀ 𝓑 r j) (r j)) :
    (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).clk ω (swT G hnL hnR j (histSys cand G hnL hnR y₀ R₀ 𝓑 r j) (r j) ω) =
      G (r j) (swIdx G hnL hnR j (histSys cand G hnL hnR y₀ R₀ 𝓑 r j) (r j) ω) := by
  have hreg := isRegStage_histSys (G := G) (hnL := hnL) (hnR := hnR) (R₀ := R₀) (𝓑 := 𝓑) hfam hy₀ r j
  rw [swT_eq hreg h]
  exact clk_clkInv (swIdx_spec hreg h).1.1

/-- **The realized total capacity time is the start of the realized candidate.** -/
theorem capT_eq_start (hfam : IsRegFam cand) (hy₀ : Measurable y₀)
    (hch : IsChainFam P cand hnL hnR C start drv trc life) (r : ℕ → ℕ) :
    ∀ j, ∀ᵐ ω ∂P, ω ∈ (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).R →
      capT G hnL hnR (histSys cand G hnL hnR y₀ R₀ 𝓑) r j ω =
        start j (times G r ((hstate cand G hnL hnR y₀ R₀ 𝓑 r j).hist ω)) ω
  | 0 => by
    filter_upwards [hch.start_zero] with ω hω _
    have e : times G r ((hstate cand G hnL hnR y₀ R₀ 𝓑 r 0).hist ω) = Fin.elim0 := funext fun i => i.elim0
    rw [e, hω]
    simp only [capT, Finset.range_zero, Finset.sum_empty]
  | j + 1 => by
    have hst : ∀ᵐ ω ∂P, ∀ k : Fin j → ℕ, ∀ k' : ℕ, ∀ s : ℝ≥0,
        (cand j (times G r k)).clk ω s = G (r j) k' → (s : ℝ≥0∞) < (cand j (times G r k)).ζ ω →
        start (j + 1) (Fin.snoc (α := fun _ => ℝ≥0) (times G r k) (G (r j) k')) ω =
          start j (times G r k) ω + s := by
      rw [ae_all_iff]
      intro k
      rw [ae_all_iff]
      intro k'
      exact hch.step j (times G r k) (G (r j) k')
    filter_upwards [capT_eq_start hfam hy₀ hch r j, hst] with ω hω hst' hR
    have hRj : ω ∈ (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).R := hR.1
    have hsucc := hR.2
    have hsw := swT_spec hsucc
    rw [capT, Finset.sum_range_succ, ← capT, hω hRj, times_hist_succ]
    exact (hst' _ _ _ (clk_swT_histSys hfam hy₀ r j hsucc) hsw.1.1).symm

/-- **The tree link** (`IsStageSystem.chain`) from the chain data. -/
theorem chain_histSys (hfam : IsRegFam cand) (hy₀ : Measurable y₀)
    (hch : IsChainFam P cand hnL hnR C start drv trc life) (r : ℕ → ℕ) (j : ℕ) :
    ∀ᵐ ω ∂P, ω ∈ (histSys cand G hnL hnR y₀ R₀ 𝓑 r (j + 1)).R → ∃ (W' : ℝ → ℝ) (η : ℝ → ℂ) (T : ℝ),
      Continuous W' ∧ W' 0 = 0 ∧ IsLoewnerTraceLT W' T η ∧
      capT G hnL hnR (histSys cand G hnL hnR y₀ R₀ 𝓑) r (j + 1) ω < T ∧
      η '' Icc 0 (capT G hnL hnR (histSys cand G hnL hnR y₀ R₀ 𝓑) r (j + 1) ω) ⊆ closure (C ω) := by
  have htr : ∀ᵐ ω ∂P, ∀ k : Fin j → ℕ, Continuous (drv j (times G r k) ω) ∧ drv j (times G r k) ω 0 = 0 ∧
      IsLoewnerTraceLT (drv j (times G r k) ω) (life j (times G r k) ω) (trc j (times G r k) ω) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) < (cand j (times G r k)).ζ ω →
        (∀ u ≤ s, 0 < pGap hnL hnR j (cand j (times G r k)) ω u) →
        start j (times G r k) ω + s < life j (times G r k) ω ∧
          trc j (times G r k) ω '' Icc 0 (start j (times G r k) ω + s) ⊆ closure (C ω) := by
    rw [ae_all_iff]
    exact fun k => hch.trace j (times G r k)
  filter_upwards [capT_eq_start (G := G) (R₀ := R₀) (𝓑 := 𝓑) hfam hy₀ hch r j, htr] with ω hω htr' hR
  have hRj : ω ∈ (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).R := hR.1
  have hsw := swT_spec hR.2
  obtain ⟨hc, h0, hL, hs⟩ := htr' ((hstate cand G hnL hnR y₀ R₀ 𝓑 r j).hist ω)
  have he : capT G hnL hnR (histSys cand G hnL hnR y₀ R₀ 𝓑) r (j + 1) ω =
      start j (times G r ((hstate cand G hnL hnR y₀ R₀ 𝓑 r j).hist ω)) ω +
        (swT G hnL hnR j (histSys cand G hnL hnR y₀ R₀ 𝓑 r j) (r j) ω : ℝ) := by
    rw [capT, Finset.sum_range_succ, ← capT, hω hRj]
  obtain ⟨h1, h2⟩ := hs _ hsw.1.1 hsw.1.2.2
  exact ⟨_, _, _, hc, h0, hL, he ▸ h1, he ▸ h2⟩

end Chain

/-! ### The stage system -/

/-- **The structural facts of the alternating construction** (`IsStageSystem`) for the stage system along the tree of
switching histories, from the regularity and the chain data of the candidates, the grids, the initial start, reached
event and past, and the initial dilation. -/
theorem isStageSystem_histSys {P : Measure Ω} {Q : Set ℝ≥0} {δ : ℕ → ℝ≥0} {C : Ω → Set ℂ}
    {start : (j : ℕ) → (Fin j → ℝ≥0) → Ω → ℝ} {drv : (j : ℕ) → (Fin j → ℝ≥0) → Ω → ℝ → ℝ}
    {trc : (j : ℕ) → (Fin j → ℝ≥0) → Ω → ℝ → ℂ} {life : (j : ℕ) → (Fin j → ℝ≥0) → Ω → ℝ}
    (hfam : IsRegFam cand) (hgrid : ∀ n, IsSwitchGrid Q (δ n) (G n)) (hmesh : Tendsto δ atTop (𝓝 0))
    (hy₀ : Measurable y₀) (h𝓑 : 𝓑 ≤ mΩ) (hR₀ : MeasurableSet[𝓑] R₀)
    (hinit : ∀ᵐ ω ∂P, ω ∈ R₀ → (y₀ ω).1 = 0 ∧ (y₀ ω).1 + (y₀ ω).2.1 (farL (by omega : 0 < nL₀ + 0)) ≤ -3 ∧
      3 ≤ (y₀ ω).1 + (y₀ ω).2.2 (farR (by omega : 0 < nR₀ + 0)))
    (hch : IsChainFam P cand hnL hnR C start drv trc life) :
    IsStageSystem P hnL hnR Q δ G (histSys cand G hnL hnR y₀ R₀ 𝓑) C where
  grid := hgrid
  mesh := hmesh
  coh r r' j h := histSys_congr j h
  past_le := by
    intro r j
    induction j with
    | zero => exact h𝓑
    | succ j ih =>
      rw [histSys_past_succ]
      have hreg := isRegStage_histSys (G := G) (hnL := hnL) (hnR := hnR) (R₀ := R₀) (𝓑 := 𝓑) hfam hy₀ r j
      refine sup_le ih (sup_le (MeasurableSpace.generateFrom_le ?_) ?_)
      · rintro s (rfl | rfl)
        · exact measurableSet_succSet hreg (r j)
        · exact measurableSet_succ_one hreg (r j)
      · refine Measurable.comap_le ?_
        have hh := (measurable_hstate (G := G) (hnL := hnL) (hnR := hnR) (R₀ := R₀) (𝓑 := 𝓑) hfam hy₀ r
          (j + 1)).2
        have hy := (measurable_hstate (G := G) (hnL := hnL) (hnR := hnR) (R₀ := R₀) (𝓑 := 𝓑) hfam hy₀ r
          (j + 1)).1
        exact hh.prodMk hy
  past_mono r j := by
    rw [histSys_past_succ]
    exact le_sup_left
  R_meas := by
    intro r j
    induction j with
    | zero => exact hR₀
    | succ j ih =>
      rw [histSys_R_succ, histSys_past_succ]
      refine MeasurableSet.inter (le_sup_left (a := (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).past) _ ih) ?_
      refine (le_sup_left.trans le_sup_right :
        MeasurableSpace.generateFrom _ ≤ (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).past ⊔
          stepSigma G hnL hnR j (histSys cand G hnL hnR y₀ R₀ 𝓑 r j) (r j)
            (hstate cand G hnL hnR y₀ R₀ 𝓑 r j).hist) _ ?_
      exact MeasurableSpace.measurableSet_generateFrom (Or.inl rfl)
  R_succ r j := histSys_R_succ r j
  y_next r j := ae_of_all _ fun _ _ => rfl
  succ_meas r j := by
    have hle : MeasurableSpace.generateFrom {succSet G hnL hnR j (histSys cand G hnL hnR y₀ R₀ 𝓑 r j) (r j),
        {ω | ω ∈ succSet G hnL hnR j (histSys cand G hnL hnR y₀ R₀ 𝓑 r j) (r j) ∧
          (1 : ℝ≥0) ≤ swT G hnL hnR j (histSys cand G hnL hnR y₀ R₀ 𝓑 r j) (r j) ω}} ≤
        (histSys cand G hnL hnR y₀ R₀ 𝓑 r (j + 1)).past := by
      rw [histSys_past_succ]
      exact le_sup_left.trans le_sup_right
    exact ⟨hle _ (MeasurableSpace.measurableSet_generateFrom (Or.inl rfl)),
      hle _ (MeasurableSpace.measurableSet_generateFrom (Or.inr rfl))⟩
  meas r j := by
    have hreg := isRegStage_histSys (G := G) (hnL := hnL) (hnR := hnR) (R₀ := R₀) (𝓑 := 𝓑) hfam hy₀ r j
    exact ⟨hreg.y, measurable_samp_of_joint hreg.W hreg.VL hreg.VR hreg.ζ⟩
  clk r j := ae_of_all _ fun ω _ =>
    ⟨(isRegStage_histSys (G := G) (hnL := hnL) (hnR := hnR) (R₀ := R₀) (𝓑 := 𝓑) hfam hy₀ r j).clk_cont ω,
      (isRegStage_histSys (G := G) (hnL := hnL) (hnR := hnR) (R₀ := R₀) (𝓑 := 𝓑) hfam hy₀ r j).clk_mono ω⟩
  init r := hinit
  chain r j := chain_histSys hfam hy₀ hch r j

end InteractingSLE.Sec5.Prop59System
