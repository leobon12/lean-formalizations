/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59SystemCand

/-!
# The tree link of Proposition 5.9's alternating construction, per switch

Packet PROVE-PROP59-PIECES. PROVE-PROP59T4's chain data `IsChainFam` ask, for every candidate piece, for **one**
continuous driver on `ℝ` and one real horizon `life` beyond every admissible switch of the candidate. For the
concrete candidates (pieces read through killed arcs, `Prop59PiecesArc`) this cannot be supplied: a piece whose
first new contact never happens has an infinite lifetime, so no real horizon lies beyond all its switches, and at a
finite first contact the driver need not extend continuously. What `IsStageSystem.chain` consumes is weaker: for the
realized switch only, *some* Loewner trace of a continuous driver covers the realized prefix inside the closure of
the node images. This file states the chain data in that per-switch form and proves `IsStageSystem` from it.

* `candInv`: the piece time at which a candidate's original clock reaches `q` (PROVE-PROP59T4's `clkInv`);
* `recStart`: the start capacities defined recursively along the tree, `recStart (j+1) t = recStart j (init t) +
  candInv j (init t) (t last)`; its `step` clause holds at every sample (`recStart_step`);
* `IsChainFamEx`: the chain data with the trace clause per switch (existential driver and horizon);
* `isChainFamEx_of_trace`: the recursive start satisfies `start_zero` and `step`, so only the trace clause remains;
* **`isStageSystem_histSys_ex`**: `IsStageSystem` for PROVE-PROP59T4's `histSys` from `IsChainFamEx`;
* `CandExpEx`, **`CandExpEx.toProdExp`**, **`prop513_path_of_partA_reverseVisit_candExpEx`**: PROVE-PROP59T4's
  experiments from candidate families with per-switch chain data, and Proposition 5.13's measurable path from them.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop59Pieces

open Prop59System Prop59Stage

/-! ### The recursive start -/

section Start

variable {Ω : Type*} {nL₀ nR₀ : ℕ}

/-- The piece time at which the original clock of the candidate `(j, t)` reaches `q`. -/
def candInv (cand : CandFam Ω nL₀ nR₀) (j : ℕ) (t : Fin j → ℝ≥0) (q : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  clkInv ((cand j t).toStage ⊥ ∅ fun _ => 0) q ω

/-- **The start capacities along the tree**: `0` at the root; the start of the candidate switched at `q` after `t`
is the start of `t` plus the piece time at which the clock of `t` reaches `q`. -/
def recStart (cand : CandFam Ω nL₀ nR₀) : (j : ℕ) → (Fin j → ℝ≥0) → Ω → ℝ
  | 0, _, _ => 0
  | j + 1, t, ω => recStart cand j (Fin.init t) ω + candInv cand j (Fin.init t) (t (Fin.last j)) ω

theorem recStart_snoc (cand : CandFam Ω nL₀ nR₀) (j : ℕ) (t : Fin j → ℝ≥0) (q : ℝ≥0) (ω : Ω) :
    recStart cand (j + 1) (Fin.snoc (α := fun _ => ℝ≥0) t q) ω =
      recStart cand j t ω + candInv cand j t q ω := by
  simp only [recStart, Fin.init_snoc, Fin.snoc_last]

/-- **The step clause of the recursive start holds at every sample.** -/
theorem recStart_step {cand : CandFam Ω nL₀ nR₀} (hmono : ∀ j t ω, StrictMono ((cand j t).clk ω)) (j : ℕ)
    (t : Fin j → ℝ≥0) (q : ℝ≥0) (ω : Ω) (s : ℝ≥0) (hs : (cand j t).clk ω s = q) :
    recStart cand (j + 1) (Fin.snoc (α := fun _ => ℝ≥0) t q) ω = recStart cand j t ω + s := by
  rw [recStart_snoc]
  congr 1
  exact congrArg _ (eq_clkInv (d := (cand j t).toStage ⊥ ∅ fun _ => 0) (hmono j t ω) hs).symm

end Start

/-! ### Chain data per switch -/

section Chain

variable {Ω : Type*} {𝓑 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {nL₀ nR₀ : ℕ}

/-- **Chain data of a candidate family, per switch**: the start capacities `start`, the root starts at `0`, a switch
of the candidate `t` at original time `q` (piece time `s`) starts the next candidate at `start + s`, and before its
first far contact a candidate's prefix through `start + s` is covered by a Loewner trace inside the closure of `C`. -/
structure IsChainFamEx (P : Measure Ω) (cand : CandFam Ω nL₀ nR₀) (hnL : 0 < nL₀) (hnR : 0 < nR₀)
    (C : Ω → Set ℂ) (start : (j : ℕ) → (Fin j → ℝ≥0) → Ω → ℝ) : Prop where
  start_zero : ∀ᵐ ω ∂P, start 0 Fin.elim0 ω = 0
  step : ∀ j (t : Fin j → ℝ≥0) (q : ℝ≥0), ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (cand j t).clk ω s = q →
    (s : ℝ≥0∞) < (cand j t).ζ ω → start (j + 1) (Fin.snoc (α := fun _ => ℝ≥0) t q) ω = start j t ω + s
  trace : ∀ j (t : Fin j → ℝ≥0), ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) < (cand j t).ζ ω →
    (∀ u ≤ s, 0 < pGap hnL hnR j (cand j t) ω u) →
      ∃ (W' : ℝ → ℝ) (η : ℝ → ℂ) (T : ℝ), Continuous W' ∧ W' 0 = 0 ∧ IsLoewnerTraceLT W' T η ∧
        start j t ω + s < T ∧ η '' Icc 0 (start j t ω + s) ⊆ closure (C ω)

/-- **The recursive start gives the bookkeeping clauses**; only the trace clause remains. -/
theorem isChainFamEx_of_trace {P : Measure Ω} {cand : CandFam Ω nL₀ nR₀} {hnL : 0 < nL₀} {hnR : 0 < nR₀}
    {C : Ω → Set ℂ} (hmono : ∀ j t ω, StrictMono ((cand j t).clk ω))
    (htr : ∀ j (t : Fin j → ℝ≥0), ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) < (cand j t).ζ ω →
      (∀ u ≤ s, 0 < pGap hnL hnR j (cand j t) ω u) →
        ∃ (W' : ℝ → ℝ) (η : ℝ → ℂ) (T : ℝ), Continuous W' ∧ W' 0 = 0 ∧ IsLoewnerTraceLT W' T η ∧
          recStart cand j t ω + s < T ∧ η '' Icc 0 (recStart cand j t ω + s) ⊆ closure (C ω)) :
    IsChainFamEx P cand hnL hnR C (recStart cand) where
  start_zero := ae_of_all _ fun _ => rfl
  step j t q := ae_of_all _ fun ω s hs _ => recStart_step hmono j t q ω s hs
  trace := htr

variable {cand : CandFam Ω nL₀ nR₀} {G : ℕ → ℕ → ℝ≥0} {hnL : 0 < nL₀} {hnR : 0 < nR₀}
  {y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)} {R₀ : Set Ω} {P : Measure Ω} {C : Ω → Set ℂ}
  {start : (j : ℕ) → (Fin j → ℝ≥0) → Ω → ℝ}

/-- The realized total capacity time is the start of the realized candidate (per-switch chain data). -/
theorem capT_eq_start_ex (hfam : IsRegFam cand) (hy₀ : Measurable y₀)
    (hch : IsChainFamEx P cand hnL hnR C start) (r : ℕ → ℕ) :
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
    filter_upwards [capT_eq_start_ex hfam hy₀ hch r j, hst] with ω hω hst' hR
    have hRj : ω ∈ (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).R := hR.1
    have hsucc := hR.2
    have hsw := swT_spec hsucc
    rw [capT, Finset.sum_range_succ, ← capT, hω hRj, times_hist_succ]
    exact (hst' _ _ _ (clk_swT_histSys hfam hy₀ r j hsucc) hsw.1.1).symm

/-- **The tree link** (`IsStageSystem.chain`) from per-switch chain data. -/
theorem chain_histSys_ex (hfam : IsRegFam cand) (hy₀ : Measurable y₀)
    (hch : IsChainFamEx P cand hnL hnR C start) (r : ℕ → ℕ) (j : ℕ) :
    ∀ᵐ ω ∂P, ω ∈ (histSys cand G hnL hnR y₀ R₀ 𝓑 r (j + 1)).R → ∃ (W' : ℝ → ℝ) (η : ℝ → ℂ) (T : ℝ),
      Continuous W' ∧ W' 0 = 0 ∧ IsLoewnerTraceLT W' T η ∧
      capT G hnL hnR (histSys cand G hnL hnR y₀ R₀ 𝓑) r (j + 1) ω < T ∧
      η '' Icc 0 (capT G hnL hnR (histSys cand G hnL hnR y₀ R₀ 𝓑) r (j + 1) ω) ⊆ closure (C ω) := by
  have htr : ∀ᵐ ω ∂P, ∀ k : Fin j → ℕ, ∀ s : ℝ≥0, (s : ℝ≥0∞) < (cand j (times G r k)).ζ ω →
      (∀ u ≤ s, 0 < pGap hnL hnR j (cand j (times G r k)) ω u) →
        ∃ (W' : ℝ → ℝ) (η : ℝ → ℂ) (T : ℝ), Continuous W' ∧ W' 0 = 0 ∧ IsLoewnerTraceLT W' T η ∧
          start j (times G r k) ω + s < T ∧ η '' Icc 0 (start j (times G r k) ω + s) ⊆ closure (C ω) := by
    rw [ae_all_iff]
    exact fun k => hch.trace j (times G r k)
  filter_upwards [capT_eq_start_ex (G := G) (R₀ := R₀) (𝓑 := 𝓑) hfam hy₀ hch r j, htr] with ω hω htr' hR
  have hRj : ω ∈ (histSys cand G hnL hnR y₀ R₀ 𝓑 r j).R := hR.1
  have hsw := swT_spec hR.2
  have he : capT G hnL hnR (histSys cand G hnL hnR y₀ R₀ 𝓑) r (j + 1) ω =
      start j (times G r ((hstate cand G hnL hnR y₀ R₀ 𝓑 r j).hist ω)) ω +
        (swT G hnL hnR j (histSys cand G hnL hnR y₀ R₀ 𝓑 r j) (r j) ω : ℝ) := by
    rw [capT, Finset.sum_range_succ, ← capT, hω hRj]
  obtain ⟨W', η, T, hc, h0, hL, h1, h2⟩ := htr' ((hstate cand G hnL hnR y₀ R₀ 𝓑 r j).hist ω) _ hsw.1.1 hsw.1.2.2
  exact ⟨W', η, T, hc, h0, hL, he ▸ h1, he ▸ h2⟩

/-- **The structural facts of the alternating construction** (`IsStageSystem`) for `histSys`, from the regularity
and the per-switch chain data of the candidates. -/
theorem isStageSystem_histSys_ex {Q : Set ℝ≥0} {δ : ℕ → ℝ≥0}
    (hfam : IsRegFam cand) (hgrid : ∀ n, IsSwitchGrid Q (δ n) (G n)) (hmesh : Tendsto δ atTop (𝓝 0))
    (hy₀ : Measurable y₀) (h𝓑 : 𝓑 ≤ mΩ) (hR₀ : MeasurableSet[𝓑] R₀)
    (hinit : ∀ᵐ ω ∂P, ω ∈ R₀ → (y₀ ω).1 = 0 ∧ (y₀ ω).1 + (y₀ ω).2.1 (farL (by omega : 0 < nL₀ + 0)) ≤ -3 ∧
      3 ≤ (y₀ ω).1 + (y₀ ω).2.2 (farR (by omega : 0 < nR₀ + 0)))
    (hch : IsChainFamEx P cand hnL hnR C start) :
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
  chain r j := chain_histSys_ex hfam hy₀ hch r j

end Chain


/-! ### Experiments with per-switch chain data -/

section Exp

open scoped Real

variable {κ : ℝ} {Ω Ωa : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace Ωa]
  [StandardBorelSpace Ωa] {P : Measure Ω} [IsProbabilityMeasure P] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]

/-- **PROVE-PROP59T4's candidate experiments with per-switch chain data** (`IsChainFamEx` in place of
`IsChainFam`): at every positive rational counterflow time, on the product extension `Ω × Ωa`. -/
structure CandExpEx (κ : ℝ) (P : Measure Ω) (Pa : Measure Ωa) (D : ℚ → Ω → Set ℂ) (A : ℚ → Set Ω) where
  nL : ℚ → ℕ
  nR : ℚ → ℕ
  posL : ∀ r, 0 < nL r
  posR : ∀ r, 0 < nR r
  rhoL : (r : ℚ) → Fin (nL r) → ℝ
  rhoR : (r : ℚ) → Fin (nR r) → ℝ
  /-- The allowed original switching times. -/
  grid : ℚ → Set ℝ≥0
  /-- The meshes. -/
  mesh : ℚ → ℕ → ℝ≥0
  /-- The grids. -/
  times : ℚ → ℕ → ℕ → ℝ≥0
  grid_ok : ∀ r n, IsSwitchGrid (grid r) (mesh r n) (times r n)
  mesh_ok : ∀ r, Tendsto (mesh r) atTop (𝓝 0)
  /-- The candidate pieces. -/
  cand : (r : ℚ) → CandFam (Ω × Ωa) (nL r) (nR r)
  /-- The initial start (in the dilated joint chart). -/
  y₀ : (r : ℚ) → Ω × Ωa → Start (nL r + 0) (nR r + 0)
  /-- The initial reached event. -/
  R₀ : ℚ → Set (Ω × Ωa)
  /-- The initial revealed history. -/
  base : ℚ → MeasurableSpace (Ω × Ωa)
  /-- The node images in the dilated joint chart. -/
  image : ℚ → Ω × Ωa → Set ℂ
  start : (r : ℚ) → (j : ℕ) → (Fin j → ℝ≥0) → Ω × Ωa → ℝ
  reg : ∀ r : ℚ, 0 < r → IsRegFam (cand r)
  y₀_meas : ∀ r : ℚ, 0 < r → Measurable (y₀ r)
  base_le : ∀ r : ℚ, 0 < r → base r ≤ (inferInstance : MeasurableSpace (Ω × Ωa))
  R₀_meas : ∀ r : ℚ, 0 < r → MeasurableSet[base r] (R₀ r)
  init : ∀ r : ℚ, 0 < r → ∀ᵐ ω' ∂(P.prod Pa), ω' ∈ R₀ r → (y₀ r ω').1 = 0 ∧
    (y₀ r ω').1 + (y₀ r ω').2.1 (farL (by have := posL r; omega : 0 < nL r + 0)) ≤ -3 ∧
    3 ≤ (y₀ r ω').1 + (y₀ r ω').2.2 (farR (by have := posR r; omega : 0 < nR r + 0))
  chain : ∀ r : ℚ, 0 < r → IsChainFamEx (P.prod Pa) (cand r) (posL r) (posR r) (image r) (start r)
  /-- **The piece laws of the realized construction** (the staged cross-conditioning law). -/
  pieceLaw : ∀ r : ℚ, 0 < r → Prop59StagePieceLawStatement κ (P.prod Pa) (rhoL r) (rhoR r)
    (histSys (cand r) (times r) (posL r) (posR r) (y₀ r) (R₀ r) (base r))
  initialWord : ∀ r : ℚ, 0 < r → IsStageInit κ (rhoL r) (rhoR r)
  image_bdd : ∀ r : ℚ, 0 < r → ∀ ω' : Ω × Ωa, Bornology.IsBounded (D r ω'.1) → Bornology.IsBounded (image r ω')
  active : ∀ r : ℚ, 0 < r → ∀ᵐ ω' ∂(P.prod Pa), ω'.1 ∈ A r → ω' ∈ R₀ r

/-- **A candidate experiment with per-switch chain data is an experiment** (`isStageSystem_histSys_ex`). -/
def CandExpEx.toProdExp {D : ℚ → Ω → Set ℂ} {A : ℚ → Set Ω} (X : CandExpEx κ P Pa D A) : ProdExp κ P Pa D A where
  nL := X.nL
  nR := X.nR
  posL := X.posL
  posR := X.posR
  rhoL := X.rhoL
  rhoR := X.rhoR
  grid := X.grid
  mesh := X.mesh
  times := X.times
  system r := histSys (X.cand r) (X.times r) (X.posL r) (X.posR r) (X.y₀ r) (X.R₀ r) (X.base r)
  image := X.image
  pieceLaw := X.pieceLaw
  stages r hr := isStageSystem_histSys_ex (X.reg r hr) (X.grid_ok r) (X.mesh_ok r) (X.y₀_meas r hr)
    (X.base_le r hr) (X.R₀_meas r hr) (X.init r hr) (X.chain r hr)
  initialWord := X.initialWord
  image_bdd := X.image_bdd
  active := X.active

end Exp

open Sec4 Prop513Schedule Prop513TreeExtract Prop513Target Prop513Wire Restart
open LQGMetric Exist Exist.Staged Exist.StagedLaw QuantumZipper Prop59Tips
open scoped Real

/-- **Proposition 5.13 from candidate experiments with per-switch chain data** at the root and at every node. -/
theorem prop513_path_of_partA_reverseVisit_candExpEx
    (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDiv)
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh𝒢 : Measurable[𝒢] h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P
      (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω)) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P (scheduleSpec s) (E s))
    (hVisit : StripReverseVisitLaw (Real.exp (π * x₀)) P E γ)
    {Ωa : Type} [MeasurableSpace Ωa] [StandardBorelSpace Ωa] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]
    (X₀ : CandExpEx κ P Pa (rootTarget W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime))
      fun _ => univ)
    (X : ∀ n, CandExpEx κ P Pa
      (nodeTarget W (extremeAngleTreeDescendants (capacityTree (driverTree E)) treeTime descendantIndex n))
      (nodeActive γ (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n))) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[𝒢] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = γ ω :=
  prop513_path_of_partA_reverseVisit_prodExp h44 hA hκ hκ4 hb hh𝒢 hG hcf htr hE hR hVisit X₀.toProdExp
    fun n => (X n).toProdExp

end InteractingSLE.Sec5.Prop59Pieces
