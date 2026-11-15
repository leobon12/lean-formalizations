/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvAssemble

/-!
# K2 on the countable force-type cells: the canonical code from (S) and (L)

Packet PROVE-T14-SB2DRV. K2 (`Cond.isCondFlowLineDriverOn_of_hasSafeLaw_on`) fixes the numbers and
weights of the force marks; a random launch word has countably many force types almost surely
(`exists_k2Launch_countable_types`, PROVE-T14-SB2K2). This file runs K2 on every type cell on which
the relative seed is admissible (`seedCell`) and combines the cells, for an arbitrary conditioning
σ-algebra `𝒢` (for SB2(1) the entrance σ-algebra, not only the retained past):

* `thr_eq_zero_of_seed`: a seed at its threshold has threshold time `0`;
  `not_seed_of_thr_pos`: a positive threshold time forces an admissible seed;
* `measurableSet_seedCell`;
* `isCondFlowLineDriverOn_of_hasSafeLaw_onI`: K2 on a live event with the chart pairings integrable on
  the event only (`integrable_cond_of_integrableOn`);
* **`ae_codeMatch_of_k2_cells`**: from K2's inputs (S) and (L) on every admissible type cell, the
  relative driver, with the geometric threshold as lifetime, matches the canonical code of
  (word, chart field) almost surely on every admissible cell (Theorems 1.2–1.3 through K2 and
  `ae_codeMatch_of_isCondFlowLineDriverOn`).

**R48.** Theorems 1.2–1.3 are hypotheses; this serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist.Staged Exist.StagedLaw Supp8.Q3Stop
  Sec7.PocketTraversal WalkInf

/-! ### The threshold at the seed -/

section Seed

variable {Ω : Type*} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **A seed at its threshold has threshold time `0`.** -/
theorem thr_eq_zero_of_seed {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0)
    (hWc : ∀ ω, Continuous fun t => W t ω) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j) {ω : Ω}
    (hs : ForceWord.ThresholdCondition ρL ρR 0 (xL ω) (xR ω)) : FCDet.thr ρL ρR W xL xR ω = 0 := by
  have hL : (fun i => geomLW W xL i 0 ω) = xL ω := funext fun i => geomLW_zero hWc hW0 (hxL0 ω i)
  have hR : (fun j => geomRW W xR j 0 ω) = xR ω := funext fun j => geomRW_zero hWc hW0 (hxR0 ω j)
  have hmem : (0 : ℝ≥0) ∈ MartChar.thresholdSet ρL ρR (fun t => W t ω) (fun i t => geomLW W xL i t ω)
      (fun j t => geomRW W xR j t ω) := by
    show ForceWord.ThresholdCondition ρL ρR (W 0 ω) (fun i => geomLW W xL i 0 ω)
      (fun j => geomRW W xR j 0 ω)
    rw [hL, hR, hW0 ω]
    exact hs
  have hinf : sInf (MartChar.thresholdSet ρL ρR (fun t => W t ω) (fun i t => geomLW W xL i t ω)
      (fun j t => geomRW W xR j t ω)) = 0 :=
    le_antisymm (csInf_le (OrderBot.bddBelow _) hmem) bot_le
  unfold FCDet.thr MartChar.thresholdTime
  rw [ite_eq_left ⟨0, hmem⟩, hinf]
  rfl

/-- **A positive threshold time forces an admissible seed.** -/
theorem not_seed_of_thr_pos {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0)
    (hWc : ∀ ω, Continuous fun t => W t ω) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j) {ω : Ω}
    (hpos : 0 < FCDet.thr ρL ρR W xL xR ω) :
    ¬ ForceWord.ThresholdCondition ρL ρR 0 (xL ω) (xR ω) := fun hs => by
  rw [thr_eq_zero_of_seed hW0 hWc hxL0 hxR0 hs] at hpos
  exact lt_irrefl _ hpos

end Seed

/-! ### The admissible type cells -/

section Cells

variable {Ω : Type*}

/-- The left mark positions of the type `w` read from the random word. -/
def cellXL (κ θ : ℝ) (cw : Ω → BoundaryWord) (w : WordType) : Ω → Fin w.1 → ℝ :=
  fun ω => FCDet.typeXL κ θ w.1 w.2.1 (typedRhoL w) (typedRhoR w) (cw ω)

/-- The right mark positions of the type `w` read from the random word. -/
def cellXR (κ θ : ℝ) (cw : Ω → BoundaryWord) (w : WordType) : Ω → Fin w.2.1 → ℝ :=
  fun ω => FCDet.typeXR κ θ w.1 w.2.1 (typedRhoL w) (typedRhoR w) (cw ω)

/-- **The type cell with an admissible seed**: the live event restricted to the force type `w`, on
which the type's seed is not at its continuation threshold (K2's `hseed`). -/
def seedCell (κ θ : ℝ) (cw : Ω → BoundaryWord) (F : Set Ω) (w : WordType) : Set Ω :=
  wordTypeCell κ θ cw F w ∩
    {ω | ¬ ForceWord.ThresholdCondition (typedRhoL w) (typedRhoR w) 0 (cellXL κ θ cw w ω)
      (cellXR κ θ cw w ω)}

theorem measurable_cellXL {𝒢 : MeasurableSpace Ω} {κ θ : ℝ} {cw : Ω → BoundaryWord}
    (hcw : Measurable[𝒢] cw) (w : WordType) : Measurable[𝒢] (cellXL κ θ cw w) :=
  (FCDet.measurable_typeXL κ θ w.1 w.2.1 (typedRhoL w) (typedRhoR w)).comp hcw

theorem measurable_cellXR {𝒢 : MeasurableSpace Ω} {κ θ : ℝ} {cw : Ω → BoundaryWord}
    (hcw : Measurable[𝒢] cw) (w : WordType) : Measurable[𝒢] (cellXR κ θ cw w) :=
  (FCDet.measurable_typeXR κ θ w.1 w.2.1 (typedRhoL w) (typedRhoR w)).comp hcw

theorem measurableSet_seedCell {𝒢 : MeasurableSpace Ω} {κ θ : ℝ} {cw : Ω → BoundaryWord}
    {F : Set Ω} (hcw : Measurable[𝒢] cw) (hF : MeasurableSet[𝒢] F) (w : WordType) :
    MeasurableSet[𝒢] (seedCell κ θ cw F w) := by
  have h1 : MeasurableSet[𝒢] (wordTypeCell κ θ cw F w) :=
    @measurableSet_wordTypeCell Ω 𝒢 κ θ cw F hcw hF w
  have hm : Measurable[𝒢] fun ω => (cellXL κ θ cw w ω, cellXR κ θ cw w ω) :=
    (measurable_cellXL hcw w).prodMk (measurable_cellXR hcw w)
  exact h1.inter (hm (FCDet.measurableSet_thresholdCondition_zero (typedRhoL w) (typedRhoR w))).compl

theorem seedCell_subset {κ θ : ℝ} {cw : Ω → BoundaryWord} {F : Set Ω} (w : WordType) :
    seedCell κ θ cw F w ⊆ F := fun _ hω => hω.1.1

end Cells

/-! ### K2 with integrability on the live event only -/

/-- Integrability on `F` is integrability under the conditioned measure `P[·|F]`. -/
theorem integrable_cond_of_integrableOn {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {F : Set Ω}
    {E' : Type*} [NormedAddCommGroup E'] {f : Ω → E'} (hf : IntegrableOn f F P) :
    Integrable f (ProbabilityTheory.cond P F) := by
  by_cases hPF : P F = 0
  · rw [ProbabilityTheory.cond, Measure.restrict_eq_zero.2 hPF, smul_zero]
    exact integrable_zero_measure
  · exact hf.smul_measure (ENNReal.inv_ne_top.2 hPF)

/-- **K2 on a live event with the chart pairings integrable on the event only**
(`Cond.isCondFlowLineDriverOn_of_hasSafeLaw_on`, whose proof runs K2 under `P[·|F]` and so uses the
integrability only there). -/
theorem isCondFlowLineDriverOn_of_hasSafeLaw_onI (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {nL nR : ℕ} {κ θ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hκ : 0 < κ) {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓗 : Filtration ℝ≥0 mΩ} (h𝒢 : 𝒢 ≤ 𝓗 0)
    {F : Set Ω} (hF : MeasurableSet[𝒢] F)
    {cw : Ω → BoundaryWord} (hcw : Measurable[𝒢] cw)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝒢] xL) (hxR : Measurable[𝒢] xR)
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j) (hxLa : ∀ ω, Antitone (xL ω))
    (hxRm : ∀ ω, Monotone (xR ω))
    (hword : ∀ᵐ ω ∂P, ω ∈ F → flowLineNL (cw ω).fn (cw ω).jumps 0 = nL ∧
      flowLineNR (cw ω).fn (cw ω).jumps 0 = nR ∧
      truncWord nL nR (padFL κ θ (cw ω).fn (cw ω).jumps) = ((xL ω, xR ω), (ρL, ρR)))
    {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓗 W) {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hlc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hint : ∀ φ : TestOn upperHalfPlaneOpens,
      IntegrableOn (fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω) φ) F P)
    (hseed : ∀ᵐ ω ∂P, ω ∈ F → ¬ ForceWord.ThresholdCondition ρL ρR 0 (xL ω) (xR ω))
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗 F (FCDet.thr ρL ρR W xL xR) W (geomLW W xL) (geomRW W xR)
      fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω))
    (hmem : HasSafeMembers P 𝓗 F (FCDet.thr ρL ρR W xL xR) W
      fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω))
    (hG : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → IsPiecewiseConstantBoundaryData (cw ω₀).fn (cw ω₀).jumps ∧
      ∃ h' : Ω → DistOn upperHalfPlaneOpens, (∀ ω, IsChartTransport (c ω₀) 1 0 (chiC κ) (h ω) (h' ω)) ∧
        IsGFFWithBoundaryData (condExpKernel P 𝒢 ω₀) h' (cw ω₀).fn (cw ω₀).jumps)
    (hcc : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), c ω = c ω₀) :
    SB.IsCondFlowLineDriverOn κ θ 𝒢 P F h c (fun ω => (cw ω).fn) (fun ω => (cw ω).jumps) W
      (FCDet.thr ρL ρR W xL xR) := by
  have h𝒢m : 𝒢 ≤ mΩ := h𝒢.trans (𝓗.le 0)
  have hFm : MeasurableSet F := h𝒢m _ hF
  by_cases hPF : P F = 0
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hPF] with ω h1 h2 using absurd h2 h1
  set Q : Measure Ω := ProbabilityTheory.cond P F with hQ
  have : IsProbabilityMeasure Q := ProbabilityTheory.cond_isProbabilityMeasure hPF
  have hker := BW1Chain.ae_condExpKernel_cond_eq (P := P) h𝒢m hF
  have hF0 : MeasurableSet[𝓗 0] F := h𝒢 _ hF
  have hres := Cond.isCondFlowLineDriverOn_of_hasSafeLaw (P := Q) h12p h13 hκ h𝒢 hcw hxL hxR hxL0 hxR0
    hxLa hxRm (BW1Chain.ae_cond_of_ae hFm hword) hW0 hWc hWa hhm hc hdom hfwd hliftm hlc
    (fun φ => integrable_cond_of_integrableOn (hint φ)) (BW1Chain.ae_cond_of_ae hFm hseed)
    (BW1Chain.hasSafeLaw_cond hF0 hlaw) (BW1Chain.hasSafeMembers_cond hF0 hmem)
    (BW1Chain.ae_cond_of_ae hFm (by
      filter_upwards [hG, hker] with ω₀ hG₀ hk₀ hω₀
      rw [hk₀ hω₀]
      exact hG₀ hω₀))
    (BW1Chain.ae_cond_of_ae hFm (by
      filter_upwards [hcc, hker] with ω₀ hc₀ hk₀ hω₀
      rw [hk₀ hω₀]
      exact hc₀ hω₀))
  filter_upwards [BW1Chain.ae_of_ae_cond hFm hres, hker] with ω₀ hr hk hω₀
  have h1 := hr hω₀ (mem_univ ω₀)
  rw [hk hω₀] at h1
  exact h1

/-! ### K2 on every admissible cell -/

/-- **The canonical code from K2's (S) and (L) on the admissible type cells.** Let the field be read
through a `𝒢`-measurable random chart `c`, kernel-almost surely constant on the live event `F ∈ 𝒢`,
and let the chart field be, conditionally on `𝒢`, the GFF of the `𝒢`-measurable word `cw` on `F`.
Let `W` be a globally continuous relative driver from `0`, adapted to `𝓗` with `𝒢 ≤ 𝓗 0`. If K2's
(S) (`HasSafeLaw`) and (L) (`HasSafeMembers`) hold with the geometric threshold of the type's marks
as lifetime, on every admissible cell of a countable set `T` of types, then almost surely, on every
admissible cell of `T`, `W` with that threshold matches the canonical code of (word, chart field). -/
theorem ae_codeMatch_of_k2_cells (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {κ θ : ℝ} (hκ : 0 < κ)
    {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓗 : Filtration ℝ≥0 mΩ} (h𝒢 : 𝒢 ≤ 𝓗 0)
    {F : Set Ω} (hF : MeasurableSet[𝒢] F) {cw : Ω → BoundaryWord} (hcw : Measurable[𝒢] cw)
    {c : Ω → Chart} (hc : IsMeasChart 𝒢 c)
    (hcc : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), c ω = c ω₀)
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h)
    (hG : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → IsPiecewiseConstantBoundaryData (cw ω₀).fn (cw ω₀).jumps ∧
      ∃ h' : Ω → DistOn upperHalfPlaneOpens, (∀ ω, IsChartTransport (c ω₀) 1 0 (chiC κ) (h ω) (h' ω)) ∧
        IsGFFWithBoundaryData (condExpKernel P 𝒢 ω₀) h' (cw ω₀).fn (cw ω₀).jumps)
    {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓗 W)
    (hint : ∀ φ : TestOn upperHalfPlaneOpens,
      IntegrableOn (fun ω => Chart.chartTransport (hc.1 ω) 1 (θ * chiC κ) (chiC κ) (h ω) φ) F P)
    {T : Set WordType} (hT : T.Countable)
    (hlaw : ∀ w ∈ T, HasSafeLaw κ (typedRhoL w) (typedRhoR w) P 𝓗 (seedCell κ θ cw F w)
      (FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ θ cw w) (cellXR κ θ cw w)) W
      (geomLW W (cellXL κ θ cw w)) (geomRW W (cellXR κ θ cw w))
      (fun ω => Chart.chartTransport (hc.1 ω) 1 (θ * chiC κ) (chiC κ) (h ω)))
    (hmem : ∀ w ∈ T, HasSafeMembers P 𝓗 (seedCell κ θ cw F w)
      (FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ θ cw w) (cellXR κ θ cw w)) W
      (fun ω => Chart.chartTransport (hc.1 ω) 1 (θ * chiC κ) (chiC κ) (h ω))) :
    ∀ᵐ ω ∂P, ∀ w ∈ T, ω ∈ seedCell κ θ cw F w →
      IsDriverCodeMatch (driverCode h12p hκ θ
        (cw ω, Chart.chartTransport (hc.1 ω) 1 0 (chiC κ) (h ω))) (fun t => W t ω)
        (FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ θ cw w) (cellXR κ θ cw w) ω) := by
  have h𝒢m : 𝒢 ≤ mΩ := h𝒢.trans (𝓗.le 0)
  have hcm := hc.mono h𝒢m
  have hWm : ∀ t, Measurable (W t) := fun t => (hWa t).measurable.mono (𝓗.le t) le_rfl
  refine (ae_ball_iff hT).2 fun w hw => ?_
  have hFw := measurableSet_seedCell (θ := θ) (κ := κ) hcw hF w
  have hxL := measurable_cellXL (κ := κ) (θ := θ) hcw w
  have hxR := measurable_cellXR (κ := κ) (θ := θ) hcw w
  have hxL0 : ∀ ω i, cellXL κ θ cw w ω i ≤ 0 := fun ω => (FCDet.isOrderedForceWord_typeXL (cw ω)).2.1
  have hxR0 : ∀ ω j, 0 ≤ cellXR κ θ cw w ω j := fun ω =>
    (FCDet.isOrderedForceWord_typeXL (cw ω)).2.2.2
  have hxLa : ∀ ω, Antitone (cellXL κ θ cw w ω) := fun ω => (FCDet.isOrderedForceWord_typeXL (cw ω)).1
  have hxRm : ∀ ω, Monotone (cellXR κ θ cw w ω) := fun ω =>
    (FCDet.isOrderedForceWord_typeXL (cw ω)).2.2.1
  have hword : ∀ᵐ ω ∂P, ω ∈ seedCell κ θ cw F w →
      flowLineNL (cw ω).fn (cw ω).jumps 0 = w.1 ∧ flowLineNR (cw ω).fn (cw ω).jumps 0 = w.2.1 ∧
      truncWord w.1 w.2.1 (padFL κ θ (cw ω).fn (cw ω).jumps) =
        ((cellXL κ θ cw w ω, cellXR κ θ cw w ω), (typedRhoL w, typedRhoR w)) :=
    Eventually.of_forall fun ω hω => k2_word_of_mem_wordTypeCell hω.1
  have hseed : ∀ᵐ ω ∂P, ω ∈ seedCell κ θ cw F w →
      ¬ ForceWord.ThresholdCondition (typedRhoL w) (typedRhoR w) 0 (cellXL κ θ cw w ω)
        (cellXR κ θ cw w ω) :=
    Eventually.of_forall fun ω hω => hω.2
  have hD := isCondFlowLineDriverOn_of_hasSafeLaw_onI h12p h13 hκ h𝒢 hFw hcw hxL hxR hxL0 hxR0
    hxLa hxRm hword hW0 hWc hWa hhm hc.1 (fun z => h𝒢m _ (hc.2.2.2.1 z))
    (fun z => (hc.2.2.2.2.1 z).mono h𝒢m le_rfl) (fun z => (hc.2.2.2.2.2.2 z).mono h𝒢m le_rfl)
    hc.2.1 (fun φ => (hint φ).mono_set (seedCell_subset w)) hseed (hlaw w hw) (hmem w hw)
    (hG.mono fun ω h hω => h (seedCell_subset w hω))
    (hcc.mono fun ω h hω => h (seedCell_subset w hω))
  have hVm : Measurable (FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ θ cw w)
      (cellXR κ θ cw w)) :=
    FCDet.measurable_thr hWc hWa (hxL.mono h𝒢 le_rfl) (hxR.mono h𝒢 le_rfl)
  exact ae_codeMatch_of_isCondFlowLineDriverOn h12p h13 hκ θ h𝒢m hFw hhm hcw hc
    (hcc.mono fun ω h hω => h (seedCell_subset w hω)) hWm hVm hD

end InteractingSLE.Theorem14.SB.Lv
