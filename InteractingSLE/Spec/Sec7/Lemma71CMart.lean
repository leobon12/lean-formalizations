/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71BTop
import InteractingSLE.Spec.Coupling.MartMeans2Local

/-!
# Lemma 7.1: the killed martingale clause from the chart form of the coupling clause

Packet PROVE-LEMMA71C. Specification, proof of Lemma 7.1 (`source/spec/p193-240.md` L604, pp. 224–225): "For each
bounded stopping time of this mapped path, the history-locality statement of Lemma 6.2 applies … The means in all the
remaining components are those of the three-curve result in Remark 6.7. In particular, in the active component they
have the two seed heights (CPF2), with the inherited logarithmic-derivative branch. Their time continuity is
Proposition 6.5. The martingale characterization, Theorem 2.4, …". The mapped driver is only defined up to its
terminal capacity time `T` (Remark 6.14, p. 218), so the coupling clause it satisfies is the one with lifetime `T`.

PROVE-CPL-MART2's `hasTwoSeedMartingaleMeans_of_isChartTransport` turns the chart form of the coupling clause
(`IsChartCouplingCharFun`) into the martingale clause of Theorem 2.4 for a **global** continuous driver (lifetime `⊤`).
This file proves the **killed** version: for a driver continuous and adapted on `[0, T)` and unbounded near a finite
`T`, the coupling clause with lifetime `T` gives the killed martingale clause `Lemma71B.HasMartingaleMeansBefore`
consumed by `Lemma71B.Lemma71KilledSegmentStatement`.

## Main results

* `frz W T t`: the killed driver frozen after `t` (and `0` off `{t < T}`), continuous and `𝓖_t`-measurable;
  through it the geometric force points of a killed driver are adapted before `T` (`adaptedBefore_geomL`,
  `adaptedBefore_geomR`), continuous on `[0, T)` and ordered around the driver;
* `annSeq`: the exit times of `|W|` capped at `n` announce `T` when the driver is unbounded near a finite `T`
  (`isAnnouncingSeq_annSeq`);
* `isLocalMartingaleBefore_couplingMean_of_meanProcOn`: the null modification `meanProcOn G` of PROVE-CPL-MART2 can be
  removed for the two-seed word (the time-zero mean is deterministic);
* **`hasMartingaleMeansBefore_of_charFun`**: the killed martingale clause from the killed coupling clause;
* **`hasMartingaleMeansBefore_of_isChartTransport`**: the killed martingale clause for every chart transport `h'` of a
  field `h` satisfying the killed chart form of the coupling clause (the form in which Lemma 7.1's three-curve
  construction delivers it, with `c ω` the pocket chart).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma71C

open MartChar Coupling Lemma71B

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### The frozen killed driver -/

section Frozen

variable {T : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}

open scoped Classical in
/-- **The killed driver frozen after `t`**: `s ↦ W (min s t)` on `{t < T}`, and `0` off it. -/
def frz (W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0∞) (t : ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun s ω => if (t : ℝ≥0∞) < T ω then W (min s t) ω else 0

theorem frz_eq {t s : ℝ≥0} {ω : Ω} (ht : (t : ℝ≥0∞) < T ω) (hs : s ≤ t) : frz W T t s ω = W s ω := by
  classical
  simp only [frz, ht, ↓reduceIte, min_eq_left hs]

theorem continuous_frz (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω}) (t : ℝ≥0)
    (ω : Ω) : Continuous fun s => frz W T t s ω := by
  classical
  by_cases ht : (t : ℝ≥0∞) < T ω
  · simp only [frz, ht, ↓reduceIte]
    refine (hc ω).comp_continuous (continuous_id.min continuous_const) fun s => ?_
    exact lt_of_le_of_lt (by exact_mod_cast min_le_right s t) ht
  · simp only [frz, ht, ↓reduceIte]
    exact continuous_const

/-- The frozen driver is `𝓖_t`-measurable at every time. -/
theorem measurable_frz {𝓖 : Filtration ℝ≥0 mΩ} (hWa : AdaptedBefore 𝓖 T W) (t s : ℝ≥0) :
    Measurable[𝓖 t] (frz W T t s) := by
  classical
  intro A hA
  have h1 : MeasurableSet[𝓖 t] {ω | (t : ℝ≥0∞) < T ω} := by
    have := hWa t univ MeasurableSet.univ
    simpa only [mem_univ, and_true] using this
  have h2 : MeasurableSet[𝓖 t] {ω | ((min s t : ℝ≥0) : ℝ≥0∞) < T ω ∧ W (min s t) ω ∈ A} :=
    𝓖.mono (min_le_right s t) _ (hWa _ A hA)
  have heq : frz W T t s ⁻¹' A = ({ω | (t : ℝ≥0∞) < T ω} ∩
      {ω | ((min s t : ℝ≥0) : ℝ≥0∞) < T ω ∧ W (min s t) ω ∈ A}) ∪
      ({ω | (t : ℝ≥0∞) < T ω}ᶜ ∩ {_ω | (0 : ℝ) ∈ A}) := by
    ext ω
    by_cases ht : (t : ℝ≥0∞) < T ω
    · have hst : ((min s t : ℝ≥0) : ℝ≥0∞) < T ω :=
        lt_of_le_of_lt (by exact_mod_cast min_le_right s t) ht
      simp [frz, ht]
    · simp [frz, ht]
  rw [heq]
  exact (h1.inter h2).union (h1.compl.inter (MeasurableSet.const _))

/-- The frozen driver is adapted to the constant filtration `𝓖_t`. -/
theorem stronglyAdapted_frz {𝓖 : Filtration ℝ≥0 mΩ} (hWa : AdaptedBefore 𝓖 T W) (t : ℝ≥0) :
    StronglyAdapted (Filtration.const ℝ≥0 (𝓖 t) (𝓖.le t)) (frz W T t) := fun s =>
  (measurable_frz hWa t s).stronglyMeasurable

end Frozen

/-- A function agreeing near each point of a set with continuous functions is continuous on it. -/
theorem continuousOn_of_locally_eq {f : ℝ≥0 → ℝ} {U : Set ℝ≥0}
    (h : ∀ t ∈ U, ∃ g : ℝ≥0 → ℝ, Continuous g ∧ f =ᶠ[𝓝 t] g) : ContinuousOn f U := by
  intro t ht
  obtain ⟨g, hg, hfg⟩ := h t ht
  exact (hg.continuousAt.congr hfg.symm).continuousWithinAt

/-! ### The geometric force points of a killed driver -/

section Geom

variable {nL nR : ℕ} {T : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
  (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω})
include hc

theorem geomL_eq_frz (xL : Fin nL → ℝ) (i : Fin nL) {t s : ℝ≥0} {ω : Ω} (ht : (t : ℝ≥0∞) < T ω)
    (hs : s ≤ t) : geomL W xL i s ω = geomL (frz W T t) xL i s ω :=
  geomL_congr (continuous_frz hc t ω) (fun _ hr => (frz_eq ht (hr.trans hs)).symm) xL i

theorem geomR_eq_frz (xR : Fin nR → ℝ) (i : Fin nR) {t s : ℝ≥0} {ω : Ω} (ht : (t : ℝ≥0∞) < T ω)
    (hs : s ≤ t) : geomR W xR i s ω = geomR (frz W T t) xR i s ω :=
  geomR_congr (continuous_frz hc t ω) (fun _ hr => (frz_eq ht (hr.trans hs)).symm) xR i

/-- The left geometric force points of a killed driver are adapted before `T`. -/
theorem adaptedBefore_geomL {𝓖 : Filtration ℝ≥0 mΩ} (hWa : AdaptedBefore 𝓖 T W) (xL : Fin nL → ℝ)
    (i : Fin nL) : AdaptedBefore 𝓖 T (geomL W xL i) := by
  intro t A hA
  have h1 : MeasurableSet[𝓖 t] {ω | (t : ℝ≥0∞) < T ω} := by
    have := hWa t univ MeasurableSet.univ
    simpa only [mem_univ, and_true] using this
  have h2 : MeasurableSet[𝓖 t] ((fun ω => geomL (frz W T t) xL i t ω) ⁻¹' A) :=
    ((stronglyAdapted_geomL (stronglyAdapted_frz hWa t) (continuous_frz hc t) xL i t).measurable) hA
  have heq : {ω | (t : ℝ≥0∞) < T ω ∧ geomL W xL i t ω ∈ A} =
      {ω | (t : ℝ≥0∞) < T ω} ∩ (fun ω => geomL (frz W T t) xL i t ω) ⁻¹' A := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨ht, hA⟩
      exact ⟨ht, by rwa [← geomL_eq_frz hc xL i ht le_rfl]⟩
    · rintro ⟨ht, hA⟩
      exact ⟨ht, by rwa [geomL_eq_frz hc xL i ht le_rfl]⟩
  rw [heq]
  exact h1.inter h2

/-- The right geometric force points of a killed driver are adapted before `T`. -/
theorem adaptedBefore_geomR {𝓖 : Filtration ℝ≥0 mΩ} (hWa : AdaptedBefore 𝓖 T W) (xR : Fin nR → ℝ)
    (i : Fin nR) : AdaptedBefore 𝓖 T (geomR W xR i) := by
  intro t A hA
  have h1 : MeasurableSet[𝓖 t] {ω | (t : ℝ≥0∞) < T ω} := by
    have := hWa t univ MeasurableSet.univ
    simpa only [mem_univ, and_true] using this
  have h2 : MeasurableSet[𝓖 t] ((fun ω => geomR (frz W T t) xR i t ω) ⁻¹' A) :=
    ((stronglyAdapted_geomR (stronglyAdapted_frz hWa t) (continuous_frz hc t) xR i t).measurable) hA
  have heq : {ω | (t : ℝ≥0∞) < T ω ∧ geomR W xR i t ω ∈ A} =
      {ω | (t : ℝ≥0∞) < T ω} ∩ (fun ω => geomR (frz W T t) xR i t ω) ⁻¹' A := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨ht, hA⟩
      exact ⟨ht, by rwa [← geomR_eq_frz hc xR i ht le_rfl]⟩
    · rintro ⟨ht, hA⟩
      exact ⟨ht, by rwa [geomR_eq_frz hc xR i ht le_rfl]⟩
  rw [heq]
  exact h1.inter h2

/-- The left geometric force points of a killed driver are continuous on `[0, T)`. -/
theorem continuousOn_geomL (xL : Fin nL → ℝ) (i : Fin nL) (ω : Ω) :
    ContinuousOn (fun t => geomL W xL i t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < T ω} := by
  refine continuousOn_of_locally_eq fun t₀ ht₀ => ?_
  obtain ⟨t₁, ht₀₁, ht₁T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (show (t₀ : ℝ≥0∞) < T ω from ht₀)
  refine ⟨fun s => geomL (frz W T t₁) xL i s ω,
    (isForcePath_geomL (continuous_frz hc t₁) xL ω i).1, ?_⟩
  filter_upwards [Iio_mem_nhds (ENNReal.coe_lt_coe.1 ht₀₁)] with s hs
  exact geomL_eq_frz hc xL i ht₁T (le_of_lt hs)

/-- The right geometric force points of a killed driver are continuous on `[0, T)`. -/
theorem continuousOn_geomR (xR : Fin nR → ℝ) (i : Fin nR) (ω : Ω) :
    ContinuousOn (fun t => geomR W xR i t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < T ω} := by
  refine continuousOn_of_locally_eq fun t₀ ht₀ => ?_
  obtain ⟨t₁, ht₀₁, ht₁T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (show (t₀ : ℝ≥0∞) < T ω from ht₀)
  refine ⟨fun s => geomR (frz W T t₁) xR i s ω,
    (isForcePath_geomR (continuous_frz hc t₁) xR ω i).1, ?_⟩
  filter_upwards [Iio_mem_nhds (ENNReal.coe_lt_coe.1 ht₀₁)] with s hs
  exact geomR_eq_frz hc xR i ht₁T (le_of_lt hs)

/-- The geometric force points of a killed driver lie on either side of it before `T`. -/
theorem geomL_le_le_geomR (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {t : ℝ≥0} {ω : Ω}
    (ht : (t : ℝ≥0∞) < T ω) :
    (∀ i, geomL W xL i t ω ≤ W t ω) ∧ ∀ i, W t ω ≤ geomR W xR i t ω := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · rw [geomL_eq_frz hc xL i ht le_rfl, ← frz_eq (W := W) ht le_rfl]
    exact geomL_le (continuous_frz hc t ω) xL i t
  · rw [geomR_eq_frz hc xR i ht le_rfl, ← frz_eq (W := W) ht le_rfl]
    exact le_geomR (continuous_frz hc t ω) xR i t

end Geom

/-- The left geometric seed image of a driver started at `0` starts at `0` (only `W 0 = 0` is used). -/
theorem geomL_twoSeed_zero_of {W : ℝ≥0 → Ω → ℝ} {ω : Ω} (hW0 : W 0 ω = 0) (i : Fin 1) :
    geomL W LP.twoSeedXL i 0 ω = 0 := by
  rw [geomL_congr (W' := fun _ _ => (0 : ℝ)) (ω := ω) continuous_const (fun s hs => by
    rw [nonpos_iff_eq_zero.1 hs, hW0])]
  exact geomL_twoSeed_zero' continuous_const rfl i

/-- The right geometric seed image of a driver started at `0` starts at `0` (only `W 0 = 0` is used). -/
theorem geomR_twoSeed_zero_of {W : ℝ≥0 → Ω → ℝ} {ω : Ω} (hW0 : W 0 ω = 0) (i : Fin 1) :
    geomR W LP.twoSeedXR i 0 ω = 0 := by
  rw [geomR_congr (W' := fun _ _ => (0 : ℝ)) (ω := ω) continuous_const (fun s hs => by
    rw [nonpos_iff_eq_zero.1 hs, hW0])]
  exact geomR_twoSeed_zero' continuous_const rfl i

/-! ### Announcing a killing time at which the driver is unbounded -/

section Announce

variable {T : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {G : Set Ω}

/-- The exit times of `|W|` above `n` (`exitAbove`), capped at `n`. -/
def annSeq (W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0∞) (G : Set Ω) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  (min (exitAbove W T G n ω) ((n : ℝ≥0) : WithTop ℝ≥0)).untop
    (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _))

theorem coe_annSeq (n : ℕ) (ω : Ω) :
    (annSeq W T G n ω : WithTop ℝ≥0) = min (exitAbove W T G n ω) ((n : ℝ≥0) : WithTop ℝ≥0) :=
  WithTop.coe_untop _ _

/-- **The capped exit times announce `T`** when the driver is continuous and adapted on `[0, T)` and unbounded near
a finite `T` (on a `𝓖₀`-measurable full event `G`). -/
theorem isAnnouncingSeq_annSeq {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous]
    (hWa : AdaptedBefore 𝓖 T W) (hG : MeasurableSet[𝓖 0] G)
    (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω})
    (hGae : ∀ᵐ ω ∂P, ω ∈ G)
    (hunb : ∀ ω ∈ G, T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|) :
    IsAnnouncingSeq 𝓖 P T (annSeq W T G) := by
  refine ⟨fun n => ?_, fun ω m n hmn => ?_, fun n => ?_, ?_⟩
  · have h := (isStoppingTime_exitAbove hWa hG hc (n : ℝ)).min_const ((n : ℝ≥0))
    have e : (fun ω => (annSeq W T G n ω : WithTop ℝ≥0)) =
        fun ω => min (exitAbove W T G n ω) ((n : ℝ≥0) : WithTop ℝ≥0) := funext fun ω => coe_annSeq n ω
    rw [e]
    exact h
  · have h : min (exitAbove W T G m ω) ((m : ℝ≥0) : WithTop ℝ≥0) ≤
        min (exitAbove W T G n ω) ((n : ℝ≥0) : WithTop ℝ≥0) := by
      refine min_le_min ?_ (WithTop.coe_le_coe.2 (Nat.cast_le.2 hmn))
      by_cases hω : ω ∈ G
      · rw [exitAbove_of_mem hω, exitAbove_of_mem hω]
        exact hitBelow_anti (neg_le_neg (Nat.cast_le.2 hmn))
      · rw [exitAbove_of_notMem hω, exitAbove_of_notMem hω]
    rw [← coe_annSeq, ← coe_annSeq] at h
    exact WithTop.coe_le_coe.1 h
  · filter_upwards [hGae] with ω hω
    by_cases hT : T ω = ⊤
    · rw [hT]
      exact ENNReal.coe_lt_top
    · obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.1
        (exitAbove_ne_top (n := (n : ℝ)) hω (hunb ω hω) hT)
      have h1 : (u : ℝ≥0∞) < T ω := lt_of_exitAbove_eq hω hu.symm
      have h2 : annSeq W T G n ω ≤ u := by
        have := min_le_left (exitAbove W T G n ω) ((n : ℝ≥0) : WithTop ℝ≥0)
        rw [← coe_annSeq, ← hu] at this
        exact WithTop.coe_le_coe.1 this
      exact lt_of_le_of_lt (by exact_mod_cast h2) h1
  · filter_upwards [hGae] with ω hω t ht
    obtain ⟨C, hC⟩ := exists_lt_exitAbove hω (hc ω) ht
    obtain ⟨n, hn⟩ := exists_nat_gt (max C t)
    refine ⟨n, ?_⟩
    have h1 : (t : WithTop ℝ≥0) < exitAbove W T G n ω := hC n (lt_of_le_of_lt (le_max_left _ _) hn)
    have h2 : (t : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0) := by
      have : (t : ℝ) < n := lt_of_le_of_lt (le_max_right _ _) hn
      exact WithTop.coe_le_coe.2 (by exact_mod_cast this.le)
    have := le_min h1.le h2
    rw [← coe_annSeq] at this
    exact WithTop.coe_le_coe.1 this

end Announce

/-! ### Removing the null modification -/

section NullMod

variable {P : Measure Ω} [IsFiniteMeasure P] {𝓖 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {W : ℝ≥0 → Ω → ℝ} {u : Ω → ℝ≥0 → ℂ → ℝ} {z : ℂ} {G : Set Ω} {ζ : Ω → WithTop ℝ≥0}

/-- **The null modification can be removed when the time-zero mean is deterministic.** If the coupling mean set to
`0` off a full event `G ∈ 𝓖₀` (`MartMeans2.meanProcOn`) is a local martingale before `ζ`, the driver starts at `0` and
the time-zero mean `u ω 0 z` does not depend on `ω`, then the coupling mean itself is a local martingale before `ζ`
(localize at `σ_k` on `G` and at `0` off `G`; the stopped mean is the `𝓖₀`-measurable constant `c` off `G`). -/
theorem isLocalMartingaleBefore_couplingMean_of_meanProcOn (hG : MeasurableSet[𝓖 0] G)
    (hGae : ∀ᵐ ω ∂P, ω ∈ G) (hW0 : ∀ ω, W 0 ω = 0) (hz : z ∈ H) {c : ℝ} (hu0 : ∀ ω, u ω 0 z = c)
    (h : IsLocalMartingaleBefore 𝓖 P ζ (MartMeans2.meanProcOn κ W u z G)) :
    IsLocalMartingaleBefore 𝓖 P ζ
      (fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω t) z) := by
  classical
  obtain ⟨σ, hσ, hσζ, hσlim, hσmart⟩ := h
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hz)
  have hGt : ∀ t, MeasurableSet[𝓖 t] G := fun t => 𝓖.mono zero_le _ hG
  set X : ℝ≥0 → Ω → ℝ := fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω t) z with hX
  have hX0 : ∀ ω, X 0 ω = c := fun ω => by
    have hw0 : (fun s : ℝ => W s.toNNReal ω) 0 = 0 := by simp only [Real.toNNReal_zero, hW0]
    simp only [hX, NNReal.coe_zero]
    rw [MartMeans2.couplingMean_zero κ hw0 (u ω 0) hz0, hu0]
  refine ⟨fun k ω => if ω ∈ G then σ k ω else 0, fun k => ?_, fun k ω => ?_, ?_, fun k => ?_⟩
  · -- a stopping time
    intro t
    have heq : {ω | (if ω ∈ G then σ k ω else 0) ≤ (t : WithTop ℝ≥0)} =
        (G ∩ {ω | σ k ω ≤ t}) ∪ Gᶜ := by
      ext ω
      by_cases hω : ω ∈ G
      · simp [hω]
      · simp only [hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_inter_iff, false_and, mem_compl_iff,
          not_false_eq_true, or_true, iff_true]
        exact WithTop.coe_le_coe.2 (zero_le : (0 : ℝ≥0) ≤ t)
    rw [heq]
    exact ((hGt t).inter (hσ k t)).union (hGt t).compl
  · -- below `ζ`
    by_cases hω : ω ∈ G
    · simp only [hω, ↓reduceIte]
      exact hσζ k ω
    · simp only [hω, ↓reduceIte]
      rw [← WithTop.coe_zero]
      exact WithTop.coe_le_iff.2 fun _ _ => zero_le
  · -- exhausting
    filter_upwards [hσlim, hGae] with ω hω hωG r hr
    simp only [hωG, ↓reduceIte]
    exact hω r hr
  · -- a martingale: the stopped mean is the stopped modified mean plus a `𝓖₀`-measurable constant off `G`
    have heq : stoppedProcess X (fun ω => if ω ∈ G then σ k ω else 0) =
        stoppedProcess (MartMeans2.meanProcOn κ W u z G) (σ k) + fun _ => Gᶜ.indicator fun _ => c := by
      funext t ω
      by_cases hω : ω ∈ G
      · simp only [stoppedProcess, hω, ↓reduceIte, Pi.add_apply, MartMeans2.meanProcOn,
          MartMeans.meanProc, indicator_of_notMem (show ω ∉ Gᶜ from fun h => h hω), add_zero, hX]
      · simp only [stoppedProcess, hω, ↓reduceIte, Pi.add_apply, MartMeans2.meanProcOn, untopA_min_zero,
          indicator_of_mem (show ω ∈ Gᶜ from hω), zero_add]
        exact hX0 ω
    rw [heq]
    refine (hσmart k).add (martingale_const_fun 𝓖 P ?_ ((integrable_const c).indicator (𝓖.le 0 _ hG.compl)))
    exact stronglyMeasurable_const.indicator hG.compl

end NullMod

/-! ### The killed martingale clause -/

section Main

variable {P : Measure Ω} [IsProbabilityMeasure P] {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous]
  {κ rL rR : ℝ} {T : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}

/-- The two-seed time-zero mean does not depend on the sample: at time `0` both geometric seed images are at the
driver `0`, and bounded harmonic extensions of the same data agree on `ℍ`. -/
theorem exists_forall_eq_time_zero (hW0 : ∀ ω, W 0 ω = 0) {u : Ω → ℝ≥0 → ℂ → ℝ}
    (hu : ∀ ω t, IsBoundedHarmonicExtension
      (forceBoundaryData κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
        (fun i => geomL W LP.twoSeedXL i t ω - W t ω) (fun i => geomR W LP.twoSeedXR i t ω - W t ω))
      (forceJumpSet (fun i => geomL W LP.twoSeedXL i t ω - W t ω)
        (fun i => geomR W LP.twoSeedXR i t ω - W t ω)) (u ω t))
    {z : ℂ} (hz : z ∈ H) : ∃ c : ℝ, ∀ ω, u ω 0 z = c := by
  rcases isEmpty_or_nonempty Ω with hΩ | hne
  · exact ⟨0, fun ω => isEmptyElim ω⟩
  obtain ⟨ω₀⟩ := hne
  refine ⟨u ω₀ 0 z, fun ω => ?_⟩
  have h1 := hu ω 0
  have h2 := hu ω₀ 0
  simp only [geomL_twoSeed_zero_of (hW0 ω), geomR_twoSeed_zero_of (hW0 ω), hW0 ω] at h1
  simp only [geomL_twoSeed_zero_of (hW0 ω₀), geomR_twoSeed_zero_of (hW0 ω₀), hW0 ω₀] at h2
  exact Impl.eqOn_of_isBoundedHarmonicExtension
    (Impl.forceJumpSet_finite (Ito.weightWord (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR))
      (fun _ => (0 : ℝ) - 0) (fun _ => (0 : ℝ) - 0)) h2 h1 hz

/-- **The killed martingale clause from the killed coupling clause.** Let `W` be a driver started at `0`, continuous
and adapted on `[0, T)` in a right-continuous filtration `𝓖` whose time-zero σ-algebra contains the null sets, almost
surely unbounded near a finite `T`, and let `h` be a random distribution on `ℍ` with integrable pairings satisfying the
coupling clause of the two-seed word with weights `(rL; rR)`, geometric force points and lifetime `T`
(`MartMeans.IsCouplingCharFun`). Then the two-seed coupling means are local martingales before
`min (swallowTime z) T`: `Lemma71B.HasMartingaleMeansBefore` (the martingale clause of
`Lemma71B.Lemma71KilledSegmentStatement`). -/
theorem hasMartingaleMeansBefore_of_charFun {h : Ω → DistOn upperHalfPlaneOpens}
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s) (hW0 : ∀ ω, W 0 ω = 0)
    (hc : ∀ ω, ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < T ω}) (hWa : AdaptedBefore 𝓖 T W)
    (hunb : ∀ᵐ ω ∂P, T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|)
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => h ω φ) P)
    (hcf : MartMeans.IsCouplingCharFun κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P 𝓖 W
      (geomL W LP.twoSeedXL) (geomR W LP.twoSeedXR) T h) :
    HasMartingaleMeansBefore κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓖 W T := by
  classical
  intro u hu z hz
  -- a `𝓖₀`-measurable full event on which the driver is unbounded at a finite `T`
  obtain ⟨G₁, hG₁m, hG₁c, hG₁⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧
      ∀ ω ∈ G, T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω| := by
    refine ⟨(toMeasurable P {ω | ¬ (T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|)})ᶜ,
      (measurableSet_toMeasurable _ _).compl, ?_, fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]
      exact ae_iff.1 hunb
    · by_contra hcon
      exact hω (subset_toMeasurable _ _ hcon)
  have hG₁0 : MeasurableSet[𝓖 0] G₁ := by
    have := (hnull _ hG₁m.compl hG₁c).compl
    rwa [compl_compl] at this
  have hG₁ae : ∀ᵐ ω ∂P, ω ∈ G₁ := by
    rw [ae_iff]
    exact hG₁c
  have hann := isAnnouncingSeq_annSeq (P := P) hWa hG₁0 hc hG₁ae hG₁
  obtain ⟨G, hG0, hGae, hloc⟩ := MartMeans2.exists_isLocalMartingaleBefore_meanProcOn hnull hWa
    (adaptedBefore_geomL hc hWa LP.twoSeedXL) (adaptedBefore_geomR hc hWa LP.twoSeedXR)
    (Eventually.of_forall fun ω => ⟨hW0 ω, hc ω,
      ⟨fun i => continuousOn_geomL hc _ i ω, fun i => continuousOn_geomR hc _ i ω⟩,
      fun t ht => geomL_le_le_geomR hc _ _ ht⟩)
    hann hint hcf u hu hz
  obtain ⟨c, hc0⟩ := exists_forall_eq_time_zero hW0 hu hz
  have hfin := isLocalMartingaleBefore_couplingMean_of_meanProcOn hG0 hGae hW0 hz hc0 hloc
  convert hfin using 2 with ω
  exact min_comm _ _

/-- **The killed martingale clause from the killed chart form of the coupling clause** (Lemma 7.1, p. 225: "The joint
pair with `h_ψ` has the original coupling specification", with the mapped driver living up to its terminal capacity
time `T`). Let `W` be a driver started at `0`, continuous and adapted on `[0, T)` in a right-continuous filtration `𝓖`
whose time-zero σ-algebra contains the null sets, almost surely unbounded near a finite `T`; let `c ω` be
`𝓖₀`-measurable conformal charts with lifts continuous on their domains, and `h` a measurable random distribution
satisfying the coupling clause of the two-seed word with weights `(rL; rR)` and lifetime `T` in the original domain of
the chart (`MartMeans2.IsChartCouplingCharFun`). Then for every chart transport `h'` of `h`, the two-seed coupling means
are local martingales before `min (swallowTime z) T`. This is PROVE-CPL-MART2's
`hasTwoSeedMartingaleMeans_of_isChartTransport` with a killing time. -/
theorem hasMartingaleMeansBefore_of_isChartTransport {c : Ω → Chart} {a k : ℝ}
    {h h' : Ω → DistOn upperHalfPlaneOpens} (hcc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) (hh : Measurable h)
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s) (hW0 : ∀ ω, W 0 ω = 0)
    (hc : ∀ ω, ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < T ω}) (hWa : AdaptedBefore 𝓖 T W)
    (hunb : ∀ᵐ ω ∂P, T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|)
    (hcf : MartMeans2.IsChartCouplingCharFun κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P 𝓖 W
      (geomL W LP.twoSeedXL) (geomR W LP.twoSeedXR) T c a k h)
    (ht : ∀ ω, IsChartTransport (c ω) 1 a k (h ω) (h' ω)) :
    HasMartingaleMeansBefore κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓖 W T := by
  have hcf' := MartMeans2.isCouplingCharFun_of_isChartTransport hcc hdom hfwd hliftm hliftc hh
    (Eventually.of_forall fun ω => ⟨hW0 ω, hc ω⟩) hcf ht
  have hm : Measurable fun ω => Chart.chartTransport (hcc ω) 1 a k (h ω) :=
    Chart.measurable_chartTransport_random' hcc (fun z => 𝓖.le 0 _ (hdom z))
      (fun z => (hfwd z).mono (𝓖.le 0) le_rfl) (fun z => (hliftm z).mono (𝓖.le 0) le_rfl) hliftc hh 1 a k
  have he : h' = fun ω => Chart.chartTransport (hcc ω) 1 a k (h ω) := funext fun ω =>
    IsChartTransport.eq_chartTransport (hcc ω)
      (Chart.locallyIntegrableOn_of_continuousOn ((hcc ω).continuousOn_lift_inv (hliftc ω))) (ht ω)
  have hT0 : ∀ᵐ ω ∂P, 0 < T ω := by
    filter_upwards [hunb] with ω hω
    by_cases hT : T ω = ⊤
    · rw [hT]
      exact ENNReal.zero_lt_top
    · obtain ⟨s, hs, -⟩ := hω hT 0
      exact zero_le.trans_lt hs
  have hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => h' ω φ) P := fun φ =>
    MartMeans2.integrable_apply_of_isCouplingCharFun (xL := LP.twoSeedXL) (xR := LP.twoSeedXR) hcf'
      (by
        filter_upwards [hT0] with ω hω
        exact ⟨hω, hc ω, hW0 ω, fun i => geomL_twoSeed_zero_of (hW0 ω) i,
          fun i => geomR_twoSeed_zero_of (hW0 ω) i⟩) φ
      (by rw [he]; exact (LQGMetric.measurable_distOn_apply φ).comp hm)
  exact hasMartingaleMeansBefore_of_charFun hnull hW0 hc hWa hunb hint hcf'

end Main

end InteractingSLE.Sec7.Lemma71C
