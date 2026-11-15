/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71LMain
import InteractingSLE.Spec.Sec7.Lemma72DHull
import InteractingSLE.Spec.Sec7.Lemma72BChart
import InteractingSLE.Spec.Coupling.Assembly11Meas

/-!
# Lemma 7.1, B4 (measurability): the avoidance event, the chart mean and the chart variance

Packet PROVE-LEMMA71M (`planning/handoffs/PROVE-LEMMA71L.md`, "What remains" 2). The fixed-time chart coupling clause
of Lemma 7.1 (`Lemma71L.isChartCouplingCharFunConst_of_premise`) needs, at every fixed capacity time `t`, the
avoidance event `{t < ζ, supp φ ⊆ ψ⁻¹(ℍ ∖ K_t)}` (`Lemma71D.IsChartAvoid`), the chart mean and the chart variance to be
measurable for the prefix filtration at `t`. Only their values on the avoidance event enter the law, so the mean and
the variance are taken **on the avoidance event** (`E.indicator`): off it the chart mean reads the forward chart map off
its domain, where nothing is measurable.

For any filtration `𝓐` in which the driver `W` is adapted and continuous before `ζ`, and any random conformal chart `c`
with domain `C`, measurable for some `𝓐₀ ≤ 𝓐 t` through its closed-ball domain events and pointwise:

* `measurableSet_lt_subset_H_diff_fwdHull`: for a compact `Q`, `{t < ζ, Q ⊆ ℍ ∖ K_t} ∈ 𝓐 t` (cover `Q` by finitely many
  rational closed discs inside `ℍ ∖ K_t`, `Coupling.exists_rationalBalls`; avoidance of a finite union of rational
  discs is `Lemma72D.measurableSet_lt_disjoint_ballsK`);
* `measurableSet_lt_subset_image`: for a compact `S`, `{t < ζ, S ⊆ ψ⁻¹(ℍ ∖ K_t)} ∈ 𝓐 t` (the random compact image
  `ψ(S)` is read on a countable dense subset of `S`);
* `measurable_meanCan_alive`: the explicit mean `𝔥_t(y)` on `{t < ζ, y ∈ ℍ ∖ K_t}` (zero elsewhere) is jointly
  measurable in `(ω, y)` (Carathéodory on the random open set `ℍ ∖ K_t`, `Lemma71I.measurable_indicator_uncurry`;
  pointwise by `Ito.measurable_fwdMap_alive`, continuity by `Lemma71D.exists_isSafeAt`);
* **`measurable_chartAvoid`**: the three measurability statements of B4 (avoidance event, chart mean and chart
  variance on it).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma71M

open QuantumZipper (H fwdHull fwdMap logDerivFwd)
open Ito Coupling Lemma71C Lemma71D

/-! ### Hull avoidance of a compact set -/

section Hull

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓐 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Hull avoidance of a compact set at a fixed time is an event of the filtration.** -/
theorem measurableSet_lt_subset_H_diff_fwdHull (hWa : AdaptedBefore 𝓐 ζ W)
    (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω}) (t : ℝ≥0) {Q : Set ℂ} (hQ : IsCompact Q) :
    MeasurableSet[𝓐 t] {ω | (t : ℝ≥0∞) < ζ ω ∧ Q ⊆ H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ)} := by
  have hζ : MeasurableSet[𝓐 t] {ω | (t : ℝ≥0∞) < ζ ω} := by
    have := hWa t univ MeasurableSet.univ
    simpa only [mem_univ, and_true] using this
  have e : {ω | (t : ℝ≥0∞) < ζ ω ∧ Q ⊆ H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ)} =
      ⋃ F ∈ {F : Finset (ℚ × ℚ × ℚ) | ballsK F ⊆ H ∧ Q ⊆ ballsK F},
        {ω | (t : ℝ≥0∞) < ζ ω ∧ Disjoint (ballsK F) (fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ))} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨ht, hQK⟩
      have ho : IsOpen (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ)) :=
        MartMeans2.isOpen_H_diff_fwdHull_rpath (hc ω) ht
      obtain ⟨F, hQF, hFO⟩ := exists_rationalBalls hQ ho hQK
      refine ⟨F, ⟨fun z hz => (hFO hz).1, hQF.trans (ballsU_subset_ballsK F)⟩, ht, ?_⟩
      exact Set.disjoint_left.2 fun z hz hzK => (hFO hz).2 hzK
    · rintro ⟨F, ⟨hFH, hQF⟩, ht, hd⟩
      exact ⟨ht, fun z hz => ⟨hFH (hQF hz), fun hzK => Set.disjoint_left.1 hd (hQF hz) hzK⟩⟩
  rw [e]
  exact MeasurableSet.biUnion (Set.to_countable _) fun F hF =>
    Lemma72D.measurableSet_lt_disjoint_ballsK hWa hc t hζ hF.1

end Hull

/-! ### Hull avoidance of a random chart image -/

section Image

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓐 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {𝓐₀ : MeasurableSpace Ω} {C : Ω → Set ℂ} {c : Ω → Chart}

/-- **The avoidance event of a compact set in the chart domain is an event of the filtration**: for a random
conformal chart, `𝓐₀`-measurable through its closed-ball domain events and pointwise, with `𝓐₀ ≤ 𝓐 t`, and a
compact `S`, the event `{t < ζ, S ⊆ ψ⁻¹(ℍ ∖ K_t)}` is in `𝓐 t`. -/
theorem measurableSet_lt_subset_image (hWa : AdaptedBefore 𝓐 ζ W)
    (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω}) (t : ℝ≥0) (h₀ : 𝓐₀ ≤ 𝓐 t)
    (hCo : ∀ ω, IsOpen (C ω)) (hCm : ∀ (z : ℂ) (r : ℝ), MeasurableSet[𝓐₀] {ω | closedBall z r ⊆ C ω})
    (hconf : ∀ ω, (c ω).IsConformal) (hdom : ∀ ω, ((c ω).dom : Set ℂ) = C ω)
    (hfm : ∀ z, Measurable[𝓐₀] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) {S : Set ℂ}
    (hS : IsCompact S) :
    MeasurableSet[𝓐 t] {ω | (t : ℝ≥0∞) < ζ ω ∧
      S ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ))} := by
  obtain ⟨D, hDS, hDc, hSD⟩ := hS.isSeparable.exists_countable_dense_subset
  have hmem : ∀ ω x, x ∈ C ω → x ∈ (c ω).dom := fun ω x hx => by
    rw [← SetLike.mem_coe, hdom ω]; exact hx
  have hcont : ∀ ω, ContinuousOn (c ω).1 (C ω) := fun ω => by
    rw [← hdom ω]; exact (hconf ω).differentiableOn_fwd.continuousOn
  set ind : ℂ → Ω → ℂ := fun x => {ω | x ∈ (c ω).dom}.indicator fun ω => (c ω).1 x with hind
  have hindx : ∀ ω x, x ∈ C ω → ind x ω = (c ω).1 x := fun ω x hx => by
    simp only [hind]
    exact indicator_of_mem (s := {ω | x ∈ (c ω).dom}) (hmem ω x hx) _
  have e : {ω | (t : ℝ≥0∞) < ζ ω ∧ S ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ))} =
      {ω | S ⊆ C ω} ∩ ⋃ F ∈ {F : Finset (ℚ × ℚ × ℚ) | ballsK F ⊆ H},
        ((⋂ x ∈ D, {ω | ind x ω ∈ ballsK F}) ∩
          {ω | (t : ℝ≥0∞) < ζ ω ∧ Disjoint (ballsK F) (fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ))}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_iInter, exists_prop]
    constructor
    · rintro ⟨ht, hSK⟩
      have hSC : S ⊆ C ω := fun x hx => by
        obtain ⟨y, hy, rfl⟩ := hSK hx
        rw [← hdom ω]
        exact (hconf ω).inv_mem_dom hy.1
      have hQ : IsCompact ((c ω).1 '' S) := hS.image_of_continuousOn ((hcont ω).mono hSC)
      have hQK : (c ω).1 '' S ⊆ H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ) := by
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨y, hy, rfl⟩ := hSK hx
        rw [(hconf ω).2.2 y hy.1]
        exact hy
      have ho : IsOpen (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ)) :=
        MartMeans2.isOpen_H_diff_fwdHull_rpath (hc ω) ht
      obtain ⟨F, hQF, hFO⟩ := exists_rationalBalls hQ ho hQK
      refine ⟨hSC, F, fun z hz => (hFO hz).1, fun x hx => ?_, ht, ?_⟩
      · rw [hindx ω x (hSC (hDS hx))]
        exact ballsU_subset_ballsK F (hQF (mem_image_of_mem _ (hDS hx)))
      · exact Set.disjoint_left.2 fun z hz hzK => (hFO hz).2 hzK
    · rintro ⟨hSC, F, hFH, hDF, ht, hd⟩
      refine ⟨ht, fun x hx => ?_⟩
      have hcl : (c ω).1 '' D ⊆ ballsK F := by
        rintro _ ⟨y, hy, rfl⟩
        rw [← hindx ω y (hSC (hDS hy))]
        exact hDF y hy
      have hxF : (c ω).1 x ∈ ballsK F := by
        have hca : ContinuousAt (c ω).1 x := (hcont ω).continuousAt ((hCo ω).mem_nhds (hSC hx))
        exact closure_minimal hcl (isCompact_ballsK F).isClosed
          (hca.continuousWithinAt.mem_closure_image (hSD hx))
      refine ⟨(c ω).1 x, ⟨hFH hxF, fun hK => Set.disjoint_left.1 hd hxF hK⟩, ?_⟩
      exact (hconf ω).inv_fwd (hmem ω x (hSC hx))
  rw [e]
  refine MeasurableSet.inter (h₀ _ (Lemma72B.measurableSet_subset_of_closedBall hCo hCm hS)) ?_
  refine MeasurableSet.biUnion (Set.to_countable _) fun F hF => MeasurableSet.inter ?_
    (Lemma72D.measurableSet_lt_disjoint_ballsK hWa hc t (by
      have := hWa t univ MeasurableSet.univ
      simpa only [mem_univ, and_true] using this) hF)
  exact MeasurableSet.biInter hDc fun x _ =>
    h₀ _ ((hfm x) (isCompact_ballsK F).isClosed.measurableSet)

end Image

/-! ### The explicit mean on the alive domain, jointly -/

section Mean

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓐 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {nL nR : ℕ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}

/-- The alive domain `{y : t < ζ, y ∈ ℍ ∖ K_t}` at the fixed time `t`. -/
def aliveDom (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) : Set ℂ :=
  {y | (t : ℝ≥0∞) < ζ ω ∧ y ∈ H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ)}

theorem isOpen_aliveDom (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω}) (t : ℝ≥0) (ω : Ω) :
    IsOpen (aliveDom W ζ t ω) := by
  by_cases ht : (t : ℝ≥0∞) < ζ ω
  · have e : aliveDom W ζ t ω = H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ) := by
      ext y; simp only [aliveDom, mem_ofPred_eq, ht, true_and]
    rw [e]
    exact MartMeans2.isOpen_H_diff_fwdHull_rpath (hc ω) ht
  · have e : aliveDom W ζ t ω = ∅ := by
      ext y; simp only [aliveDom, mem_ofPred_eq, ht, false_and, mem_empty_iff_false]
    rw [e]
    exact isOpen_empty

theorem measurableSet_closedBall_subset_aliveDom (hWa : AdaptedBefore 𝓐 ζ W)
    (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω}) (t : ℝ≥0) (z : ℂ) (r : ℝ) :
    MeasurableSet[𝓐 t] {ω | closedBall z r ⊆ aliveDom W ζ t ω} := by
  have e : {ω | closedBall z r ⊆ aliveDom W ζ t ω} =
      {ω | (t : ℝ≥0∞) < ζ ω ∧ closedBall z r ⊆ H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ)} ∪
        {_ω | closedBall z r = ∅} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union]
    constructor
    · intro h
      rcases (closedBall z r).eq_empty_or_nonempty with he | ⟨y, hy⟩
      · exact Or.inr he
      · exact Or.inl ⟨(h hy).1, fun x hx => (h hx).2⟩
    · rintro (⟨ht, h⟩ | he) x hx
      · exact ⟨ht, h hx⟩
      · rw [he] at hx; exact hx.elim
  rw [e]
  exact (measurableSet_lt_subset_H_diff_fwdHull hWa hc t (isCompact_closedBall z r)).union
    (MeasurableSet.const _)

/-- **The explicit mean on the alive domain is jointly measurable** in `(ω, y)` for `𝓐 t ⊗ Borel`. -/
theorem measurable_meanCan_alive (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (hWa : AdaptedBefore 𝓐 ζ W)
    (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hVLa : ∀ i, AdaptedBefore 𝓐 ζ (VL i)) (hVRa : ∀ i, AdaptedBefore 𝓐 ζ (VR i)) (t : ℝ≥0) :
    @Measurable (Ω × ℂ) ℂ (@Prod.instMeasurableSpace Ω ℂ (𝓐 t) _) _
      ({p : Ω × ℂ | p.2 ∈ aliveDom W ζ t p.1}.indicator fun p =>
        ((meanCan κ ρL ρR (W · p.1) (fun i s => VL i s p.1) (fun i s => VR i s p.1) t p.2 : ℝ) : ℂ)) := by
  classical
  refine @Lemma71I.measurable_indicator_uncurry Ω (𝓐 t) (aliveDom W ζ t) (isOpen_aliveDom hc t)
    (measurableSet_closedBall_subset_aliveDom hWa hc t)
    (F := fun ω y => ((meanCan κ ρL ρR (W · ω) (fun i s => VL i s ω) (fun i s => VR i s ω) t y : ℝ) : ℂ))
    (fun ω => ?_) (fun y => ?_)
  · intro y hy
    obtain ⟨ht, hyK⟩ := hy
    have ho := MartMeans2.isOpen_H_diff_fwdHull_rpath (hc ω) ht
    obtain ⟨ε, hε, hεb⟩ := Metric.isOpen_iff.1 ho y hyK
    have hK : closedBall y (ε / 2) ⊆ H \ fwdHull (rpath (W · ω)) (t : ℝ) :=
      (closedBall_subset_ball (by linarith)).trans hεb
    obtain ⟨δ, hδ, hsafe⟩ := exists_isSafeAt (hc ω) (isCompact_closedBall y (ε / 2)) ht hK
    have hcm := IsSafeAt.continuousOn_meanCan_space (κ := κ) (ρL := ρL) (ρR := ρR)
      (vL := fun i s => VL i s ω) (vR := fun i s => VR i s ω) (hc ω) (hK.trans sdiff_subset) hsafe hδ le_rfl
    have hca : ContinuousAt (meanCan κ ρL ρR (W · ω) (fun i s => VL i s ω) (fun i s => VR i s ω) t) y :=
      hcm.continuousAt (closedBall_mem_nhds y (by linarith))
    exact (Complex.continuous_ofReal.continuousAt.comp hca).continuousWithinAt
  · by_cases hy : 0 < y.im
    · have hset : {ω | y ∈ aliveDom W ζ t ω} = aliveSet W ζ univ y t := by
        ext ω
        simp only [aliveDom, aliveSet, mem_ofPred_eq, mem_univ, true_and]
        constructor
        · rintro ⟨ht, hyH, hyK⟩
          exact ⟨ht, QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull t.coe_nonneg hyH hyK⟩
        · rintro ⟨ht, hsol⟩
          exact ⟨ht, hy, notMem_fwdHull_of_alive (hc ω) ht hy hsol⟩
      have hGc : ∀ ω ∈ (univ : Set Ω), ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} :=
        fun ω _ => hc ω
      have hG : MeasurableSet[𝓐 0] (univ : Set Ω) := MeasurableSet.univ
      have hA := measurableSet_aliveSet hWa hGc hG hy t
      have hf := measurable_fwdMap_alive hWa hGc hG hy t
      have hL := measurable_logDerivFwd_alive hWa hGc hG hy t
      set a : Ω → Fin nL → ℝ := fun ω i => Girsanov.killed ζ (VL i) t ω - Girsanov.killed ζ W t ω
      set b : Ω → Fin nR → ℝ := fun ω i => Girsanov.killed ζ (VR i) t ω - Girsanov.killed ζ W t ω
      have ha : Measurable[𝓐 t] a := @Measurable.of_eval Ω (Fin nL) (fun _ => ℝ) (𝓐 t) _ a fun i =>
        (Girsanov.measurable_killed (hVLa i) t).sub (Girsanov.measurable_killed hWa t)
      have hb : Measurable[𝓐 t] b := @Measurable.of_eval Ω (Fin nR) (fun _ => ℝ) (𝓐 t) _ b fun i =>
        (Girsanov.measurable_killed (hVRa i) t).sub (Girsanov.measurable_killed hWa t)
      have hm : Measurable[𝓐 t] fun ω => ((meanHarmonic κ ρL ρR (a ω) (b ω)
          (if ω ∈ aliveSet W ζ univ y t then fwdMap (rpath (W · ω)) t y else 0) -
          QuantumZipper.chiC κ * (if ω ∈ aliveSet W ζ univ y t then
            logDerivFwd (rpath (W · ω)) t y else 0).im : ℝ) : ℂ) := by
        let _ : MeasurableSpace Ω := 𝓐 t
        exact Complex.measurable_ofReal.comp (((measurable_meanHarmonic_prod κ ρL ρR).comp
          (ha.prodMk (hb.prodMk hf))).sub (measurable_const.mul (Complex.measurable_im.comp hL)))
      have e : ({ω | y ∈ aliveDom W ζ t ω}.indicator fun ω =>
          ((meanCan κ ρL ρR (W · ω) (fun i s => VL i s ω) (fun i s => VR i s ω) t y : ℝ) : ℂ)) =
          (aliveSet W ζ univ y t).indicator fun ω => ((meanHarmonic κ ρL ρR (a ω) (b ω)
            (if ω ∈ aliveSet W ζ univ y t then fwdMap (rpath (W · ω)) t y else 0) -
            QuantumZipper.chiC κ * (if ω ∈ aliveSet W ζ univ y t then
              logDerivFwd (rpath (W · ω)) t y else 0).im : ℝ) : ℂ) := by
        rw [hset]
        funext ω
        by_cases hω : ω ∈ aliveSet W ζ univ y t
        · simp only [indicator_of_mem hω, hω, ↓reduceIte, meanCan, a, b,
            Girsanov.killed_of_lt hω.2.1]
        · simp only [indicator_of_notMem hω]
      rw [e]
      exact hm.indicator hA
    · have e : ({ω | y ∈ aliveDom W ζ t ω}.indicator fun ω =>
          ((meanCan κ ρL ρR (W · ω) (fun i s => VL i s ω) (fun i s => VR i s ω) t y : ℝ) : ℂ)) = 0 := by
        funext ω
        refine indicator_of_notMem (fun h => hy ?_) _
        exact h.2.1
      rw [e]
      exact measurable_const

end Mean

/-! ### B4: the avoidance event, the chart mean and the chart variance -/

section Chart

theorem measurable_integral_uncurry {Ω : Type*} [m : MeasurableSpace Ω] {g : Ω × ℂ → ℝ} (hg : Measurable g) :
    Measurable fun ω => ∫ z, g (ω, z) :=
  hg.stronglyMeasurable.integral_prod_right'.measurable

theorem prod_mono_left {Ω : Type*} {m₁ m₂ : MeasurableSpace Ω} (h : m₁ ≤ m₂) :
    @Prod.instMeasurableSpace Ω ℂ m₁ _ ≤ @Prod.instMeasurableSpace Ω ℂ m₂ _ :=
  sup_le_sup_right (MeasurableSpace.comap_mono h) _

/-- For a conformal chart, `ψ⁻¹(X) = {z ∈ dom : ψ(z) ∈ X}` for `X ⊆ ℍ`. -/
theorem image_inv_eq {c : Chart} (hc : c.IsConformal) {X : Set ℂ} (hX : X ⊆ H) :
    c.2.1 '' X = {z | z ∈ c.dom ∧ c.1 z ∈ X} := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hc.inv_mem_dom (hX hy), by rw [hc.2.2 y (hX hy)]; exact hy⟩
  · rintro ⟨hz, hzX⟩
    exact ⟨c.1 z, hzX, hc.inv_fwd hz⟩

theorem isOpen_image_inv {c : Chart} (hc : c.IsConformal) {X : Set ℂ} (hXo : IsOpen X) (hX : X ⊆ H) :
    IsOpen (c.2.1 '' X) := by
  rw [image_inv_eq hc hX]
  exact hc.differentiableOn_fwd.continuousOn.isOpen_inter_preimage c.dom.isOpen hXo

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓐 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {nL nR : ℕ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {𝓐₀ : MeasurableSpace Ω} {C : Ω → Set ℂ} {c : Ω → Chart}

/-- **B4, measurability.** For a driver adapted and continuous before `ζ` with adapted force points, and a random
conformal chart measurable for `𝓐₀ ≤ 𝓐 t` (closed-ball domain events, forward map and lift pointwise), the chart
avoidance event at `t` is in `𝓐 t`, and the chart mean and the chart variance **on it** are `𝓐 t`-measurable. -/
theorem measurable_chartAvoid (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (a k : ℝ) (hWa : AdaptedBefore 𝓐 ζ W)
    (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hVLa : ∀ i, AdaptedBefore 𝓐 ζ (VL i)) (hVRa : ∀ i, AdaptedBefore 𝓐 ζ (VR i)) (t : ℝ≥0)
    (h₀ : 𝓐₀ ≤ 𝓐 t) (hCo : ∀ ω, IsOpen (C ω))
    (hCm : ∀ (z : ℂ) (r : ℝ), MeasurableSet[𝓐₀] {ω | closedBall z r ⊆ C ω})
    (hconf : ∀ ω, (c ω).IsConformal) (hdom : ∀ ω, ((c ω).dom : Set ℂ) = C ω)
    (hfm : ∀ z, Measurable[𝓐₀] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hlm : ∀ z, Measurable[𝓐₀] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hlc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) (φ : TestOn upperHalfPlaneOpens) :
    MeasurableSet[𝓐 t] {ω | IsChartAvoid (fun s => W s ω) (ζ ω) (c ω) φ t} ∧
    Measurable[𝓐 t] ({ω | IsChartAvoid (fun s => W s ω) (ζ ω) (c ω) φ t}.indicator fun ω =>
      chartMean κ ρL ρR (fun s => W s ω) (fun i s => VL i s ω) (fun i s => VR i s ω) (c ω) a k φ t) ∧
    Measurable[𝓐 t] ({ω | IsChartAvoid (fun s => W s ω) (ζ ω) (c ω) φ t}.indicator fun ω =>
      chartVar (fun s => W s ω) (c ω) φ t) := by
  classical
  set E := {ω | IsChartAvoid (fun s => W s ω) (ζ ω) (c ω) φ t} with hEdef
  have hφc : IsCompact (tsupport (φ : ℂ → ℝ)) := φ.hasCompactSupport
  have hE : MeasurableSet[𝓐 t] E :=
    measurableSet_lt_subset_image hWa hc t h₀ hCo hCm hconf hdom hfm hφc
  have hmemC : ∀ ω z, z ∈ (c ω).dom ↔ z ∈ C ω := fun ω z => by
    rw [← SetLike.mem_coe, hdom ω]
  have hset : ∀ z, {ω | z ∈ (c ω).dom} = {ω | z ∈ C ω} := fun z => by
    ext ω; exact hmemC ω z
  refine ⟨hE, ?_, ?_⟩
  · -- the chart mean
    have hF := @Lemma71I.measurable_indicator_uncurry Ω 𝓐₀ C hCo hCm (fun ω z => (c ω).1 z)
      (fun ω => by rw [← hdom ω]; exact (hconf ω).differentiableOn_fwd.continuousOn)
      (fun z => by rw [← hset z]; exact hfm z)
    have hLf := @Lemma71I.measurable_indicator_uncurry Ω 𝓐₀ C hCo hCm (fun ω z => ((c ω).2.2 z : ℂ))
      (fun ω => by
        rw [← hdom ω]
        exact Complex.continuous_ofReal.comp_continuousOn (hlc ω))
      (fun z => by
        rw [← hset z]
        have h1 := (hlm z)
        have e : ({ω | z ∈ (c ω).dom}.indicator fun ω => (((c ω).2.2 z : ℝ) : ℂ)) =
            (fun x : ℝ => (x : ℂ)) ∘ ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z) := by
          funext ω
          by_cases hω : ω ∈ {ω | z ∈ (c ω).dom}
          · simp only [indicator_of_mem hω, Function.comp_apply]
          · simp only [indicator_of_notMem hω, Function.comp_apply, Complex.ofReal_zero]
        rw [e]
        exact @Measurable.comp Ω ℝ ℂ 𝓐₀ _ _ _ _ Complex.measurable_ofReal h1)
    have hF' := hF.mono (prod_mono_left h₀) le_rfl
    have hLf' := hLf.mono (prod_mono_left h₀) le_rfl
    have hΦ := measurable_meanCan_alive κ ρL ρR hWa hc hVLa hVRa t
    set Cind : Ω × ℂ → ℂ := {p : Ω × ℂ | p.2 ∈ C p.1}.indicator fun p => (c p.1).1 p.2 with hCind
    set Lind : Ω × ℂ → ℂ := {p : Ω × ℂ | p.2 ∈ C p.1}.indicator fun p => (((c p.1).2.2 p.2 : ℝ) : ℂ)
      with hLind
    set Φ : Ω × ℂ → ℂ := {p : Ω × ℂ | p.2 ∈ aliveDom W ζ t p.1}.indicator fun p =>
      ((meanCan κ ρL ρR (W · p.1) (fun i s => VL i s p.1) (fun i s => VR i s p.1) t p.2 : ℝ) : ℂ) with hΦdef
    set g : Ω × ℂ → ℝ := fun p => if p.1 ∈ E ∧ p.2 ∈ tsupport (φ : ℂ → ℝ) then
      ((Φ (p.1, Cind p)).re - a - k * (Lind p).re) * φ p.2 else 0 with hgdef
    have hg : @Measurable (Ω × ℂ) ℝ (@Prod.instMeasurableSpace Ω ℂ (𝓐 t) _) _ g := by
      let _ : MeasurableSpace Ω := 𝓐 t
      have hEp : MeasurableSet {p : Ω × ℂ | p.1 ∈ E ∧ p.2 ∈ tsupport (φ : ℂ → ℝ)} :=
        (measurable_fst hE).inter (measurable_snd (isClosed_tsupport _).measurableSet)
      refine Measurable.ite hEp ?_ measurable_const
      refine Measurable.mul ?_ ((φ.contDiff.continuous.measurable).comp measurable_snd)
      refine ((Complex.measurable_re.comp (hΦ.comp (measurable_fst.prodMk hF'))).sub measurable_const).sub
        (measurable_const.mul (Complex.measurable_re.comp hLf'))
    have hint := @measurable_integral_uncurry Ω (𝓐 t) g hg
    convert hint using 1
    funext ω
    by_cases hω : ω ∈ E
    · rw [indicator_of_mem hω]
      simp only [chartMean]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      by_cases hz : z ∈ tsupport (φ : ℂ → ℝ)
      · have hzE := hω.2 hz
        obtain ⟨y, hy, hyz⟩ := hzE
        have hzC : z ∈ C ω := by rw [← hmemC, ← hyz]; exact (hconf ω).inv_mem_dom hy.1
        have hcz : (c ω).1 z = y := by rw [← hyz]; exact (hconf ω).2.2 y hy.1
        have hCi : Cind (ω, z) = (c ω).1 z := indicator_of_mem (s := {p : Ω × ℂ | p.2 ∈ C p.1}) hzC _
        have hLi : Lind (ω, z) = (((c ω).2.2 z : ℝ) : ℂ) :=
          indicator_of_mem (s := {p : Ω × ℂ | p.2 ∈ C p.1}) hzC _
        have hal : ((ω, (c ω).1 z) : Ω × ℂ) ∈ {p : Ω × ℂ | p.2 ∈ aliveDom W ζ t p.1} := by
          show (c ω).1 z ∈ aliveDom W ζ t ω
          rw [hcz]
          exact ⟨hω.1, hy⟩
        have hΦi : Φ (ω, (c ω).1 z) = ((meanCan κ ρL ρR (W · ω) (fun i s => VL i s ω)
            (fun i s => VR i s ω) t ((c ω).1 z) : ℝ) : ℂ) := indicator_of_mem hal _
        simp only [hgdef, hω, hz, and_self, ↓reduceIte, hCi, hLi, hΦi, Complex.ofReal_re]
      · simp only [hgdef, hz, and_false, ↓reduceIte, image_eq_zero_of_notMem_tsupport hz, mul_zero]
    · rw [indicator_of_notMem hω]
      simp only [hgdef, hω, false_and, ↓reduceIte, integral_zero]
  · -- the chart variance
    set U : Ω → Set ℂ := fun ω => if ω ∈ E then
      (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ)) else ∅ with hUdef
    have hU : ∀ ω, IsOpen (U ω) ∧ U ω ⊆ H := fun ω => by
      by_cases hω : ω ∈ E
      · simp only [hUdef, hω, ↓reduceIte]
        refine ⟨isOpen_image_inv (hconf ω) (MartMeans2.isOpen_H_diff_fwdHull_rpath (hc ω) hω.1) sdiff_subset,
          ?_⟩
        rintro _ ⟨y, hy, rfl⟩
        exact (hconf ω).2.1 hy.1
      · simp only [hUdef, hω, ↓reduceIte]
        exact ⟨isOpen_empty, empty_subset _⟩
    have hUm : ∀ j, MeasurableSet[𝓐 t] {ω | tsupport (QuantumZipper.K3.testFamily j) ⊆ U ω} := fun j => by
      have hj := QuantumZipper.K3.testFamily_mem j
      have e : {ω | tsupport (QuantumZipper.K3.testFamily j) ⊆ U ω} =
          (E ∩ {ω | (t : ℝ≥0∞) < ζ ω ∧ tsupport (QuantumZipper.K3.testFamily j) ⊆
            (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ))}) ∪
          (Eᶜ ∩ {_ω | tsupport (QuantumZipper.K3.testFamily j) ⊆ ∅}) := by
        ext ω
        by_cases hω : ω ∈ E
        · simp only [hUdef, hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_inter_iff, true_and, mem_compl_iff,
            not_true_eq_false, false_and, or_false]
          exact ⟨fun h => ⟨hω.1, h⟩, fun h => h.2⟩
        · simp only [hUdef, hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_inter_iff, false_and, mem_compl_iff,
            not_false_eq_true, true_and, false_or]
      rw [e]
      exact (hE.inter (measurableSet_lt_subset_image hWa hc t h₀ hCo hCm hconf hdom hfm hj.2.1)).union
        (hE.compl.inter (MeasurableSet.const _))
    have hV := @QuantumZipper.K3.measurable_zeroGFFTestCov Ω (𝓐 t) U hU hUm (LocalSets.toTestFunH φ)
      (LocalSets.toTestFunH φ)
    have e : (E.indicator fun ω => chartVar (fun s => W s ω) (c ω) φ t) =
        E.indicator fun ω => QuantumZipper.zeroGFFTestCov (U ω) (LocalSets.toTestFunH φ).1
          (LocalSets.toTestFunH φ).1 := by
      funext ω
      by_cases hω : ω ∈ E
      · simp only [indicator_of_mem hω, chartVar, hUdef, hω, ↓reduceIte]
        rfl
      · simp only [indicator_of_notMem hω]
    rw [e]
    exact hV.indicator hE

end Chart

end InteractingSLE.Sec7.Lemma71M
