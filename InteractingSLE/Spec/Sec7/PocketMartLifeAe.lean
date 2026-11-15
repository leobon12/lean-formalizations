/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketMartLifeStop

/-!
# Aux. lemma 125 before the lifetime, part 3: the infinite relative lifetime from Aux. lemma 122's hypotheses

Packet PROVE-STRIPSYS14 (specification §7.4, proof of Aux. lemma 125, `source/spec/p385-432.md` L213–L232,
pp. 396–397). For a random driven curve `γ ω` (`PocketTraversal.IsDrivenCurve`; for the pocket traversal its relative
curve) with points of `ℍ` of arbitrarily large modulus and filled prefixes adapted to a right-continuous filtration,
random `𝓕₀`-measurable ordered marks with seeds at `0`, side partial sums of the weights `> −2`, and Aux. lemma 122's
hypotheses **before the terminal capacity time** `capLife (γ ω)` for the canonical driver `W t ω = segDriver (γ ω) t`
and the geometric force coordinates (`HasPhaseMeansBefore`):

* `continuousOn_geomLW_of_lt`, `continuousOn_geomRW_of_lt`: the force coordinates are continuous before the lifetime;
* `exists_announcing_coords`: the times `τₘ = m ∧ inf {s < ζ : |W_s| + ∑ |V_s| > m}` are stopping times, strictly
  before the lifetime, nondecreasing, exhausting, with the coordinates bounded by `m` up to `τₘ` ("`ζₙ = n ∧ inf {s < ζ
  : |X_C(s)| ≥ n}` […] These are genuine stopping times in the relative history and supply pre-lifetime localizations
  for the martingale and SDE arguments", p. 396);
* **`ae_isForcePathPre_of_hasPhaseMeans`**: almost surely the path conditions of Definition 2.1 hold before the
  lifetime (Aux. lemma 122's conclusion before the lifetime, with "no continuation threshold", p. 397);
* **`ae_capLife_eq_top_of_hasPhaseMeans`**: almost surely `capLife (γ ω) = ∞` (Aux. lemma 125: "Thus `ζ = ∞`").
  This removes the martingale hypotheses of PROVE-STRIPSYS13's `PocketLife.ae_capLife_eq_top_of_martProc`: the
  stopped martingale part and its compensated square are martingales along `τₘ`
  (`PocketMartLife.martingale_martProc_stop`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketMartLife

open MartChar PocketTraversal PhaseSel

/-! ### Continuity of the force coordinates before the lifetime -/

section Path

variable {Ω : Type*} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {T : Ω → WithTop ℝ≥0}

theorem continuousOn_geomLW_of_lt (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω})
    (xL : Ω → Fin nL → ℝ) (i : Fin nL) (ω : Ω) :
    ContinuousOn (fun t => geomLW W xL i t ω) {t | (t : WithTop ℝ≥0) < T ω} := by
  intro t ht
  obtain ⟨r, htr, hrT⟩ := WithTop.lt_iff_exists_coe_btwn.1 ht
  have hc : ContinuousOn (W · ω) (Iic r) := (hWc ω).mono fun s hs =>
    lt_of_le_of_lt (WithTop.coe_le_coe.2 hs) hrT
  have hg : Continuous fun s => geomLW (fun s (_ : Ω) => PhaseSelAdapt.contW (W · ω) r s) xL i s ω :=
    (isForcePath_geomLW (W := fun s (_ : Ω) => PhaseSelAdapt.contW (W · ω) r s)
      (fun _ => PhaseSelAdapt.continuous_contW hc) xL ω i).1
  have heq : (fun s => geomLW (fun s (_ : Ω) => PhaseSelAdapt.contW (W · ω) r s) xL i s ω) =ᶠ[𝓝 t]
      fun s => geomLW W xL i s ω := by
    filter_upwards [Iio_mem_nhds (WithTop.coe_lt_coe.1 htr)] with s hs
    exact (geomLW_eq_contW (hWc ω) hrT (le_of_lt hs) xL i).symm
  exact (hg.continuousAt.congr heq).continuousWithinAt

theorem continuousOn_geomRW_of_lt (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω})
    (xR : Ω → Fin nR → ℝ) (j : Fin nR) (ω : Ω) :
    ContinuousOn (fun t => geomRW W xR j t ω) {t | (t : WithTop ℝ≥0) < T ω} := by
  intro t ht
  obtain ⟨r, htr, hrT⟩ := WithTop.lt_iff_exists_coe_btwn.1 ht
  have hc : ContinuousOn (W · ω) (Iic r) := (hWc ω).mono fun s hs =>
    lt_of_le_of_lt (WithTop.coe_le_coe.2 hs) hrT
  have hg : Continuous fun s => geomRW (fun s (_ : Ω) => PhaseSelAdapt.contW (W · ω) r s) xR j s ω :=
    (isForcePath_geomRW (W := fun s (_ : Ω) => PhaseSelAdapt.contW (W · ω) r s)
      (fun _ => PhaseSelAdapt.continuous_contW hc) xR ω j).1
  have heq : (fun s => geomRW (fun s (_ : Ω) => PhaseSelAdapt.contW (W · ω) r s) xR j s ω) =ᶠ[𝓝 t]
      fun s => geomRW W xR j s ω := by
    filter_upwards [Iio_mem_nhds (WithTop.coe_lt_coe.1 htr)] with s hs
    exact (geomRW_eq_contW (hWc ω) hrT (le_of_lt hs) xR j).symm
  exact (hg.continuousAt.congr heq).continuousWithinAt

/-- The coordinate size `|W| + ∑ |V|` is continuous before the lifetime. -/
theorem continuousOn_absSum_of_lt (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω})
    (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) (ω : Ω) :
    ContinuousOn (fun t => absSum W (jointV (geomLW W xL) (geomRW W xR)) t ω) {t | (t : WithTop ℝ≥0) < T ω} := by
  refine (hWc ω).abs.add (continuousOn_finsetSum _ fun j _ => ?_)
  cases j with
  | inl i => exact (continuousOn_geomLW_of_lt hWc xL i ω).abs
  | inr j => exact (continuousOn_geomRW_of_lt hWc xR j ω).abs

/-- The martingale part is continuous before the lifetime. -/
theorem continuousOn_martProc_of_lt (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω})
    (ρ : Fin nL ⊕ Fin nR → ℝ) (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) (ω : Ω) :
    ContinuousOn (fun t => martProc ρ W (jointV (geomLW W xL) (geomRW W xR)) t ω)
      {t | (t : WithTop ℝ≥0) < T ω} := by
  simp only [martProc, martValue]
  refine ((hWc ω).sub continuousOn_const).add (continuousOn_const.mul (continuousOn_finsetSum _ fun j _ => ?_))
  refine continuousOn_const.mul (ContinuousOn.sub ?_ continuousOn_const)
  cases j with
  | inl i => exact continuousOn_geomLW_of_lt hWc xL i ω
  | inr j => exact continuousOn_geomRW_of_lt hWc xR j ω

/-- **The martingale part is bounded by the coordinate size**: `|M_t| ≤ 2m + m ∑ |ρ|` when `|W| + ∑ |V| ≤ m` at
the times `0` and `t`. -/
theorem abs_martProc_le {ι : Type*} [Fintype ι] {ρ : ι → ℝ} {V : ι → ℝ≥0 → Ω → ℝ} {m : ℝ} {t : ℝ≥0} {ω : Ω}
    (ht : absSum W V t ω ≤ m) (h0 : absSum W V 0 ω ≤ m) :
    |martProc ρ W V t ω| ≤ 2 * m + (∑ j, |ρ j|) * m := by
  have hWs : ∀ s, |W s ω| ≤ absSum W V s ω := fun s => by
    have h := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => abs_nonneg (V j s ω)
    simp only [absSum]
    linarith
  have hWt := (hWs t).trans ht
  have hW0 := (hWs 0).trans h0
  have hV : ∀ s j, |V j s ω| ≤ absSum W V s ω := fun s j => by
    have := Finset.single_le_sum (f := fun j => |V j s ω|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
    simp only [absSum]
    linarith [abs_nonneg (W s ω)]
  simp only [martProc, martValue]
  have hs : |∑ j, ρ j * (V j t ω - V j 0 ω)| ≤ (∑ j, |ρ j|) * (2 * m) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have := abs_sub (V j t ω) (V j 0 ω)
    linarith [(hV t j).trans ht, (hV 0 j).trans h0]
  have hw := abs_sub (W t ω) (W 0 ω)
  calc |W t ω - W 0 ω + 1 / 2 * ∑ j, ρ j * (V j t ω - V j 0 ω)|
      ≤ |W t ω - W 0 ω| + |1 / 2 * ∑ j, ρ j * (V j t ω - V j 0 ω)| := abs_add_le _ _
    _ ≤ 2 * m + (∑ j, |ρ j|) * m := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith

end Path

/-! ### The announcing times of the coordinates -/

section Curve

open Lemma71C

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {γ : Ω → ℝ → ℂ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}

/-- The coordinate size `|W_t| + ∑ |V_t|` of the canonical driver of a random curve and the geometric images of
random marks. -/
def coordSize (γ : Ω → ℝ → ℂ) (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) : ℝ≥0 → Ω → ℝ :=
  absSum (fun t ω => segDriver (γ ω) t)
    (jointV (geomLW (fun t ω => segDriver (γ ω) t) xL) (geomRW (fun t ω => segDriver (γ ω) t) xR))

/-- **The canonical driver killed at the lifetime is adapted**, for adapted filled prefixes. -/
theorem stronglyAdapted_killAt_segDriver (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hpre : IsPrefixAdapted 𝓕 γ) :
    StronglyAdapted 𝓕 (Aux122Disint.killAt (fun ω => capLife (γ ω)) fun t ω => segDriver (γ ω) t) := fun t =>
  (Aux122Disint.measurable_killAt_of_adaptedBefore (adaptedBefore_segDriver_of_isDrivenCurve hγ hpre)
    t).stronglyMeasurable

theorem killAt_segDriver_of_lt {ω : Ω} {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) < capLife (γ ω)) :
    Aux122Disint.killAt (fun ω => capLife (γ ω)) (fun t ω => segDriver (γ ω) t) t ω = segDriver (γ ω) t := by
  simp only [Aux122Disint.killAt]
  exact ite_eq_left_iff.2 fun h => absurd ht h

/-- The coordinate size of the restarted coordinates agrees with that of the original ones up to `σ`. -/
theorem absSum_stopW {W : ℝ≥0 → Ω → ℝ} {T : Ω → WithTop ℝ≥0} {σ : Ω → ℝ≥0}
    (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω}) (hσT : ∀ ω, (σ ω : WithTop ℝ≥0) < T ω)
    {ω : Ω} {t : ℝ≥0} (ht : t ≤ σ ω) :
    absSum (stopW W σ) (jointV (geomLW (stopW W σ) xL) (geomRW (stopW W σ) xR)) t ω =
      absSum W (jointV (geomLW W xL) (geomRW W xR)) t ω := by
  simp only [absSum, stopW_of_le ht]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  cases j with
  | inl i =>
    show |geomLW (stopW W σ) xL i t ω| = |geomLW W xL i t ω|
    rw [geomLW_stopW hWc hσT ht i]
  | inr j =>
    show |geomRW (stopW W σ) xR j t ω| = |geomRW W xR j t ω|
    rw [geomRW_stopW hWc hσT ht j]

/-- **The coordinates announce the lifetime** (proof of Aux. lemma 125, p. 396): the times
`τₘ = m ∧ inf {s < ζ : |W_s| + ∑ |V_s| > m}` are stopping times, strictly before the lifetime `ζ = capLife`,
nondecreasing, exhausting `[0, ζ)`, bounded by `m`, with the coordinate size at most `m` up to `τₘ` when `τₘ > 0`. -/
theorem exists_announcing_coords [𝓕.IsRightContinuous] (hγ : ∀ ω, IsDrivenCurve (γ ω))
    (hunb : ∀ ω (M : ℝ), ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖) (hpre : IsPrefixAdapted 𝓕 γ)
    (hxLm : Measurable[𝓕 0] xL) (hxRm : Measurable[𝓕 0] xR) :
    ∃ τ : ℕ → Ω → ℝ≥0, (∀ m, IsStoppingTime 𝓕 fun ω => (τ m ω : WithTop ℝ≥0)) ∧
      (∀ m ω, (τ m ω : WithTop ℝ≥0) < capLife (γ ω)) ∧ (∀ ω, Monotone fun m => τ m ω) ∧
      (∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < capLife (γ ω) → ∃ m, t ≤ τ m ω) ∧ (∀ m ω, τ m ω ≤ m) ∧
      ∀ m ω, 0 < τ m ω → ∀ t ≤ τ m ω, coordSize γ xL xR t ω ≤ m := by
  set W : ℝ≥0 → Ω → ℝ := fun t ω => segDriver (γ ω) t with hWdef
  set T : Ω → WithTop ℝ≥0 := fun ω => capLife (γ ω) with hTdef
  set X := coordSize γ xL xR with hXdef
  have hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω} := fun ω => (hγ ω).segDriver_spec.2.1
  have hXc : ∀ ω, ContinuousOn (X · ω) {t | (t : WithTop ℝ≥0) < T ω} := continuousOn_absSum_of_lt hWc xL xR
  have hWka := stronglyAdapted_killAt_segDriver hγ hpre
  have hWk : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < T ω →
      Aux122Disint.killAt (fun ω => capLife (γ ω)) (fun t ω => segDriver (γ ω) t) t ω = W t ω :=
    fun ω t ht => killAt_segDriver_of_lt ht
  obtain ⟨σ, hσ, hσT, -, hσex⟩ := PocketLife.exists_announcing_capLife hγ hunb hpre
  -- measurability of the coordinate size before the lifetime, through the restarted coordinates
  have hXa : ∀ (t : ℝ≥0) (c : ℝ), MeasurableSet[𝓕 t] {ω | (t : WithTop ℝ≥0) < T ω ∧ c < X t ω} := by
    intro t c
    have e : {ω | (t : WithTop ℝ≥0) < T ω ∧ c < X t ω} = ⋃ n, ({ω | ((t : ℝ≥0) : WithTop ℝ≥0) ≤ (σ n ω)} ∩
        {ω | c < absSum (stopW W (σ n)) (jointV (geomLW (stopW W (σ n)) xL) (geomRW (stopW W (σ n)) xR)) t ω}) := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
      constructor
      · rintro ⟨ht, hc⟩
        obtain ⟨n, hn⟩ := hσex ω t ht
        refine ⟨n, WithTop.coe_le_coe.2 hn, ?_⟩
        rw [absSum_stopW hWc (fun ω => hσT n ω) hn]
        exact hc
      · rintro ⟨n, hn, hc⟩
        have hn' : t ≤ σ n ω := WithTop.coe_le_coe.1 hn
        rw [absSum_stopW hWc (fun ω => hσT n ω) hn'] at hc
        exact ⟨lt_of_le_of_lt hn (hσT n ω), hc⟩
    rw [e]
    refine MeasurableSet.iUnion fun n => (hσ n).measurableSet_ge t |>.inter ?_
    have hWa' := stronglyAdapted_stopW hWka hWk hWc (hσ n) (fun ω => hσT n ω)
    have hWc' := continuous_stopW hWc (fun ω => hσT n ω)
    have hVa : ∀ j, StronglyAdapted 𝓕
        (jointV (geomLW (stopW W (σ n)) xL) (geomRW (stopW W (σ n)) xR) j) := fun j => by
      cases j with
      | inl i => exact stronglyAdapted_geomLW hWa' hWc' hxLm i
      | inr j => exact stronglyAdapted_geomRW hWa' hWc' hxRm j
    exact measurableSet_lt measurable_const (measurable_absSum hWa' hVa t)
  -- unboundedness before a finite lifetime
  have hWX : ∀ ω t, |W t ω| ≤ X t ω := fun ω t => by
    have h := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) =>
      abs_nonneg (jointV (geomLW W xL) (geomRW W xR) j t ω)
    simp only [hXdef, coordSize, absSum]
    linarith
  have hunb' : ∀ ω, T ω ≠ ⊤ → ∀ M : ℝ, ∃ s : ℝ≥0, (s : WithTop ℝ≥0) < T ω ∧ M < X s ω := fun ω hfin M => by
    obtain ⟨s, hs, hM⟩ := PocketLife.exists_lt_abs_segDriver (hγ ω) (hunb ω) hfin M
    exact ⟨s, hs, hM.trans_le (hWX ω s)⟩
  refine ⟨RelClock.announce X T, RelClock.isStoppingTime_announce hXa hXc,
    fun m ω => RelClock.announce_lt (hunb' ω) m, RelClock.monotone_announce,
    fun ω t ht => RelClock.exists_le_announce hXc ht, fun m ω => min_le_left _ _, fun m ω hpos t ht => ?_⟩
  have hτT : ((RelClock.announce X T m ω : ℝ≥0) : WithTop ℝ≥0) < T ω := RelClock.announce_lt (hunb' ω) m
  -- before `τₘ` the size is at most `m`
  have hbefore : ∀ s : ℝ≥0, s < RelClock.announce X T m ω → X s ω ≤ m := fun s hs => by
    by_contra hlt
    push Not at hlt
    have hsT : (s : WithTop ℝ≥0) < T ω := lt_trans (WithTop.coe_lt_coe.2 hs) hτT
    have h1 := RelClock.entrance_le hsT hlt
    have h2 : ((RelClock.announce X T m ω : ℝ≥0) : WithTop ℝ≥0) ≤ RelClock.entrance X T m ω := by
      rw [RelClock.coe_announce]; exact min_le_right _ _
    exact absurd (h2.trans h1) (not_le.2 (WithTop.coe_lt_coe.2 hs))
  rcases ht.lt_or_eq with ht' | ht'
  · exact hbefore t ht'
  -- at `τₘ` itself, by continuity from the left
  subst ht'
  have hne : (𝓝[<] (RelClock.announce X T m ω)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
  have hopen : IsOpen {s : ℝ≥0 | (s : WithTop ℝ≥0) < T ω} := isOpen_lt WithTop.continuous_coe continuous_const
  have hcont : ContinuousAt (X · ω) (RelClock.announce X T m ω) := (hXc ω).continuousAt (hopen.mem_nhds hτT)
  have hev : ∀ᶠ s in 𝓝[<] (RelClock.announce X T m ω), X s ω ≤ m :=
    eventually_nhdsWithin_of_forall fun s hs => hbefore s hs
  exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev

/-! ### The infinite lifetime -/

/-- **Aux. lemma 125 with the path conditions almost surely**: PROVE-STRIPSYS13's
`PocketLife.ae_capLife_eq_top_of_martProc` with the path conditions before the lifetime holding almost surely instead
of for every `ω` (the same proof: the noise has a left limit at a finite lifetime, `ae_exists_tendsto_of_announcing`,
and the pathwise Aux. lemma 125 `capLife_eq_top_of_driverEq` contradicts finiteness). -/
theorem ae_capLife_eq_top_of_martProc_ae [IsProbabilityMeasure P] (hγ : ∀ ω, IsDrivenCurve (γ ω))
    (hunb : ∀ ω (M : ℝ), ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖) {a : ℝ} (ha : 0 < a) {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hpath : ∀ᵐ ω ∂P, Aux125.IsForcePathPre (xL ω) (xR ω) ρL ρR (segDriver (γ ω)) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (capLife (γ ω)))
    (hL : ∑ i, ρL i ≠ -2) (hR : ∑ j, ρR j ≠ -2)
    {σ : ℕ → Ω → ℝ≥0} (hσ : ∀ n, IsStoppingTime 𝓕 fun ω => (σ n ω : WithTop ℝ≥0))
    (hσT : ∀ n ω, (σ n ω : ℝ≥0∞) < capLife (γ ω)) (hσm : ∀ ω, Monotone fun n => σ n ω)
    (hσex : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < capLife (γ ω) → ∃ n, t ≤ σ n ω)
    (hbc : ∀ ω, ContinuousOn (fun t => martProc (jointρ ρL ρR) (fun t ω => segDriver (γ ω) t) (jointV VL VR) t ω /
      Real.sqrt a) {t | (t : ℝ≥0∞) < capLife (γ ω)})
    (hbb : ∀ n, ∃ C, ∀ ω t, t ≤ σ n ω →
      |martProc (jointρ ρL ρR) (fun t ω => segDriver (γ ω) t) (jointV VL VR) t ω / Real.sqrt a| ≤ C)
    (hbm : ∀ n, Martingale (fun t ω => martProc (jointρ ρL ρR) (fun t ω => segDriver (γ ω) t) (jointV VL VR)
      (min t (σ n ω)) ω / Real.sqrt a) 𝓕 P)
    (hQ : ∀ n, Martingale (fun t ω => (martProc (jointρ ρL ρR) (fun t ω => segDriver (γ ω) t) (jointV VL VR)
      (min t (σ n ω)) ω / Real.sqrt a) ^ 2 - ((min t (σ n ω) : ℝ≥0) : ℝ)) 𝓕 P) :
    ∀ᵐ ω ∂P, capLife (γ ω) = ⊤ := by
  classical
  set b : ℝ≥0 → Ω → ℝ := fun t ω =>
    martProc (jointρ ρL ρR) (fun t ω => segDriver (γ ω) t) (jointV VL VR) t ω / Real.sqrt a with hbdef
  have hint : ∀ n (N : ℝ≥0), Integrable (fun ω => b (min N (σ n ω)) ω ^ 2) P := fun n N => by
    obtain ⟨C, hC⟩ := hbb n
    refine Integrable.of_bound ((((hbm n).1 N).mono (Filtration.le _ N)).aestronglyMeasurable.pow 2) (C ^ 2)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC ω _ (min_le_right _ _)) 2
  have hL2 : ∀ N : ℝ≥0, BddAbove (range fun n => ∫ ω, b (min N (σ n ω)) ω ^ 2 ∂P) := fun N =>
    PocketLife.bddAbove_integral_sq_of_martingale_sq_sub (κ := 1) zero_le_one hint
      (fun n => by simpa only [one_mul] using hQ n) N
  filter_upwards [PocketLife.ae_exists_tendsto_of_announcing (M := b) hσ hσT hσm hσex hbc hbb hbm hL2, hpath]
    with ω hω hp
  by_contra hne
  obtain ⟨Lim, hLim⟩ := hω hne
  set T : ℝ≥0 := (capLife (γ ω)).toNNReal with hTdef
  have hTe : (T : ℝ≥0∞) = capLife (γ ω) := ENNReal.coe_toNNReal hne
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < capLife (γ ω) ↔ t < T := fun t => by
    rw [← hTe]; exact ENNReal.coe_lt_coe
  have hc : ContinuousOn (b · ω) (Iio T) := (hbc ω).mono fun t ht => (hlt t).2 ht
  have hb'c := PocketLife.continuous_extend_of_tendsto hc hLim
  have hw := PocketLife.driverEq_martValue hp ha
  have e : (fun t => b t ω) = fun t => martValue (jointρ ρL ρR) (segDriver (γ ω) 0)
      (jointV (fun i => VL i 0 ω) (fun j => VR j 0 ω)) (segDriver (γ ω) t)
      (jointV (fun i => VL i t ω) (fun j => VR j t ω)) / Real.sqrt a :=
    funext fun t => by simp only [hbdef]; rw [PocketLife.martProc_jointV_apply]
  rw [← e] at hw
  have hw' : Sec2.DriverEq a ρL ρR (segDriver (γ ω)) (fun i t => VL i t ω) (fun j t => VR j t ω)
      (fun t => if t < T then b t ω else Lim) (capLife (γ ω)) := fun t ht => by
    rw [hw t ht]
    simp only [(hlt t).1 ht, ↓reduceIte]
  exact hne (PocketLife.capLife_eq_top_of_driverEq (hγ ω) (hunb ω) hp hw' hb'c hL hR)

variable {k : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {d : ℝ≥0 → Ω → ℝ}

/-- `−2 < ρ 0` from the partial sums. -/
theorem neg_two_lt_zero_of_partialSums {n : ℕ} {ρ : Fin (n + 1) → ℝ}
    (hs : ∀ m : Fin (n + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρ i) : -2 < ρ 0 := by
  have h := hs 0
  have e : Finset.univ.filter (fun i : Fin (n + 1) => i ≤ 0) = {0} := by
    ext i; simp
  rwa [e, Finset.sum_singleton] at h

/-- The total weight from the partial sums: `∑ ρ ≠ −2`. -/
theorem sum_ne_neg_two_of_partialSums {n : ℕ} {ρ : Fin (n + 1) → ℝ}
    (hs : ∀ m : Fin (n + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρ i) : ∑ i, ρ i ≠ -2 := by
  have h := hs (Fin.last n)
  have e : Finset.univ.filter (fun i : Fin (n + 1) => i ≤ Fin.last n) = Finset.univ := by
    ext i; simp [Fin.le_last]
  rw [e] at h
  exact h.ne'

end Curve

section Main

open Lemma71C

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {k : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {γ : Ω → ℝ → ℂ}
  {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {d : ℝ≥0 → Ω → ℝ}

/-- **Aux. lemma 122's conclusion before the lifetime: Definition 2.1's equations hold before `capLife`, almost
surely**, with the noise `M/√k` (specification pp. 389–391 and p. 397). Hypotheses: a random driven curve with points
of `ℍ` of arbitrarily large modulus and filled prefixes adapted to a right-continuous filtration; random
`𝓕₀`-measurable marks (seeds `0`, the other left marks negative, the other right marks positive, ordered in the
index); side partial sums of the weights `> −2` and the seed weights below `2(k/2 − 2) − 2`; the phase `d_t ∈ 2πχℤ`
and Aux. lemma 122's hypotheses before the lifetime (`HasPhaseMeansBefore`). -/
theorem ae_isWordEntrance_of_hasPhaseMeans [IsProbabilityMeasure P] [𝓕.IsRightContinuous] (hk : 4 < k)
    (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    (hrL' : ρL 0 < 2 * (k / 2 - 2) - 2) (hrR' : ρR 0 < 2 * (k / 2 - 2) - 2)
    (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hunb : ∀ ω (M : ℝ), ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    (hpre : IsPrefixAdapted 𝓕 γ) (hxLm : Measurable[𝓕 0] xL) (hxRm : Measurable[𝓕 0] xR)
    (hseedL : ∀ ω, xL ω 0 = 0) (hseedR : ∀ ω, xR ω 0 = 0)
    (hxLd : ∀ ω (i : Fin nL), xL ω i.succ < 0) (hxRd : ∀ ω (j : Fin nR), 0 < xR ω j.succ)
    (hxLi : ∀ ω, Antitone (xL ω)) (hxRi : ∀ ω, Monotone (xR ω))
    (hd : ∀ (t : ℝ≥0) ω, 0 < t → (t : WithTop ℝ≥0) < capLife (γ ω) → ∃ n : ℤ, d t ω = n * phaseStep k)
    (hM : HasPhaseMeansBefore k ρL ρR P 𝓕 (fun t ω => segDriver (γ ω) t) xL xR d (fun ω => capLife (γ ω))) :
    ∀ᵐ ω ∂P, Aux117.IsWordEntrance k (xL ω) (xR ω) ρL ρR (segDriver (γ ω))
      (fun i t => geomLW (fun t ω => segDriver (γ ω) t) xL i t ω)
      (fun j t => geomRW (fun t ω => segDriver (γ ω) t) xR j t ω)
      (fun t => martProc (jointρ ρL ρR) (fun t ω => segDriver (γ ω) t)
        (jointV (geomLW (fun t ω => segDriver (γ ω) t) xL) (geomRW (fun t ω => segDriver (γ ω) t) xR)) t ω /
          Real.sqrt k) (capLife (γ ω)) := by
  have hWc : ∀ ω, ContinuousOn ((fun t ω => segDriver (γ ω) t) · ω)
      {t | (t : WithTop ℝ≥0) < capLife (γ ω)} := fun ω => (hγ ω).segDriver_spec.2.1
  have hW0 : ∀ ω, segDriver (γ ω) 0 = 0 := fun ω => (hγ ω).segDriver_spec.1
  obtain ⟨τ, hτ, hτT, -, hτex, -, -⟩ := exists_announcing_coords hγ hunb hpre hxLm hxRm
  have h := fun m => ae_isWordEntrance_stop (P := P) (σ := τ m) hk (neg_two_lt_zero_of_partialSums hsL) hrL'
    (neg_two_lt_zero_of_partialSums hsR) hrR' hsL hsR hW0 hWc (stronglyAdapted_killAt_segDriver hγ hpre)
    (fun ω t ht => killAt_segDriver_of_lt ht) hxLm hxRm hseedL hseedR hxLd hxRd hxLi hxRi hd hM (hτ m)
    (hτT m)
  filter_upwards [ae_all_iff.2 h] with ω hω
  refine isWordEntrance_of_forall (Tm := fun m => (τ m ω : ℝ≥0∞)) hω fun t ht => ?_
  obtain ⟨t', htt', ht'T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  obtain ⟨m, hm⟩ := hτex ω t' ht'T
  exact ⟨m, htt'.trans_le (ENNReal.coe_le_coe.2 hm)⟩

/-- **The path conditions of Definition 2.1 before the lifetime hold almost surely** (`Aux125.IsForcePathPre`; the
threshold condition fails because all side partial sums exceed `−2`, specification p. 397). -/
theorem ae_isForcePathPre_of_hasPhaseMeans [IsProbabilityMeasure P] [𝓕.IsRightContinuous] (hk : 4 < k)
    (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    (hrL' : ρL 0 < 2 * (k / 2 - 2) - 2) (hrR' : ρR 0 < 2 * (k / 2 - 2) - 2)
    (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hunb : ∀ ω (M : ℝ), ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    (hpre : IsPrefixAdapted 𝓕 γ) (hxLm : Measurable[𝓕 0] xL) (hxRm : Measurable[𝓕 0] xR)
    (hseedL : ∀ ω, xL ω 0 = 0) (hseedR : ∀ ω, xR ω 0 = 0)
    (hxLd : ∀ ω (i : Fin nL), xL ω i.succ < 0) (hxRd : ∀ ω (j : Fin nR), 0 < xR ω j.succ)
    (hxLi : ∀ ω, Antitone (xL ω)) (hxRi : ∀ ω, Monotone (xR ω))
    (hd : ∀ (t : ℝ≥0) ω, 0 < t → (t : WithTop ℝ≥0) < capLife (γ ω) → ∃ n : ℤ, d t ω = n * phaseStep k)
    (hM : HasPhaseMeansBefore k ρL ρR P 𝓕 (fun t ω => segDriver (γ ω) t) xL xR d (fun ω => capLife (γ ω))) :
    ∀ᵐ ω ∂P, Aux125.IsForcePathPre (xL ω) (xR ω) ρL ρR (segDriver (γ ω))
      (fun i t => geomLW (fun t ω => segDriver (γ ω) t) xL i t ω)
      (fun j t => geomRW (fun t ω => segDriver (γ ω) t) xR j t ω) (capLife (γ ω)) := by
  filter_upwards [ae_isWordEntrance_of_hasPhaseMeans hk hsL hsR hrL' hrR' hγ hunb hpre hxLm hxRm hseedL hseedR hxLd
    hxRd hxLi hxRi hd hM] with ω hE
  exact isForcePathPre_of_isWordEntrance hE fun t ht => not_thresholdCondition_of_partialSums
    (hE.antitone_vL t ht) (hE.vL_le_w t ht) (hE.monotone_vR t ht) (hE.w_le_vR t ht) hsL hsR

/-- **Aux. lemma 125: the relative lifetime is infinite almost surely** (specification p. 397, "Thus `ζ = ∞`"), from
Aux. lemma 122's hypotheses before the lifetime alone: the martingale part of the driver stopped at the announcing
times `τₘ` of the coordinates is a bounded martingale with compensated square a martingale
(`martingale_martProc_stop`), and the path conditions hold almost surely (`ae_isForcePathPre_of_hasPhaseMeans`). -/
theorem ae_capLife_eq_top_of_hasPhaseMeans [IsProbabilityMeasure P] [𝓕.IsRightContinuous] (hk : 4 < k)
    (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    (hrL' : ρL 0 < 2 * (k / 2 - 2) - 2) (hrR' : ρR 0 < 2 * (k / 2 - 2) - 2)
    (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hunb : ∀ ω (M : ℝ), ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    (hpre : IsPrefixAdapted 𝓕 γ) (hxLm : Measurable[𝓕 0] xL) (hxRm : Measurable[𝓕 0] xR)
    (hseedL : ∀ ω, xL ω 0 = 0) (hseedR : ∀ ω, xR ω 0 = 0)
    (hxLd : ∀ ω (i : Fin nL), xL ω i.succ < 0) (hxRd : ∀ ω (j : Fin nR), 0 < xR ω j.succ)
    (hxLi : ∀ ω, Antitone (xL ω)) (hxRi : ∀ ω, Monotone (xR ω))
    (hd : ∀ (t : ℝ≥0) ω, 0 < t → (t : WithTop ℝ≥0) < capLife (γ ω) → ∃ n : ℤ, d t ω = n * phaseStep k)
    (hM : HasPhaseMeansBefore k ρL ρR P 𝓕 (fun t ω => segDriver (γ ω) t) xL xR d (fun ω => capLife (γ ω))) :
    ∀ᵐ ω ∂P, capLife (γ ω) = ⊤ := by
  have hk0 : 0 < k := by linarith
  set W : ℝ≥0 → Ω → ℝ := fun t ω => segDriver (γ ω) t with hWdef
  have hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < capLife (γ ω)} := fun ω =>
    (hγ ω).segDriver_spec.2.1
  have hW0 : ∀ ω, W 0 ω = 0 := fun ω => (hγ ω).segDriver_spec.1
  obtain ⟨τ, hτ, hτT, hτm, hτex, hτN, hτb⟩ := exists_announcing_coords hγ hunb hpre hxLm hxRm
  set ρ := jointρ ρL ρR with hρdef
  set V := jointV (geomLW W xL) (geomRW W xR) with hVdef
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.2 hk0
  have hmart := fun m => martingale_martProc_stop (P := P) (σ := τ m) (N := m) hk
    (neg_two_lt_zero_of_partialSums hsL) hrL' (neg_two_lt_zero_of_partialSums hsR) hrR' hW0 hWc
    (stronglyAdapted_killAt_segDriver hγ hpre) (fun ω t ht => killAt_segDriver_of_lt ht) hxLm hxRm hseedL hseedR
    hxLd hxRd hxLi hxRi hd hM (hτ m) (hτT m) (hτN m) (hτb m)
  refine ae_capLife_eq_top_of_martProc_ae (a := k) (VL := geomLW W xL) (VR := geomRW W xR) hγ hunb hk0
    (ae_isForcePathPre_of_hasPhaseMeans hk hsL hsR hrL' hrR' hγ hunb hpre hxLm hxRm hseedL hseedR hxLd hxRd hxLi
      hxRi hd hM) (sum_ne_neg_two_of_partialSums hsL) (sum_ne_neg_two_of_partialSums hsR) (σ := τ) hτ
    (fun m ω => hτT m ω) hτm (fun ω t ht => hτex ω t ht)
    (fun ω => (continuousOn_martProc_of_lt hWc ρ xL xR ω).div_const _) (fun m => ?_) (fun m => ?_) (fun m => ?_)
  · refine ⟨(2 * m + (∑ j, |ρ j|) * m) / Real.sqrt k, fun ω t ht => ?_⟩
    have hC : 0 ≤ 2 * (m : ℝ) + (∑ j, |ρ j|) * m := by positivity
    rw [abs_div, abs_of_pos hsk]
    refine div_le_div_of_nonneg_right ?_ hsk.le
    rcases (zero_le : (0 : ℝ≥0) ≤ τ m ω).eq_or_lt with h0 | h0
    · have ht0 : t = 0 := le_antisymm (ht.trans h0.ge) zero_le
      subst ht0
      simp only [martProc, martValue, sub_self, mul_zero, Finset.sum_const_zero, add_zero, abs_zero]
      exact hC
    · exact abs_martProc_le (hτb m ω h0 t ht) (hτb m ω h0 0 zero_le)
  · have e : (fun t ω => martProc ρ W V (min t (τ m ω)) ω / Real.sqrt k) =
        (Real.sqrt k)⁻¹ • fun t ω => martProc ρ W V (min t (τ m ω)) ω := by
      funext t ω
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact (hmart m).1.smul _
  · have e : (fun t ω => (martProc ρ W V (min t (τ m ω)) ω / Real.sqrt k) ^ 2 - ((min t (τ m ω) : ℝ≥0) : ℝ)) =
        k⁻¹ • fun t ω => martProc ρ W V (min t (τ m ω)) ω ^ 2 - k * ((min t (τ m ω) : ℝ≥0) : ℝ) := by
      funext t ω
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [div_pow, Real.sq_sqrt hk0.le]
      field_simp
    rw [e]
    exact (hmart m).2.smul _

end Main

end InteractingSLE.Sec7.PocketMartLife
