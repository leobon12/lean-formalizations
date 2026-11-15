/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.Carrier
import InteractingSLE.Spec.Sec4.ZeroMarksAvoid
import InteractingSLE.Spec.Sec4.Prob41Avoid
import InteractingSLE.Spec.Sec4.Prob41Trace
import InteractingSLE.Spec.Sec4.Special2Order

/-!
# The counterflow after mapping out a segment of another curve: the first-exit step

Packet PROVE-SEC5-E. The proofs of Lemma 4.7 (p. 118), Lemma 5.7 (p. 138) and Proposition 5.9 (p. 140) apply
Lemma 4.5 to the counterflow `η′` **after mapping out an initial segment `η([0, σ])` of a different curve**: "We apply a
conformal transformation `ψ : 𝒮 ∖ η([0, σ]) → 𝒮` which fixes `±∞` and sends `η(σ)` to `0`; the boundary data for the
GFF which describes the evolution of `ψ(η′)` is as in the right panel of Figure 5.5 … Lemma 4.5 thus implies that
`ψ(η′)` does not hit `∂_L𝒮 ∖ {0}` and exits `𝒮` at `0`. This implies that `η′` almost surely exits
`𝒮 ∖ η([0, σ])` at `η(σ)`."

The source's step "the boundary data for the GFF which describes the evolution of `ψ(η′)` is …" is a statement about
the **regular conditional law** given the explored segment (Lemma 4.7's proof: "Proposition 3.7 and Proposition 3.8
together tell us that the boundary data for the conditional law of `h` given both `η|[0,τ]` and `η′|[0,t]` … agree with
those of the conditional law of `h` given just `η|[0,τ]` … This allows us to use Theorem 2.4 to compute the
conditional law of `η′` given `η([0, τ])`"). `Lemma57.lean` states that conclusion as a named input in the kernel form
of the first-contact restart carrier (`Restart.FirstContactRestartStatement`); this file proves, for any such kernel,
everything that follows from it:

* the **chart datum** `(Q, c)` of the conditional counterflow: `c` is a boundary word (the boundary data of the
  counterflow's parameter field in its restart chart, normalized so that the counterflow starts at `0`, its target
  `η(σ)` is at `∞`, the strip end `+∞` is at `−1` and the strip end `−∞` is at `Q`, as for the chart `M_q` of
  `Sec4.IsStripCounterflowDriver`); `IsRestartTargetDatum k (Q, c)` records the heights Lemma 4.5 needs (Figure 5.5,
  right panel, with "`−λ − θᵢχ ≤ −λ′` and `λ − θᵢχ ≥ λ′`" and the upper bounds `a′, b′ ≥ λ′ + πχ`);
* the **pathwise chart continuation** `IsCounterflowChartContinuation`: the inverse chart `ψ` maps `ℍ` and the real
  points of `(−1, Q]` off `∂_L𝒮 ∪ η([0, σ])` and sends `∞` to the tip; a capacity clock identifies the physical
  completed counterflow `ξ` with `ψ ∘ γ` up to its first exit, at which the chart path reaches the chart image
  `(−∞, −1] ∪ (Q, ∞)` of `∂_L𝒮 ∪ η([0, σ])` unless it never exits;
* **`isFirstHitPoint_of_isCounterflowChartContinuation`** (deterministic): if the chart path avoids the target arcs,
  stays in `ℍ̄` and tends to `∞`, the physical counterflow first hits `∂_L𝒮 ∪ η([0, σ])` at the tip;
* `IsFlowLineTraceLaw k c Q γ U`: under `Q`, `γ` is the trace of an integrated `SLE_k(ρ)` evolution from the
  force word of the flow line of a field with data `c` (what Theorem 2.4's converse delivers; implied by the frozen
  `IsFlowLine`, `IsFlowLine.isFlowLineTraceLaw`);
* **`ae_restartEvent_of_isFlowLineTraceLaw`** (Lemma 4.5 under one conditional law, from Aux. lemma 7): such a trace,
  for a datum satisfying `IsRestartTargetDatum`, has infinite lifetime, never meets `(−∞, −1] ∪ [Q, ∞)`, stays in
  `ℍ̄` and tends to `∞`;
* the measurability of these path events on a canonical space (`measurableSet_restartEvent`) and the integration of
  a product event against a disintegration (`ae_mem_of_compProd_eq_prod`);
* **`ae_isFirstHitPoint_of_restart`**: from a disintegration of the restart variable over the datum, Lemma 4.5 for
  almost every datum and the pathwise continuation, almost surely the counterflow first hits `∂_L𝒮 ∪ η([0, σ])` at
  `η(σ)` (input (b) of Remark 4.8, the first-exit statement of Lemma 5.7's proof).

The named carrier for Lemma 5.7 and the assembly are in `Lemma57.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped Real NNReal ENNReal
open QuantumZipper (H chiC)

universe u v

namespace InteractingSLE.Sec5.MarkovOther

open Sec4 Restart

/-! ### The pathwise chart continuation and the first hit -/

/-- **The counterflow written in its restart chart after an explored set `A` with tip `z`** (pathwise part of the
restart: Lemma 5.7's proof, "We apply a conformal transformation `ψ : 𝒮 ∖ η([0, σ]) → 𝒮` …", read in the
exponential chart `E`, where `∂_L𝒮` is `lowerLineH`). There are an inverse chart `ψ`, an exit time `U′ ≤ U` of the
chart path `γ` (lifetime `U`), a capacity clock `c` and a physical exit time `s₁ ∈ (0, 1]` with:
* `ψ` maps `ℍ` and the real points of `(−1, Q]` off `∂_L𝒮 ∪ A` (they go to the remaining domain, to the upper
  boundary around the seed, and to the strip end `−∞`);
* `ψ` sends `∞` to the tip: `ψ ∘ f → z` along every path `f` in `ℍ̄` with `‖f‖ → ∞`;
* `c` is strictly increasing on `[0, U′)` and maps it onto `[0, s₁)`; the completed counterflow is
  `ξ ∘ c = ψ ∘ γ` there;
* if the exit time `U′` is finite, the chart path is then on the chart image `(−∞, −1] ∪ (Q, ∞)` of
  `∂_L𝒮 ∪ A` (the restart is valid until the first exit). -/
def IsCounterflowChartContinuation (A : Set ℂ) (z : ℂ) (ξ : ℝ → ℂ) (Q : ℝ) (γ : ℝ≥0 → ℂ)
    (U : ℝ≥0∞) : Prop :=
  ∃ (ψ : ℂ → ℂ) (U' : ℝ≥0∞) (c : ℝ≥0 → ℝ) (s₁ : ℝ),
    (∀ w ∈ H, ψ w ∉ lowerLineH ∪ A) ∧
    (∀ x : ℝ, -1 < x → x ≤ Q → ψ x ∉ lowerLineH ∪ A) ∧
    (∀ f : ℝ≥0 → ℂ, (∀ t, 0 ≤ (f t).im) → Tendsto (fun t => ‖f t‖) atTop atTop →
      Tendsto (fun t => ψ (f t)) atTop (𝓝 z)) ∧
    U' ≤ U ∧ 0 < s₁ ∧ s₁ ≤ 1 ∧ StrictMonoOn c {u | (u : ℝ≥0∞) < U'} ∧
    c '' {u | (u : ℝ≥0∞) < U'} = Ico 0 s₁ ∧
    (∀ u : ℝ≥0, (u : ℝ≥0∞) < U' → ξ (c u) = ψ (γ u)) ∧
    (U' < ⊤ → γ U'.toNNReal ∈ ((↑) : ℝ → ℂ) '' (Iic (-1) ∪ Ioi Q))

/-- A point of `ℂ` with zero imaginary part is the real number `re`. -/
theorem eq_ofReal_re_of_im_eq_zero {w : ℂ} (hw : w.im = 0) : w = (w.re : ℂ) :=
  Complex.ext rfl (by simp [hw])

/-- **The first exit from the pathwise continuation** (deterministic). If the chart path avoids the chart image
`(−∞, −1] ∪ (Q, ∞)` of `∂_L𝒮 ∪ A`, stays in `ℍ̄` and tends to `∞`, then the physical completed counterflow `ξ`
(continuous on `[0, 1]`) first hits `∂_L𝒮 ∪ A` at the tip `z ∈ A`: Lemma 5.7's "`η′` almost surely exits
`𝒮 ∖ η([0, σ])` at `η(σ)`", pathwise. -/
theorem isFirstHitPoint_of_isCounterflowChartContinuation {A : Set ℂ} {z : ℂ} {ξ : ℝ → ℂ} {Q : ℝ}
    {γ : ℝ≥0 → ℂ} {U : ℝ≥0∞} (h : IsCounterflowChartContinuation A z ξ Q γ U)
    (hξ : ContinuousOn ξ (Icc 0 1)) (hz : z ∈ A)
    (hav : ∀ t, γ t ∉ ((↑) : ℝ → ℂ) '' (Iic (-1) ∪ Ioi Q)) (him : ∀ t, 0 ≤ (γ t).im)
    (htr : Tendsto (fun t => ‖γ t‖) atTop atTop) :
    IsFirstHitPoint ξ 1 (lowerLineH ∪ A) z := by
  obtain ⟨ψ, U', c, s₁, hH, hR, hlim, -, hs₁, hs₁1, hmono, himg, heq, hstop⟩ := h
  have hU' : U' = ⊤ := by
    by_contra hne
    exact hav _ (hstop (lt_top_iff_ne_top.2 hne))
  subst hU'
  have hall : ∀ u : ℝ≥0, u ∈ {u : ℝ≥0 | (u : ℝ≥0∞) < ⊤} := fun u => ENNReal.coe_lt_top
  have hcmem : ∀ u, c u ∈ Ico 0 s₁ := fun u => himg ▸ mem_image_of_mem c (hall u)
  -- before the exit, the counterflow avoids `∂_L𝒮 ∪ A`
  have hbefore : ∀ v ∈ Ico (0 : ℝ) s₁, ξ v ∉ lowerLineH ∪ A := by
    intro v hv
    rw [← himg] at hv
    obtain ⟨u, -, rfl⟩ := hv
    rw [heq u (hall u)]
    rcases (him u).lt_or_eq with hpos | hzero
    · exact hH _ hpos
    · have hre := eq_ofReal_re_of_im_eq_zero hzero.symm
      have hx : (γ u).re ∉ Iic (-1) ∪ Ioi Q := fun hx => hav u ⟨_, hx, hre.symm⟩
      simp only [mem_union, mem_Iic, mem_Ioi, not_or, not_le, not_lt] at hx
      rw [hre]
      exact hR _ hx.1 hx.2
  -- the clock tends to the exit time
  have hmono' : Monotone c := fun a b hab => hmono.monotoneOn (hall a) (hall b) hab
  have hsup : (⨆ u, c u) = s₁ := by
    refine ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun u => (hcmem u).2.le) fun w hw => ?_
    rcases lt_or_ge w 0 with hw0 | hw0
    · exact ⟨0, hw0.trans_le (hcmem 0).1⟩
    · have hwm : w ∈ c '' {u : ℝ≥0 | (u : ℝ≥0∞) < ⊤} := himg ▸ ⟨hw0, hw⟩
      obtain ⟨u, -, hu⟩ := hwm
      obtain ⟨v, hv⟩ : ∃ v, w < c v := by
        by_contra hne
        push Not at hne
        have hu1 := hcmem (u + 1)
        have : c u < c (u + 1) := hmono (hall u) (hall _) (by simp)
        linarith [hne (u + 1)]
      exact ⟨v, hv⟩
  have htend : Tendsto c atTop (𝓝 s₁) := by
    rw [← hsup]
    exact tendsto_atTop_ciSup hmono' ⟨s₁, by rintro _ ⟨u, rfl⟩; exact (hcmem u).2.le⟩
  have htendW : Tendsto c atTop (𝓝[Icc 0 1] s₁) :=
    tendsto_nhdsWithin_iff.2 ⟨htend, Eventually.of_forall fun u =>
      ⟨(hcmem u).1, (hcmem u).2.le.trans hs₁1⟩⟩
  have h1 : Tendsto (fun u => ξ (c u)) atTop (𝓝 (ξ s₁)) :=
    (hξ s₁ ⟨hs₁.le, hs₁1⟩).tendsto.comp htendW
  have h2 : Tendsto (fun u => ξ (c u)) atTop (𝓝 z) := by
    have h := hlim γ him htr
    refine h.congr fun u => ?_
    rw [heq u (hall u)]
  have hz' : ξ s₁ = z := tendsto_nhds_unique h1 h2
  exact ⟨s₁, ⟨hs₁.le, hs₁1⟩, hz', Or.inr (hz' ▸ hz), hbefore⟩

/-! ### Rational times -/

/-- The rational times, as points of `ℝ≥0` (negative rationals give `0`). -/
def ratTime (q : ℚ) : ℝ≥0 := (q : ℝ).toNNReal

/-- Every time is a limit of rational times below it. -/
theorem exists_ratTime_tendsto_le (t : ℝ≥0) :
    ∃ q : ℕ → ℚ, (∀ n, ratTime (q n) ≤ t) ∧ Tendsto (fun n => ratTime (q n)) atTop (𝓝 t) := by
  have hq : ∀ n : ℕ, ∃ q : ℚ, (t : ℝ) - 1 / ((n : ℝ) + 1) < q ∧ (q : ℝ) < t := fun n =>
    exists_rat_btwn (by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                        linarith)
  choose q hq using hq
  refine ⟨q, fun n => ?_, ?_⟩
  · rw [ratTime, ← Real.toNNReal_coe (r := t)]
    exact Real.toNNReal_le_toNNReal (hq n).2.le
  · have hR : Tendsto (fun n => ((q n : ℚ) : ℝ)) atTop (𝓝 (t : ℝ)) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds (fun n => (hq n).1.le)
        fun n => (hq n).2.le
      have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using (tendsto_const_nhds (x := (t : ℝ))).sub h
    have := (continuous_real_toNNReal.tendsto (t : ℝ)).comp hR
    simpa [ratTime, Function.comp_def] using this

/-- Every time is a limit of rational times above it. -/
theorem exists_ratTime_tendsto_ge (t : ℝ≥0) :
    ∃ q : ℕ → ℚ, (∀ n, t ≤ ratTime (q n)) ∧ Tendsto (fun n => ratTime (q n)) atTop (𝓝 t) := by
  have hq : ∀ n : ℕ, ∃ q : ℚ, (t : ℝ) < q ∧ (q : ℝ) < t + 1 / ((n : ℝ) + 1) := fun n =>
    exists_rat_btwn (by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                        linarith)
  choose q hq using hq
  refine ⟨q, fun n => ?_, ?_⟩
  · rw [ratTime, ← Real.toNNReal_coe (r := t)]
    exact Real.toNNReal_le_toNNReal (hq n).1.le
  · have hR : Tendsto (fun n => ((q n : ℚ) : ℝ)) atTop (𝓝 (t : ℝ)) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => (hq n).1.le)
        fun n => (hq n).2.le
      have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using (tendsto_const_nhds (x := (t : ℝ))).add h
    have := (continuous_real_toNNReal.tendsto (t : ℝ)).comp hR
    simpa [ratTime, Function.comp_def] using this

variable {Y : Type*} [TopologicalSpace Y]

/-- A closed condition along a continuous path holds on `[0, N]` once it holds at the rational times there. -/
theorem forall_le_of_ratTime {g : ℝ≥0 → Y} (hg : Continuous g) {C : Set Y} (hC : IsClosed C) {N : ℝ≥0}
    (h : ∀ q : ℚ, ratTime q ≤ N → g (ratTime q) ∈ C) {t : ℝ≥0} (ht : t ≤ N) : g t ∈ C := by
  obtain ⟨q, hle, hq⟩ := exists_ratTime_tendsto_le t
  exact hC.mem_of_tendsto ((hg.tendsto t).comp hq)
    (Eventually.of_forall fun n => h _ ((hle n).trans ht))

/-- A closed condition along a continuous path holds on `[a, ∞)` once it holds at the rational times there. -/
theorem forall_ge_of_ratTime {g : ℝ≥0 → Y} (hg : Continuous g) {C : Set Y} (hC : IsClosed C) {a : ℝ≥0}
    (h : ∀ q : ℚ, a ≤ ratTime q → g (ratTime q) ∈ C) {t : ℝ≥0} (ht : a ≤ t) : g t ∈ C := by
  obtain ⟨q, hge, hq⟩ := exists_ratTime_tendsto_ge t
  exact hC.mem_of_tendsto ((hg.tendsto t).comp hq)
    (Eventually.of_forall fun n => h _ (ht.trans (hge n)))

/-! ### Measurable path events -/

section Events

variable {S : Type*} [MeasurableSpace S] {γ : S → ℝ≥0 → ℂ}

theorem isCompact_Iic_nnreal' (c : ℝ≥0) : IsCompact (Iic c) := by
  rw [← Set.Icc_bot]; exact isCompact_Icc

/-- **Avoiding a closed set is a countable condition** for continuous paths: on `G`, where the paths are
continuous, `{∀ t, γ t ∉ F}` is `⋂_N ⋃_m ⋂_q {infDist(γ q, F) ≥ 1/(m+1)}` over the rational times `q ≤ N`. -/
theorem measurableSet_inter_forall_notMem (hγm : ∀ t, Measurable fun s => γ s t) {G : Set S}
    (hG : MeasurableSet G) (hγc : ∀ s ∈ G, Continuous (γ s)) {F : Set ℂ} (hF : IsClosed F)
    (hFne : F.Nonempty) : MeasurableSet (G ∩ {s | ∀ t, γ s t ∉ F}) := by
  have heq : G ∩ {s | ∀ t, γ s t ∉ F} = G ∩ ⋂ N : ℕ, ⋃ m : ℕ, ⋂ q : ℚ,
      {s | ratTime q ≤ N → 1 / ((m : ℝ) + 1) ≤ infDist (γ s (ratTime q)) F} := by
    ext s
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_iUnion]
    refine and_congr_right fun hs => ⟨fun h N => ?_, fun h t => ?_⟩
    · have hcont : Continuous fun t => infDist (γ s t) F :=
        (continuous_infDist_pt F).comp (hγc s hs)
      obtain ⟨t₀, -, hmin⟩ := (isCompact_Iic_nnreal' (N : ℝ≥0)).exists_isMinOn
        ⟨0, show (0 : ℝ≥0) ≤ (N : ℝ≥0) from bot_le⟩ hcont.continuousOn
      have hpos : 0 < infDist (γ s t₀) F := (hF.notMem_iff_infDist_pos hFne).1 (h t₀)
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
      exact ⟨m, fun q hq => hm.le.trans (hmin hq)⟩
    · obtain ⟨m, hm⟩ := h ⌈(t : ℝ)⌉₊
      have hcont : Continuous fun t => infDist (γ s t) F :=
        (continuous_infDist_pt F).comp (hγc s hs)
      have htN : t ≤ (⌈(t : ℝ)⌉₊ : ℝ≥0) := by
        rw [← NNReal.coe_le_coe]; push_cast; exact Nat.le_ceil _
      have hle := forall_le_of_ratTime hcont (isClosed_Ici (a := 1 / ((m : ℝ) + 1)))
        (fun q hq => hm q hq) htN
      intro htF
      rw [mem_Ici, infDist_zero_of_mem htF] at hle
      have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      linarith
  rw [heq]
  refine hG.inter (MeasurableSet.iInter fun N => MeasurableSet.iUnion fun m =>
    MeasurableSet.iInter fun q => ?_)
  by_cases hq : ratTime q ≤ (N : ℝ≥0)
  · simp only [hq, true_implies]
    exact measurableSet_le measurable_const
      ((continuous_infDist_pt F).measurable.comp (hγm _))
  · simp [hq]

/-- The paths stay in `ℍ̄`: a countable condition for continuous paths. -/
theorem measurableSet_inter_forall_im_nonneg (hγm : ∀ t, Measurable fun s => γ s t) {G : Set S}
    (hG : MeasurableSet G) (hγc : ∀ s ∈ G, Continuous (γ s)) :
    MeasurableSet (G ∩ {s | ∀ t, 0 ≤ (γ s t).im}) := by
  have hC : IsClosed {w : ℂ | 0 ≤ w.im} := isClosed_le continuous_const Complex.continuous_im
  have heq : G ∩ {s | ∀ t, 0 ≤ (γ s t).im} = G ∩ ⋂ q : ℚ, {s | 0 ≤ (γ s (ratTime q)).im} := by
    ext s
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iInter]
    exact and_congr_right fun hs => ⟨fun h q => h _, fun h t =>
      forall_ge_of_ratTime (hγc s hs) hC (a := 0) (fun q _ => h q) bot_le⟩
  rw [heq]
  exact hG.inter (MeasurableSet.iInter fun q =>
    measurableSet_le measurable_const (Complex.measurable_im.comp (hγm _)))

/-- `‖f‖ → ∞` along `ℝ≥0`, with natural thresholds. -/
theorem tendsto_norm_atTop_iff_nat {f : ℝ≥0 → ℂ} :
    Tendsto (fun t => ‖f t‖) atTop atTop ↔
      ∀ R : ℕ, ∃ T : ℕ, ∀ t : ℝ≥0, (T : ℝ≥0) ≤ t → (R : ℝ) ≤ ‖f t‖ := by
  rw [tendsto_atTop_atTop]
  constructor
  · intro h R
    obtain ⟨i, hi⟩ := h R
    refine ⟨⌈(i : ℝ)⌉₊, fun t ht => hi t ?_⟩
    refine le_trans ?_ ht
    rw [← NNReal.coe_le_coe]; push_cast; exact Nat.le_ceil _
  · intro h b
    obtain ⟨T, hT⟩ := h ⌈b⌉₊
    exact ⟨T, fun t ht => (Nat.le_ceil b).trans (hT t ht)⟩

/-- Transience of continuous paths is a countable condition. -/
theorem measurableSet_inter_tendsto (hγm : ∀ t, Measurable fun s => γ s t) {G : Set S}
    (hG : MeasurableSet G) (hγc : ∀ s ∈ G, Continuous (γ s)) :
    MeasurableSet (G ∩ {s | Tendsto (fun t => ‖γ s t‖) atTop atTop}) := by
  have heq : G ∩ {s | Tendsto (fun t => ‖γ s t‖) atTop atTop} = G ∩ ⋂ R : ℕ, ⋃ T : ℕ, ⋂ q : ℚ,
      {s | (T : ℝ≥0) ≤ ratTime q → (R : ℝ) ≤ ‖γ s (ratTime q)‖} := by
    ext s
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_iUnion, tendsto_norm_atTop_iff_nat]
    refine and_congr_right fun hs => ⟨fun h R => ?_, fun h R => ?_⟩
    · obtain ⟨T, hT⟩ := h R
      exact ⟨T, fun q hq => hT _ hq⟩
    · obtain ⟨T, hT⟩ := h R
      exact ⟨T, fun t ht => forall_ge_of_ratTime (hγc s hs)
        (isClosed_le continuous_const continuous_norm) (fun q hq => hT q hq) ht⟩
  rw [heq]
  refine hG.inter (MeasurableSet.iInter fun R => MeasurableSet.iUnion fun T =>
    MeasurableSet.iInter fun q => ?_)
  by_cases hq : (T : ℝ≥0) ≤ ratTime q
  · simp only [hq, true_implies]
    exact measurableSet_le measurable_const (continuous_norm.measurable.comp (hγm _))
  · simp [hq]

/-- The chart image `(−∞, −1] ∪ [r, ∞)` of the target arcs, as a closed subset of `ℂ`. -/
def targetArcs (r : ℝ) : Set ℂ := ((↑) : ℝ → ℂ) '' (Iic (-1) ∪ Ici r)

theorem isClosed_targetArcs (r : ℝ) : IsClosed (targetArcs r) :=
  Complex.isometry_ofReal.isClosedEmbedding.isClosedMap _ (isClosed_Iic.union isClosed_Ici)

theorem targetArcs_nonempty (r : ℝ) : (targetArcs r).Nonempty := ⟨_, -1, Or.inl (show (-1 : ℝ) ≤ -1 from le_rfl), rfl⟩

/-- **The restart event at level `r`**: infinite lifetime, no visit to `(−∞, −1] ∪ [r, ∞)`, values in `ℍ̄` and
`‖γ‖ → ∞`. -/
def restartEvent (γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞) (r : ℝ) : Set S :=
  {s | U s = ⊤ ∧ (∀ t, γ s t ∉ targetArcs r) ∧ (∀ t, 0 ≤ (γ s t).im) ∧
    Tendsto (fun t => ‖γ s t‖) atTop atTop}

/-- The restart event is measurable on a space of coordinates continuous up to their lifetimes. -/
theorem measurableSet_restartEvent (hγm : ∀ t, Measurable fun s => γ s t) {U : S → ℝ≥0∞}
    (hUm : Measurable U) (hγc : ∀ s, ContinuousOn (γ s) {u | (u : ℝ≥0∞) ≤ U s}) (r : ℝ) :
    MeasurableSet (restartEvent γ U r) := by
  set G := {s | U s = ⊤} with hGdef
  have hG : MeasurableSet G := hUm (measurableSet_singleton ⊤)
  have hc : ∀ s ∈ G, Continuous (γ s) := fun s hs => by
    have h := hγc s
    rw [show {u : ℝ≥0 | (u : ℝ≥0∞) ≤ U s} = univ from eq_univ_of_forall fun u => by
      simp only [mem_ofPred_eq, show U s = ⊤ from hs, le_top]] at h
    exact continuousOn_univ.1 h
  have heq : restartEvent γ U r = (G ∩ {s | ∀ t, γ s t ∉ targetArcs r}) ∩
      ((G ∩ {s | ∀ t, 0 ≤ (γ s t).im}) ∩ (G ∩ {s | Tendsto (fun t => ‖γ s t‖) atTop atTop})) := by
    ext s
    simp only [restartEvent, mem_ofPred_eq, mem_inter_iff, hGdef]
    tauto
  rw [heq]
  exact (measurableSet_inter_forall_notMem hγm hG hc (isClosed_targetArcs r)
    (targetArcs_nonempty r)).inter ((measurableSet_inter_forall_im_nonneg hγm hG hc).inter
      (measurableSet_inter_tendsto hγm hG hc))

end Events

/-! ### Integrating a product event against a disintegration -/

/-- **Integrating a measurable event of the datum and the restart variable.** If `K` disintegrates the joint law
of `(β, X)` on `M` and a measurable `E ⊆ C × S` has, for almost every datum `c`, `K c`-almost every `s` with
`(c, s) ∈ E`, then almost surely on `M`, `(β, X) ∈ E`. -/
theorem ae_mem_of_compProd_eq_prod {Ω C S : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    [MeasurableSpace S] {P : Measure Ω} [IsFiniteMeasure P] {M : Set Ω} (hM : MeasurableSet M)
    {β : Ω → C} {X : Ω → S} (hβ : Measurable β) (hX : Measurable X) {K : Kernel C S} [IsMarkovKernel K]
    (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K)
    {E : Set (C × S)} (hE : MeasurableSet E) (hK : ∀ᵐ c ∂(P.restrict M).map β, ∀ᵐ s ∂(K c), (c, s) ∈ E) :
    ∀ᵐ ω ∂P, ω ∈ M → (β ω, X ω) ∈ E := by
  have hKc : ∀ᵐ c ∂(P.restrict M).map β, K c (Prod.mk c ⁻¹' Eᶜ) = 0 := by
    filter_upwards [hK] with c hc
    exact ae_iff.1 hc
  have hzero : (P.restrict M) ((fun ω => (β ω, X ω)) ⁻¹' Eᶜ) = 0 := by
    rw [← Measure.map_apply (hβ.prodMk hX) hE.compl, hlaw, Measure.compProd_apply hE.compl]
    exact lintegral_eq_zero_of_ae_eq_zero hKc
  rw [← ae_restrict_iff' hM]
  exact ae_iff.2 hzero

/-! ### Lemma 4.5 under one conditional law -/

/-- **The heights Lemma 4.5 needs, on the datum `(Q, c)` of the conditional counterflow** (parameter `k = κ′`). `c`
is the boundary word of the counterflow's parameter field in its normalized restart chart (start `0`, target `∞`,
strip ends at `−1` and `Q`): Remark 4.1's bounds `c ≤ −Λ + πX` left of `0` and `c ≥ Λ − πX` right of `0` past the
first height different from `∓Λ` (the form of `Sec4.IsFlowLine.ae_tendsto_of_aux7_of_nonzero`), and a height
different from `−Λ` in `[−1, 0)` and one different from `Λ` in `(0, Q]`, so that the target arcs `(−∞, −1]` and
`[Q, ∞)` lie beyond them (Figure 5.5, right panel: the data around the start come from the upper boundary data
`a′, b′ ≥ λ′ + πχ`, which are not critical for `κ′`). -/
def IsRestartTargetDatum (k : ℝ) (d : ℝ × BoundaryWord) : Prop :=
  (∀ x : ℝ, x < 0 → x ∉ d.2.jumps →
      (∃ y, x ≤ y ∧ y < 0 ∧ y ∉ d.2.jumps ∧ d.2.fn y ≠ -sleLambda k) →
        d.2.fn x ≤ -sleLambda k + π * chiC k) ∧
    (∀ x : ℝ, 0 < x → x ∉ d.2.jumps →
      (∃ y, 0 < y ∧ y ≤ x ∧ y ∉ d.2.jumps ∧ d.2.fn y ≠ sleLambda k) →
        sleLambda k - π * chiC k ≤ d.2.fn x) ∧
    (∃ y, -1 ≤ y ∧ y < 0 ∧ y ∉ d.2.jumps ∧ d.2.fn y ≠ -sleLambda k) ∧
    ∃ y, 0 < y ∧ y ≤ d.1 ∧ y ∉ d.2.jumps ∧ d.2.fn y ≠ sleLambda k

/-- **The law of a flow-line trace** (the part of the frozen `IsFlowLine` that Lemma 4.5 uses, and the output of
Theorem 2.4's converse): under the law `Q`, the path `γ` (lifetime `U`) is a continuous generating trace of the driver
of an integrated `SLE_k(ρ)` evolution started from the force word of the flow line from `0` (angle `0`) of a field
with boundary word `c`. -/
def IsFlowLineTraceLaw (k : ℝ) (c : BoundaryWord) {S : Type v} [mS : MeasurableSpace S] (Q : Measure S)
    (γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞) : Prop :=
  ∃ (𝓕 : Filtration ℝ≥0 mS) (W : ℝ≥0 → S → ℝ) (VL : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → S → ℝ)
    (VR : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → S → ℝ) (B : ℝ≥0 → S → ℝ),
    IsIntegratedSLEEvolution k (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL k c.fn c.jumps 0 0) (flowLineRhoR k c.fn c.jumps 0 0) Q 𝓕 W VL VR B U ∧
    ∀ᵐ s ∂Q, IsGeneratingTrace (fun t => W t s) (U s) (γ s)

/-- A flow line of a field with boundary word `c` has the flow-line trace law. -/
theorem IsFlowLine.isFlowLineTraceLaw {k : ℝ} {c : BoundaryWord} {S : Type v} [MeasurableSpace S]
    {Q : Measure S} {Hc : S → LQGMetric.DistOn upperHalfPlaneOpens} {γ : S → ℝ≥0 → ℂ} {U : S → ℝ≥0∞}
    (hfl : IsFlowLine k c.fn c.jumps 0 0 Q Hc γ U) : IsFlowLineTraceLaw k c Q γ U := by
  obtain ⟨𝓕, W, VL, VR, B, hev, htr⟩ := IsFlowLine.exists_evolution hfl
  exact ⟨𝓕, W, VL, VR, B, hev, htr⟩

/-- **Lemma 4.5 for the conditional counterflow, under one law** (from Aux. lemma 7 for the parameter `k`): if `γ`
has the trace law of the flow line from `0` of a field whose datum satisfies `IsRestartTargetDatum k (Q, c)`, then
almost surely its lifetime is infinite, it never meets the target arcs `(−∞, −1] ∪ [Q, ∞)`, it stays in `ℍ̄` and
`‖γ‖ → ∞`. The argument of `Sec4.IsFlowLine.ae_tendsto_of_aux7_of_nonzero`, from the evolution alone. -/
theorem ae_restartEvent_of_isFlowLineTraceLaw {k : ℝ} (hk : 0 < k) (h7 : Aux7Statement.{v} k) {S : Type v}
    [MeasurableSpace S] {Q : Measure S} {γ : S → ℝ≥0 → ℂ} {U : S → ℝ≥0∞} {d : ℝ × BoundaryWord}
    (hd : IsRestartTargetDatum k d) (hlaw : IsFlowLineTraceLaw k d.2 Q γ U) :
    ∀ᵐ s ∂Q, s ∈ restartEvent γ U d.1 := by
  obtain ⟨hL, hR, ⟨y₁, hy₁, hy₁0, hy₁J, hy₁b⟩, ⟨y₂, hy₂0, hy₂, hy₂J, hy₂b⟩⟩ := hd
  obtain ⟨𝓕, W, VL, VR, B, hev, htr⟩ := hlaw
  have hb := d.2.isPiecewiseConstantBoundaryData
  have hword := Theorem15.isOrderedForceWord_flowLine d.2.fn d.2.jumps 0
  have hadm := hasAdmissibleNonzeroPartialSums_flowLine hk hb hL hR
  filter_upwards [IsIntegratedSLEEvolution.ae_trace_ne_of_hasAdmissibleNonzeroPartialSums hk hword hadm hev htr,
    IsIntegratedSLEEvolution.ae_tendsto_of_aux7_of_nonzero h7 hword hadm hev, htr, hev.2.2.2.2]
    with s ⟨hU, hav⟩ ⟨_, _, htend⟩ hη hp
  rw [hU] at hη hp
  refine ⟨hU, fun t => ?_, fun t => ?_, htend _ hη⟩
  · rintro ⟨x, hx, hxt⟩
    rcases hx with hx | hx
    · have hx' : x ≤ -1 := hx
      have hb₁ := hy₁b
      rw [← forceBoundaryData_flowLine hk hb hy₁0.ne hy₁J] at hb₁
      obtain ⟨i, hρ, hi⟩ := exists_nonzero_left_of_forceBoundaryData_ne (x := x) (by linarith) hy₁0 hb₁
      exact (hav t).1 i hρ x (by linarith) hi hxt.symm
    · have hx' : d.1 ≤ x := hx
      have hb₂ := hy₂b
      rw [← forceBoundaryData_flowLine hk hb hy₂0.ne' hy₂J] at hb₂
      obtain ⟨i, hρ, hi⟩ := exists_nonzero_right_of_forceBoundaryData_ne (x := x) (hy₂.trans hx') hy₂0 hb₂
      exact (hav t).2 i hρ x (by linarith) hi hxt.symm
  · exact im_nonneg_of_isGeneratingTrace (continuous_toNNReal_of_isIntegratedSLEPath hp) hp.1 hη t

/-! ### The first exit, almost surely -/

/-- **The first-exit statement from the restart** (input (b) of Remark 4.8 and the first-exit step of Lemma 5.7's
proof, from the conditional law of the counterflow after an explored set). Data on `(Ω, P)`: the completed
counterflow `ξ` (continuous on `[0, 1]`), the explored set `A` with tip `z ∈ A`, an event `M`, the chart datum
`β = (Q, c)` and a restart variable `X` in a space `S` with chart path `γ` and lifetime `U` (measurable, paths
continuous up to the lifetime), and a Markov kernel `K` disintegrating `(β, X)` on `M`. If for almost every datum
`d = (Q, c)` the datum has the heights of Lemma 4.5 and under `K d` the chart path has the trace law of the flow line
(parameter `k`, from `0`) of a field with data `c` (`IsFlowLineTraceLaw`), and almost surely on `M` the counterflow is the chart path in the restart chart
(`IsCounterflowChartContinuation`) on an event `G ⊆ M` (up to a null set; `G` need not be measurable), then
almost surely on `G` the counterflow first hits `∂_L𝒮 ∪ A` at `z`. -/
theorem ae_isFirstHitPoint_of_restart {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {k : ℝ} (hk : 0 < k) (h7 : Aux7Statement.{v} k) {S : Type v} [MeasurableSpace S]
    {γ : S → ℝ≥0 → ℂ} {U : S → ℝ≥0∞} (hγm : ∀ t, Measurable fun s => γ s t) (hUm : Measurable U)
    (hγc : ∀ s, ContinuousOn (γ s) {u | (u : ℝ≥0∞) ≤ U s})
    {M : Set Ω} (hM : MeasurableSet M) {β : Ω → ℝ × BoundaryWord} (hβ : Measurable β) {X : Ω → S}
    (hX : Measurable X) {K : Kernel (ℝ × BoundaryWord) S} [IsMarkovKernel K]
    (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K)
    (hK : ∀ᵐ d ∂(P.restrict M).map β, IsRestartTargetDatum k d ∧ IsFlowLineTraceLaw k d.2 (K d) γ U)
    {ξ : Ω → ℝ → ℂ} (hξ : ∀ᵐ ω ∂P, ContinuousOn (ξ ω) (Icc 0 1)) {A : Ω → Set ℂ} {z : Ω → ℂ}
    (hz : ∀ ω, z ω ∈ A ω) {G : Ω → Prop}
    (hpath : ∀ᵐ ω ∂P, G ω → ω ∈ M ∧
      IsCounterflowChartContinuation (A ω) (z ω) (ξ ω) (β ω).1 (γ (X ω)) (U (X ω))) :
    ∀ᵐ ω ∂P, G ω → IsFirstHitPoint (ξ ω) 1 (lowerLineH ∪ A ω) (z ω) := by
  -- the restart events at the rational levels, integrated back
  have hr : ∀ r : ℚ, ∀ᵐ ω ∂P, ω ∈ M → (β ω).1 < r → X ω ∈ restartEvent γ U r := by
    intro r
    set E : Set ((ℝ × BoundaryWord) × S) := {p | (r : ℝ) ≤ p.1.1} ∪ univ ×ˢ restartEvent γ U r
    have hE : MeasurableSet E :=
      (measurableSet_le measurable_const (measurable_fst.comp measurable_fst)).union
        (MeasurableSet.univ.prod (measurableSet_restartEvent hγm hUm hγc r))
    have hKE : ∀ᵐ d ∂(P.restrict M).map β, ∀ᵐ s ∂(K d), (d, s) ∈ E := by
      filter_upwards [hK] with d ⟨hd, hfl⟩
      by_cases hdr : (r : ℝ) ≤ d.1
      · exact Eventually.of_forall fun s => Or.inl hdr
      · push Not at hdr
        filter_upwards [ae_restartEvent_of_isFlowLineTraceLaw hk h7 hd hfl] with s ⟨hU, hav, him, htr⟩
        refine Or.inr ⟨mem_univ _, hU, fun t ht => hav t ?_, him, htr⟩
        obtain ⟨x, hx, hxt⟩ := ht
        refine ⟨x, ?_, hxt⟩
        rcases hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (show d.1 ≤ x from hdr.le.trans hx)
    filter_upwards [ae_mem_of_compProd_eq_prod hM hβ hX hlaw hE hKE] with ω hω hωM hlt
    rcases hω hωM with h | ⟨-, h⟩
    · exact absurd h (not_le.2 hlt)
    · exact h
  rw [← ae_all_iff] at hr
  filter_upwards [hr, hξ, hpath] with ω hrω hξω hpω hGω
  obtain ⟨hωM, hcont⟩ := hpω hGω
  -- some rational level above `Q`
  obtain ⟨r₀, hr₀⟩ := exists_rat_gt (β ω).1
  obtain ⟨hU, -, him, htr⟩ := hrω r₀ hωM hr₀
  refine isFirstHitPoint_of_isCounterflowChartContinuation hcont hξω (hz ω) (fun t => ?_) him htr
  rintro ⟨x, hx, hxt⟩
  rcases hx with hx | hx
  · obtain ⟨-, hav, -⟩ := hrω r₀ hωM hr₀
    exact hav t ⟨x, Or.inl hx, hxt⟩
  · have hx' : (β ω).1 < x := hx
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hx'
    obtain ⟨-, hav, -⟩ := hrω r hωM hr1
    exact hav t ⟨x, Or.inr (show (r : ℝ) ≤ x from hr2.le), hxt⟩

end InteractingSLE.Sec5.MarkovOther
