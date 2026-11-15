/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.NNRat.Encodable

/-!
# Global determination from measurable local restarts (Aux. lemma 52)

Packet PROVE-SEC7-A (specification §7.1, `source/spec/p241-288.md` L69–L94, pp. 244–245). Aux. lemma 52 is
the abstract stopping-time argument behind Lemma 7.5 (the `κ < 4` determining graph used by LP11): if every
determined stopped history can be extended, by a stopping time, strictly beyond its current time (unless it
has already reached `T ∧ N`), then the whole history up to `T ∧ N` is determined.

## Statement

Let `X : ℝ≥0 → Ω → E` be a process with values in a Polish space `E` whose paths are (almost surely)
continuous on `[0, T]` (including a finite endpoint `T`), where `T` is a stopping time (the lifetime) of a
filtration `𝓕`, and let `H : Ω → γ` be a random element. A history includes its stopping time:

  `𝒳_τ = (τ, (X_{q ∧ τ})_{q ∈ ℚ≥0})` (`stoppedHistory X τ`).

"`𝒳_τ` is `σ(H)`-measurable" is read with completion: `𝒳_τ` is almost surely a Borel function of `H`
(`IsAEDeterminedBy μ H (stoppedHistory X τ)`). This is the meaning of "determined by `h`" in the
specification's field-determination statements (Theorem 1.2: "a Borel function of the field, up to a
null set"); the essential-supremum argument of the proof only ever produces almost-sure identities.

Assume `X₀` is determined by `H` and the local extension property (LG1): whenever `τ ≤ T ∧ N` is a stopping
time whose history is determined by `H`, there is a stopping time `σ ≤ T ∧ N` with `σ ≥ τ`, `σ > τ` on
`{τ < T ∧ N}` (both almost surely), whose history is determined by `H`. Then `𝒳_{T ∧ N}` is determined
by `H` for every finite `N` (`isAEDeterminedBy_stoppedHistory_of_localRestart`), and so is every stopped
value `X_{t ∧ T ∧ N}` (`isAEDeterminedBy_stopped_apply_of_localRestart`).

The filtration is arbitrary (the specification uses the usual natural filtration of `X`, a special case);
the continuity of paths, the inequalities `σ ≥ τ`, `σ > τ` and the determination statements are only
needed almost surely; `H` need only be measurable. Each of these makes the theorem stronger than the
printed statement.

## Proof (the specification's, with the measure-theoretic details)

Fix `N`, let `b = T ∧ N`, and let `𝒮` be the set of stopping times `τ ≤ b` with determined history.
* `0 ∈ 𝒮` (`X₀` is determined); `𝒮` is closed under `max` (from the two recorded times one knows which
  history is longer: `stoppedHistory_max`); `𝒮` is closed under increasing limits (the supremum of
  stopping times is a stopping time; `τₙ ↑ τ` and path continuity on `[0, T]` give `X_{q ∧ τₙ} → X_{q ∧ τ}`,
  and almost-sure limits of determined variables in a Polish space are determined:
  `IsAEDeterminedBy.of_tendsto`).
* Let `a = sup {E τ : τ ∈ 𝒮} ≤ N`; take `τₙ ∈ 𝒮` with `E τₙ → a`, replace them by their successive maxima,
  and let `τ_*` be the increasing limit. Then `τ_* ∈ 𝒮` and `E τ_* = a`; for `τ ∈ 𝒮`, `τ ∨ τ_* ∈ 𝒮` has
  `E[τ ∨ τ_*] ≤ a = E τ_*`, so `τ ≤ τ_*` almost surely.
* (LG1) at `τ_*` gives `σ`; `σ ∨ τ_* ∈ 𝒮`, so `σ ≤ τ_*` a.s., while `σ > τ_*` a.s. on `{τ_* < b}`. Hence
  `τ_* = b` almost surely and `𝒳_b = 𝒳_{τ_*}` almost surely.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

/-! ### Almost-sure determination by a random element -/

section Determined

variable {Ω γ β β' : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace γ] [MeasurableSpace β]
  [MeasurableSpace β'] {μ : Measure Ω} {H : Ω → γ}

/-- `Y` is almost surely a Borel function of `H`: there is a measurable `g` with `Y = g ∘ H` almost
everywhere. Equivalently (for standard Borel targets) `Y` is measurable with respect to the
`μ`-completion of `σ(H)`. -/
def IsAEDeterminedBy (μ : Measure Ω) (H : Ω → γ) (Y : Ω → β) : Prop :=
  ∃ g : γ → β, Measurable g ∧ Y =ᵐ[μ] fun ω => g (H ω)

theorem IsAEDeterminedBy.congr_ae {Y Z : Ω → β} (hY : IsAEDeterminedBy μ H Y) (h : Y =ᵐ[μ] Z) :
    IsAEDeterminedBy μ H Z := by
  obtain ⟨g, hg, hYg⟩ := hY
  exact ⟨g, hg, h.symm.trans hYg⟩

theorem IsAEDeterminedBy.comp {Y : Ω → β} (hY : IsAEDeterminedBy μ H Y) {φ : β → β'}
    (hφ : Measurable φ) : IsAEDeterminedBy μ H fun ω => φ (Y ω) := by
  obtain ⟨g, hg, hYg⟩ := hY
  exact ⟨fun x => φ (g x), hφ.comp hg, hYg.mono fun ω h => by simp only [h]⟩

theorem isAEDeterminedBy_const (b : β) : IsAEDeterminedBy μ H fun _ => b :=
  ⟨fun _ => b, measurable_const, ae_of_all _ fun _ => rfl⟩

theorem IsAEDeterminedBy.prodMk {Y : Ω → β} {Z : Ω → β'} (hY : IsAEDeterminedBy μ H Y)
    (hZ : IsAEDeterminedBy μ H Z) : IsAEDeterminedBy μ H fun ω => (Y ω, Z ω) := by
  obtain ⟨g, hg, hYg⟩ := hY
  obtain ⟨g', hg', hZg⟩ := hZ
  refine ⟨fun x => (g x, g' x), hg.prodMk hg', ?_⟩
  filter_upwards [hYg, hZg] with ω h1 h2
  rw [h1, h2]

/-- Countably many determined coordinates give a determined family. -/
theorem isAEDeterminedBy_pi {ι : Type*} [Countable ι] {δ : ι → Type*} [∀ i, MeasurableSpace (δ i)]
    {Y : Ω → ∀ i, δ i} (h : ∀ i, IsAEDeterminedBy μ H fun ω => Y ω i) : IsAEDeterminedBy μ H Y := by
  choose g hg hYg using h
  refine ⟨fun x i => g i x, measurable_pi_iff.2 hg, ?_⟩
  filter_upwards [ae_all_iff.2 hYg] with ω hω
  funext i
  exact hω i

/-- Almost-sure limits of determined variables with values in a Polish space are determined. -/
theorem IsAEDeterminedBy.of_tendsto [TopologicalSpace β] [PolishSpace β] [BorelSpace β]
    (hH : Measurable H) {Y : ℕ → Ω → β} {Z : Ω → β} (hY : ∀ n, IsAEDeterminedBy μ H (Y n))
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω))) : IsAEDeterminedBy μ H Z := by
  choose g hg hYg using hY
  have hC : MeasurableSet {x | ∃ c, Tendsto (fun n => g n x) atTop (𝓝 c)} :=
    StronglyMeasurable.measurableSet_exists_tendsto fun n => (hg n).stronglyMeasurable
  have hYg' := ae_all_iff.2 hYg
  have h1 : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => g n (H ω)) atTop (𝓝 c) := by
    filter_upwards [hlim, hYg'] with ω hl he
    refine ⟨Z ω, ?_⟩
    have : (fun n => Y n ω) = fun n => g n (H ω) := funext he
    rwa [this] at hl
  have h2 : ∀ᵐ x ∂(μ.map H), ∃ c, Tendsto (fun n => g n x) atTop (𝓝 c) :=
    (ae_map_iff hH.aemeasurable hC).2 h1
  obtain ⟨f, hf, hft⟩ := measurable_limit_of_tendsto_metrizable_ae
    (fun n => (hg n).aemeasurable) h2
  refine ⟨f, hf, ?_⟩
  filter_upwards [hlim, hYg', ae_of_ae_map hH.aemeasurable hft] with ω hl he hf'
  have : (fun n => Y n ω) = fun n => g n (H ω) := funext he
  rw [this] at hl
  exact tendsto_nhds_unique hl hf'

end Determined

/-! ### Stopped histories -/

section History

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}

/-- The stopped time `q ∧ τ(ω)`, as an element of `ℝ≥0` (equal to `q` when `τ(ω) = ⊤`). -/
def stopAt (τ : Ω → WithTop ℝ≥0) (q : ℝ≥0) (ω : Ω) : ℝ≥0 := min q ((τ ω).untopD q)

/-- The recorded stopped history `𝒳_τ = (τ, (X_{q ∧ τ})_{q ∈ ℚ≥0})` (Aux. lemma 52: "a history includes
its stopping time"). -/
def stoppedHistory (X : ℝ≥0 → Ω → E) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    WithTop ℝ≥0 × (ℚ≥0 → E) :=
  (τ ω, fun q => X (stopAt τ q ω) ω)

theorem stopAt_of_eq_coe {τ : Ω → WithTop ℝ≥0} {ω : Ω} {s : ℝ≥0} (h : τ ω = s) (q : ℝ≥0) :
    stopAt τ q ω = min q s := by
  simp only [stopAt, h, WithTop.untopD_coe]

theorem stopAt_le (τ : Ω → WithTop ℝ≥0) (q : ℝ≥0) (ω : Ω) :
    (stopAt τ q ω : WithTop ℝ≥0) ≤ τ ω := by
  unfold stopAt
  cases h : τ ω with
  | top => exact le_top
  | coe s => exact WithTop.coe_le_coe.2 (by simp only [WithTop.untopD_coe]; exact min_le_right _ _)

/-- The history at `τ` only depends on the value `τ ω`. -/
theorem stoppedHistory_congr {X : ℝ≥0 → Ω → E} {τ σ : Ω → WithTop ℝ≥0} {ω : Ω}
    (h : τ ω = σ ω) : stoppedHistory X τ ω = stoppedHistory X σ ω := by
  simp only [stoppedHistory, stopAt, h]

/-- From the two recorded times one knows which recorded history is the longer one. -/
theorem stoppedHistory_max (X : ℝ≥0 → Ω → E) (τ σ : Ω → WithTop ℝ≥0) (ω : Ω) :
    stoppedHistory X (fun ω => max (τ ω) (σ ω)) ω =
      if (stoppedHistory X σ ω).1 ≤ (stoppedHistory X τ ω).1 then stoppedHistory X τ ω
      else stoppedHistory X σ ω := by
  split_ifs with h
  · exact stoppedHistory_congr (X := X) (τ := fun ω => max (τ ω) (σ ω)) (σ := τ) (max_eq_left h)
  · exact stoppedHistory_congr (X := X) (τ := fun ω => max (τ ω) (σ ω)) (σ := σ)
      (max_eq_right (le_of_not_ge h))

/-- A finite time `x ≤ N` is the coercion of its `untopD`. -/
theorem eq_coe_untopD_of_le {x : WithTop ℝ≥0} {N : ℝ≥0} (h : x ≤ N) : x = ↑(x.untopD 0) := by
  cases x with
  | top => exact absurd h (WithTop.not_top_le_coe N)
  | coe s => rfl

/-- On finite times bounded by `N`, the order is read off from `untopD`. -/
theorem le_iff_untopD_le {x y : WithTop ℝ≥0} {N : ℝ≥0} (hx : x ≤ N) (hy : y ≤ N) :
    x ≤ y ↔ x.untopD 0 ≤ y.untopD 0 := by
  rw [eq_coe_untopD_of_le hx, eq_coe_untopD_of_le hy, WithTop.coe_le_coe, WithTop.untopD_coe,
    WithTop.untopD_coe]

/-- Nonnegative rationals are sequentially dense in `ℝ≥0`. -/
theorem exists_seq_nnrat_tendsto (t : ℝ≥0) :
    ∃ q : ℕ → ℚ≥0, Tendsto (fun n => ((q n : ℚ≥0) : ℝ≥0)) atTop (𝓝 t) := by
  have hex : ∀ n : ℕ, ∃ r : ℚ, (t : ℝ) < r ∧ (r : ℝ) < t + 1 / ((n : ℝ) + 1) := fun n =>
    exists_rat_btwn (by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                        linarith)
  choose r hr using hex
  have hr0 : ∀ n, 0 ≤ r n := fun n => by
    have h1 := (hr n).1
    have h2 : (0 : ℝ) ≤ t := t.2
    exact_mod_cast (by linarith : (0 : ℝ) ≤ r n)
  let q : ℕ → ℚ≥0 := fun n => ⟨r n, hr0 n⟩
  refine ⟨q, ?_⟩
  rw [← NNReal.tendsto_coe]
  have hcast : ∀ n, (((q n : ℚ≥0) : ℝ≥0) : ℝ) = (r n : ℝ) := fun n => by
    push_cast [q]
    rfl
  simp_rw [hcast]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => (hr n).1.le)
    (fun n => (hr n).2.le)
  simpa using (tendsto_const_nhds (x := (t : ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat

end History

/-! ### The class `𝒮` of the proof and its closure properties -/

section Restart

variable {Ω E γ : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [MeasurableSpace E] [MeasurableSpace γ]
  {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E} {H : Ω → γ}

/-- The class `𝒮` of the proof of Aux. lemma 52: `𝓕`-stopping times `τ ≤ b` whose stopped history is
almost surely determined by `H`. -/
def IsDeterminedStop (μ : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → E) (H : Ω → γ)
    (b τ : Ω → WithTop ℝ≥0) : Prop :=
  IsStoppingTime 𝓕 τ ∧ (∀ ω, τ ω ≤ b ω) ∧ IsAEDeterminedBy μ H (stoppedHistory X τ)

/-- `0 ∈ 𝒮` when the initial state is determined. -/
theorem isDeterminedStop_zero {b : Ω → WithTop ℝ≥0} (hX0 : IsAEDeterminedBy μ H (X 0)) :
    IsDeterminedStop μ 𝓕 X H b fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0) := by
  refine ⟨isStoppingTime_const 𝓕 0, fun ω => ?_, ?_⟩
  · cases b ω with
    | top => exact le_top
    | coe s => exact WithTop.coe_le_coe.2 zero_le
  · have hh : stoppedHistory X (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) =
        fun ω => (((0 : ℝ≥0) : WithTop ℝ≥0), fun _ : ℚ≥0 => X 0 ω) := by
      funext ω
      refine Prod.ext rfl (funext fun q => ?_)
      simp only [stoppedHistory, stopAt_of_eq_coe (τ := fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0))
        (ω := ω) rfl, min_eq_right zero_le]
    rw [hh]
    exact (isAEDeterminedBy_const _).prodMk (isAEDeterminedBy_pi fun _ => hX0)

/-- `𝒮` is closed under finite maxima. -/
theorem IsDeterminedStop.max {b τ σ : Ω → WithTop ℝ≥0} (hτ : IsDeterminedStop μ 𝓕 X H b τ)
    (hσ : IsDeterminedStop μ 𝓕 X H b σ) :
    IsDeterminedStop μ 𝓕 X H b fun ω => max (τ ω) (σ ω) := by
  refine ⟨hτ.1.max hσ.1, fun ω => max_le (hτ.2.1 ω) (hσ.2.1 ω), ?_⟩
  obtain ⟨g, hg, hτg⟩ := hτ.2.2
  obtain ⟨g', hg', hσg⟩ := hσ.2.2
  refine ⟨fun x => if (g' x).1 ≤ (g x).1 then g x else g' x,
    Measurable.ite (measurableSet_le (measurable_fst.comp hg') (measurable_fst.comp hg)) hg hg', ?_⟩
  filter_upwards [hτg, hσg] with ω h1 h2
  simp only [stoppedHistory_max, h1, h2]

/-- `𝒮` is closed under increasing limits (the paths being continuous on `[0, T]`). -/
theorem IsDeterminedStop.iSup [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
    (hH : Measurable H)
    {T b : Ω → WithTop ℝ≥0} {N : ℝ≥0} (hbT : ∀ ω, b ω ≤ T ω) (hbN : ∀ ω, b ω ≤ N)
    (hX : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ T ω})
    {ρ : ℕ → Ω → WithTop ℝ≥0} (hρ : ∀ n, IsDeterminedStop μ 𝓕 X H b (ρ n))
    (hmono : ∀ ω, Monotone fun n => ρ n ω) :
    IsDeterminedStop μ 𝓕 X H b fun ω => ⨆ n, ρ n ω := by
  set τ : Ω → WithTop ℝ≥0 := fun ω => ⨆ n, ρ n ω with hτdef
  have hτb : ∀ ω, τ ω ≤ b ω := fun ω => iSup_le fun n => (hρ n).2.1 ω
  refine ⟨fun i => ?_, hτb, ?_⟩
  · have hset : {ω | τ ω ≤ (i : WithTop ℝ≥0)} = ⋂ n, {ω | ρ n ω ≤ i} := by
      ext ω
      simp only [hτdef, mem_ofPred_eq, mem_iInter, iSup_le_iff]
    rw [hset]
    exact MeasurableSet.iInter fun n => (hρ n).1 i
  set s : ℕ → Ω → ℝ≥0 := fun n ω => (ρ n ω).untopD 0 with hsdef
  set s' : Ω → ℝ≥0 := fun ω => (τ ω).untopD 0 with hs'def
  have hρs : ∀ n ω, ρ n ω = s n ω := fun n ω =>
    eq_coe_untopD_of_le (((hρ n).2.1 ω).trans (hbN ω))
  have hτs : ∀ ω, τ ω = s' ω := fun ω => eq_coe_untopD_of_le ((hτb ω).trans (hbN ω))
  have hlim : ∀ ω, Tendsto (fun n => s n ω) atTop (𝓝 (s' ω)) := by
    intro ω
    have h1 : Tendsto (fun n => ρ n ω) atTop (𝓝 (τ ω)) := tendsto_atTop_iSup (hmono ω)
    rw [hτs ω] at h1
    have h2 : (fun n => ρ n ω) = fun n => ((s n ω : ℝ≥0) : WithTop ℝ≥0) := funext fun n => hρs n ω
    rw [h2] at h1
    exact WithTop.isEmbedding_coe.tendsto_nhds_iff.2 h1
  have hsdet : ∀ n, IsAEDeterminedBy μ H (s n) := fun n =>
    (hρ n).2.2.comp ((WithTop.measurable_untopD 0).comp measurable_fst)
  have hs'det : IsAEDeterminedBy μ H s' :=
    IsAEDeterminedBy.of_tendsto hH hsdet (ae_of_all _ hlim)
  have hXdet : ∀ q : ℚ≥0, IsAEDeterminedBy μ H fun ω => X (min (q : ℝ≥0) (s' ω)) ω := by
    intro q
    have hn : ∀ n, IsAEDeterminedBy μ H fun ω => X (min (q : ℝ≥0) (s n ω)) ω := by
      intro n
      refine ((hρ n).2.2.comp ((measurable_pi_apply q).comp measurable_snd)).congr_ae
        (ae_of_all _ fun ω => ?_)
      simp only [stoppedHistory, stopAt_of_eq_coe (hρs n ω), Function.comp_apply]
    refine IsAEDeterminedBy.of_tendsto hH hn ?_
    filter_upwards [hX] with ω hω
    have hmem : ∀ n, min (q : ℝ≥0) (s n ω) ∈ {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ T ω} := fun n =>
      calc ((min (q : ℝ≥0) (s n ω) : ℝ≥0) : WithTop ℝ≥0) ≤ ((s n ω : ℝ≥0) : WithTop ℝ≥0) :=
            WithTop.coe_le_coe.2 (min_le_right _ _)
        _ = ρ n ω := (hρs n ω).symm
        _ ≤ T ω := ((hρ n).2.1 ω).trans (hbT ω)
    have hmem' : min (q : ℝ≥0) (s' ω) ∈ {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ T ω} :=
      calc ((min (q : ℝ≥0) (s' ω) : ℝ≥0) : WithTop ℝ≥0) ≤ ((s' ω : ℝ≥0) : WithTop ℝ≥0) :=
            WithTop.coe_le_coe.2 (min_le_right _ _)
        _ = τ ω := (hτs ω).symm
        _ ≤ T ω := (hτb ω).trans (hbT ω)
    have ht : Tendsto (fun n => min (q : ℝ≥0) (s n ω)) atTop
        (𝓝[{t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ T ω}] (min (q : ℝ≥0) (s' ω))) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.min (hlim ω), Eventually.of_forall hmem⟩
    exact ((hω _ hmem').tendsto).comp ht
  have hhist : stoppedHistory X τ =
      fun ω => (((s' ω : ℝ≥0) : WithTop ℝ≥0), fun q : ℚ≥0 => X (min (q : ℝ≥0) (s' ω)) ω) := by
    funext ω
    refine Prod.ext (hτs ω) (funext fun q => ?_)
    show X (stopAt τ q ω) ω = X (min (q : ℝ≥0) (s' ω)) ω
    rw [stopAt_of_eq_coe (hτs ω)]
  rw [hhist]
  exact (hs'det.comp WithTop.measurable_coe).prodMk (isAEDeterminedBy_pi hXdet)

/-! ### Aux. lemma 52 -/

/-- **Aux. lemma 52** (Global determination from measurable local restarts; specification p. 244).
Let `X` be a process with values in a Polish space whose paths are almost surely continuous on
`[0, T]` (including a finite endpoint), let `H` be a random element, and assume that `X₀` is almost
surely determined by `H`. Assume the local extension property (LG1): whenever `τ` is a stopping time with
`τ ≤ T ∧ N` and determined history `𝒳_τ`, there is a stopping time `σ ≤ T ∧ N` with determined history,
`σ ≥ τ` and `σ > τ` on `{τ < T ∧ N}` (almost surely). Then for every finite `N` the history
`𝒳_{T ∧ N} = (T ∧ N, (X_{q ∧ T ∧ N})_{q ∈ ℚ≥0})` is almost surely determined by `H`.

(The filtration `𝓕` is arbitrary; the specification's usual natural filtration of `X` is a special
case. The lifetime `T` need not be a stopping time for this argument.) -/
theorem isAEDeterminedBy_stoppedHistory_of_localRestart [IsFiniteMeasure μ] [TopologicalSpace E]
    [PolishSpace E] [BorelSpace E] {T : Ω → WithTop ℝ≥0} (hH : Measurable H)
    (hX : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ T ω})
    (hX0 : IsAEDeterminedBy μ H (X 0))
    (hloc : ∀ (τ : Ω → WithTop ℝ≥0) (N : ℝ≥0), IsStoppingTime 𝓕 τ →
      (∀ ω, τ ω ≤ min (T ω) N) → IsAEDeterminedBy μ H (stoppedHistory X τ) →
      ∃ σ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓕 σ ∧ (∀ ω, σ ω ≤ min (T ω) N) ∧
        (∀ᵐ ω ∂μ, τ ω ≤ σ ω ∧ (τ ω < min (T ω) N → τ ω < σ ω)) ∧
        IsAEDeterminedBy μ H (stoppedHistory X σ))
    (N : ℝ≥0) : IsAEDeterminedBy μ H (stoppedHistory X fun ω => min (T ω) N) := by
  classical
  set b : Ω → WithTop ℝ≥0 := fun ω => min (T ω) N with hb
  have hbT : ∀ ω, b ω ≤ T ω := fun ω => min_le_left _ _
  have hbN : ∀ ω, b ω ≤ N := fun ω => min_le_right _ _
  -- the real expectation `E τ` of a member of `𝒮`
  let v : (Ω → WithTop ℝ≥0) → ℝ := fun τ => ∫ ω, (((τ ω).untopD 0 : ℝ≥0) : ℝ) ∂μ
  have hmeas : ∀ τ, IsDeterminedStop μ 𝓕 X H b τ →
      Measurable fun ω => (((τ ω).untopD 0 : ℝ≥0) : ℝ) := fun τ hτ =>
    measurable_coe_nnreal_real.comp ((WithTop.measurable_untopD 0).comp hτ.1.measurable')
  have hbound : ∀ τ, IsDeterminedStop μ 𝓕 X H b τ → ∀ ω, (((τ ω).untopD 0 : ℝ≥0) : ℝ) ≤ N := by
    intro τ hτ ω
    have h1 := (hτ.2.1 ω).trans (hbN ω)
    have h2 : (((τ ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0) ≤ N := (eq_coe_untopD_of_le h1) ▸ h1
    exact_mod_cast WithTop.coe_le_coe.1 h2
  have hint : ∀ τ, IsDeterminedStop μ 𝓕 X H b τ →
      Integrable (fun ω => (((τ ω).untopD 0 : ℝ≥0) : ℝ)) μ := fun τ hτ =>
    Integrable.of_bound (hmeas τ hτ).aestronglyMeasurable N (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
      exact hbound τ hτ ω)
  have hmono_v : ∀ τ σ, IsDeterminedStop μ 𝓕 X H b τ → IsDeterminedStop μ 𝓕 X H b σ →
      (∀ ω, τ ω ≤ σ ω) → v τ ≤ v σ := fun τ σ hτ hσ hle =>
    integral_mono (hint τ hτ) (hint σ hσ) fun ω => by
      have := (le_iff_untopD_le ((hτ.2.1 ω).trans (hbN ω)) ((hσ.2.1 ω).trans (hbN ω))).1 (hle ω)
      exact_mod_cast this
  -- `a = sup {E τ : τ ∈ 𝒮}` and a maximizing sequence
  set A : Set ℝ := v '' {τ | IsDeterminedStop μ 𝓕 X H b τ} with hA
  have h0 : IsDeterminedStop μ 𝓕 X H b fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0) :=
    isDeterminedStop_zero hX0
  have hAne : A.Nonempty := ⟨_, _, h0, rfl⟩
  have hAbdd : BddAbove A := by
    refine ⟨N * μ.real univ, ?_⟩
    rintro _ ⟨τ, hτ, rfl⟩
    calc v τ ≤ ∫ _, (N : ℝ) ∂μ := integral_mono (hint τ hτ) (integrable_const _) (hbound τ hτ)
      _ = N * μ.real univ := by rw [integral_const, smul_eq_mul, mul_comm]
  obtain ⟨u, -, hu, huA⟩ := exists_seq_tendsto_sSup hAne hAbdd
  choose τs hτs hvτ using huA
  -- successive maxima
  let ρ : ℕ → Ω → WithTop ℝ≥0 := fun n =>
    Nat.rec (τs 0) (fun k r => fun ω => max (r ω) (τs (k + 1) ω)) n
  have hρsucc : ∀ k, ρ (k + 1) = fun ω => max (ρ k ω) (τs (k + 1) ω) := fun k => rfl
  have hρP : ∀ n, IsDeterminedStop μ 𝓕 X H b (ρ n) := by
    intro n
    induction n with
    | zero => exact hτs 0
    | succ k ih => rw [hρsucc]; exact ih.max (hτs (k + 1))
  have hρmono : ∀ ω, Monotone fun n => ρ n ω := fun ω =>
    monotone_nat_of_le_succ fun k => by rw [hρsucc]; exact le_max_left _ _
  have hτsρ : ∀ n ω, τs n ω ≤ ρ n ω := by
    intro n ω
    cases n with
    | zero => exact le_rfl
    | succ k => rw [hρsucc]; exact le_max_right _ _
  -- the increasing limit `τ_*`
  set τstar : Ω → WithTop ℝ≥0 := fun ω => ⨆ n, ρ n ω with hτstar
  have hstar : IsDeterminedStop μ 𝓕 X H b τstar :=
    IsDeterminedStop.iSup hH hbT hbN hX hρP hρmono
  have hv_star : v τstar = sSup A := by
    refine le_antisymm (le_csSup hAbdd ⟨τstar, hstar, rfl⟩) ?_
    refine le_of_tendsto hu (Eventually.of_forall fun n => ?_)
    rw [← hvτ n]
    exact (hmono_v _ _ (hτs n) (hρP n) (hτsρ n)).trans
      (hmono_v _ _ (hρP n) hstar fun ω => le_iSup (fun n => ρ n ω) n)
  -- `τ_*` is an essential upper bound of `𝒮`
  have hess : ∀ τ, IsDeterminedStop μ 𝓕 X H b τ → ∀ᵐ ω ∂μ, τ ω ≤ τstar ω := by
    intro τ hτ
    have hm : IsDeterminedStop μ 𝓕 X H b fun ω => max (τ ω) (τstar ω) := hτ.max hstar
    have hle : v (fun ω => max (τ ω) (τstar ω)) ≤ v τstar :=
      hv_star ▸ le_csSup hAbdd ⟨_, hm, rfl⟩
    have hge := hmono_v _ _ hstar hm fun ω => le_max_right _ _
    have hpt : ∀ ω, (((τstar ω).untopD 0 : ℝ≥0) : ℝ) ≤
        (((max (τ ω) (τstar ω)).untopD 0 : ℝ≥0) : ℝ) := fun ω => by
      have := (le_iff_untopD_le ((hstar.2.1 ω).trans (hbN ω)) ((hm.2.1 ω).trans (hbN ω))).1
        (le_max_right (τ ω) (τstar ω))
      exact_mod_cast this
    have hzero : ∫ ω, ((((max (τ ω) (τstar ω)).untopD 0 : ℝ≥0) : ℝ) -
        (((τstar ω).untopD 0 : ℝ≥0) : ℝ)) ∂μ = 0 := by
      rw [integral_sub (hint _ hm) (hint _ hstar)]
      change v (fun ω => max (τ ω) (τstar ω)) - v τstar = 0
      linarith
    have hae := (integral_eq_zero_iff_of_nonneg (fun ω => sub_nonneg.2 (hpt ω))
      ((hint _ hm).sub (hint _ hstar))).1 hzero
    filter_upwards [hae] with ω hω
    have heq : (((max (τ ω) (τstar ω)).untopD 0 : ℝ≥0) : ℝ) = (((τstar ω).untopD 0 : ℝ≥0) : ℝ) :=
      sub_eq_zero.1 hω
    have heq' : max (τ ω) (τstar ω) = τstar ω :=
      calc max (τ ω) (τstar ω) = (((max (τ ω) (τstar ω)).untopD 0 : ℝ≥0) : WithTop ℝ≥0) :=
            eq_coe_untopD_of_le ((hm.2.1 ω).trans (hbN ω))
        _ = (((τstar ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0) := by
            rw [NNReal.coe_inj.1 heq]
        _ = τstar ω := (eq_coe_untopD_of_le ((hstar.2.1 ω).trans (hbN ω))).symm
    exact heq' ▸ le_max_left _ _
  -- (LG1) at `τ_*`
  obtain ⟨σ, hσst, hσb, hσae, hσdet⟩ := hloc τstar N hstar.1 hstar.2.1 hstar.2.2
  have hσP : IsDeterminedStop μ 𝓕 X H b σ := ⟨hσst, hσb, hσdet⟩
  have hσle := hess _ (hσP.max hstar)
  have hfin : ∀ᵐ ω ∂μ, τstar ω = b ω := by
    filter_upwards [hσae, hσle] with ω h1 h2
    by_contra hne
    have hlt : τstar ω < b ω := lt_of_le_of_ne (hstar.2.1 ω) hne
    exact absurd ((le_max_left (σ ω) (τstar ω)).trans h2) (not_le.2 (h1.2 hlt))
  exact hstar.2.2.congr_ae (hfin.mono fun ω h => stoppedHistory_congr h)

omit [MeasurableSpace E] in
/-- Continuity on `[0, B]` passes to the stopped times `q ∧ s` (`s ≤ B`). -/
theorem tendsto_comp_min_of_continuousOn {x : ℝ≥0 → E} [TopologicalSpace E] {B : WithTop ℝ≥0}
    (hx : ContinuousOn x {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ B}) {s : ℝ≥0}
    (hs : (s : WithTop ℝ≥0) ≤ B) {q : ℕ → ℝ≥0} {t : ℝ≥0} (hq : Tendsto q atTop (𝓝 t)) :
    Tendsto (fun n => x (min (q n) s)) atTop (𝓝 (x (min t s))) := by
  have hmem : ∀ u : ℝ≥0, min u s ∈ {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ B} := fun u =>
    (WithTop.coe_le_coe.2 (min_le_right u s)).trans hs
  exact ((hx _ (hmem t)).tendsto).comp
    (tendsto_nhdsWithin_iff.2 ⟨hq.min tendsto_const_nhds, Eventually.of_forall fun n => hmem _⟩)

/-- Aux. lemma 52, "in particular" (values): under the hypotheses of
`isAEDeterminedBy_stoppedHistory_of_localRestart`, every stopped value `X_{t ∧ T ∧ N}` (`t ∈ ℝ≥0`) is
almost surely determined by `H`; this includes `X_t` on `{t < T}` and the continuous finite terminal
value `X_T` on `{T ≤ N}`. -/
theorem isAEDeterminedBy_stopped_apply_of_localRestart [IsFiniteMeasure μ] [TopologicalSpace E]
    [PolishSpace E] [BorelSpace E] {T : Ω → WithTop ℝ≥0} (hH : Measurable H)
    (hX : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ T ω})
    (hX0 : IsAEDeterminedBy μ H (X 0))
    (hloc : ∀ (τ : Ω → WithTop ℝ≥0) (N : ℝ≥0), IsStoppingTime 𝓕 τ →
      (∀ ω, τ ω ≤ min (T ω) N) → IsAEDeterminedBy μ H (stoppedHistory X τ) →
      ∃ σ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓕 σ ∧ (∀ ω, σ ω ≤ min (T ω) N) ∧
        (∀ᵐ ω ∂μ, τ ω ≤ σ ω ∧ (τ ω < min (T ω) N → τ ω < σ ω)) ∧
        IsAEDeterminedBy μ H (stoppedHistory X σ))
    (N t : ℝ≥0) :
    IsAEDeterminedBy μ H fun ω => X (stopAt (fun ω => min (T ω) N) t ω) ω := by
  have hh := isAEDeterminedBy_stoppedHistory_of_localRestart hH hX hX0 hloc N
  obtain ⟨q, hq⟩ := exists_seq_nnrat_tendsto t
  refine IsAEDeterminedBy.of_tendsto hH
    (fun n => hh.comp ((measurable_pi_apply (q n)).comp measurable_snd)) ?_
  filter_upwards [hX] with ω hω
  have hb : min (T ω) (N : WithTop ℝ≥0) = ↑((min (T ω) (N : WithTop ℝ≥0)).untopD 0) :=
    eq_coe_untopD_of_le (min_le_right _ _)
  simp only [stoppedHistory, Function.comp_apply,
    stopAt_of_eq_coe (τ := fun ω => min (T ω) (N : WithTop ℝ≥0)) hb]
  exact tendsto_comp_min_of_continuousOn hω (hb ▸ min_le_left _ _) hq

/-- Aux. lemma 52, "in particular" (paths): under the hypotheses of
`isAEDeterminedBy_stoppedHistory_of_localRestart`, the whole stopped path `t ↦ X_{t ∧ T ∧ N}`, as an
element of `ℝ≥0 → E` with the product `σ`-algebra, is almost surely a Borel function of `H`. -/
theorem isAEDeterminedBy_stoppedPath_of_localRestart [IsFiniteMeasure μ] [TopologicalSpace E]
    [PolishSpace E] [BorelSpace E] {T : Ω → WithTop ℝ≥0} (hH : Measurable H)
    (hX : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ T ω})
    (hX0 : IsAEDeterminedBy μ H (X 0))
    (hloc : ∀ (τ : Ω → WithTop ℝ≥0) (N : ℝ≥0), IsStoppingTime 𝓕 τ →
      (∀ ω, τ ω ≤ min (T ω) N) → IsAEDeterminedBy μ H (stoppedHistory X τ) →
      ∃ σ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓕 σ ∧ (∀ ω, σ ω ≤ min (T ω) N) ∧
        (∀ᵐ ω ∂μ, τ ω ≤ σ ω ∧ (τ ω < min (T ω) N → τ ω < σ ω)) ∧
        IsAEDeterminedBy μ H (stoppedHistory X σ))
    (N : ℝ≥0) :
    IsAEDeterminedBy μ H fun ω (t : ℝ≥0) => X (stopAt (fun ω => min (T ω) N) t ω) ω := by
  obtain ⟨g, hg, hhg⟩ := isAEDeterminedBy_stoppedHistory_of_localRestart hH hX hX0 hloc N
  rcases isEmpty_or_nonempty γ with hγ | hγ
  · refine ⟨fun x => isEmptyElim x, Subsingleton.measurable, ?_⟩
    have : IsEmpty Ω := ⟨fun ω => isEmptyElim (H ω)⟩
    exact ae_of_all _ fun ω => isEmptyElim ω
  have hE : Nonempty E := by
    obtain ⟨g0, -, -⟩ := hX0
    exact ⟨g0 (Classical.arbitrary γ)⟩
  choose q hq using exists_seq_nnrat_tendsto
  let F : WithTop ℝ≥0 × (ℚ≥0 → E) → ℝ≥0 → E := fun h t => limUnder atTop fun n => h.2 (q t n)
  have hF : Measurable F := measurable_pi_iff.2 fun t =>
    (StronglyMeasurable.limUnder fun n =>
      ((measurable_pi_apply (q t n)).comp measurable_snd).stronglyMeasurable).measurable
  refine ⟨fun x => F (g x), hF.comp hg, ?_⟩
  filter_upwards [hhg, hX] with ω h1 hω
  funext t
  have hb : min (T ω) (N : WithTop ℝ≥0) = ↑((min (T ω) (N : WithTop ℝ≥0)).untopD 0) :=
    eq_coe_untopD_of_le (min_le_right _ _)
  rw [← h1]
  simp only [F, stoppedHistory, stopAt_of_eq_coe (τ := fun ω => min (T ω) (N : WithTop ℝ≥0)) hb]
  exact (tendsto_comp_min_of_continuousOn hω (hb ▸ min_le_left _ _) (hq t)).limUnder_eq.symm

end Restart

end Sec7

end InteractingSLE
