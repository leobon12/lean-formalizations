/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.PrefixLocalSides
import InteractingSLE.WangWu.TraceTransience
import InteractingSLE.Spec.Zhan.WordsEscape
import InteractingSLE.Spec.Sec7.ContinuityProb3Random
import InteractingSLE.Spec.Sec4.Thm12Special
import InteractingSLE.Spec.Sec7.DeterminationRestart
import InteractingSLE.WangWu.Bridge

/-!
# Wang–Wu Proposition 4.18: the seed line, its measurability, and determination from one reference

Packet PROVE-WW-B9. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), Proposition 4.18
(text dump L1599–1653): "Suppose the piecewise constant boundary data of `h` in `ℍ` are at most `−λ` on `ℝ₋` and at
least `λ` on `ℝ₊`. Its level line from `0` to `∞` is determined by `h`, has a simple continuous trace, and tends to `∞`."

At `κ = 4` the boundary data are `≤ −λ` on `ℝ₋` and `≥ λ` on `ℝ₊` exactly when the cumulative weights are nonnegative
(`HasNonnegCumWeights`, equivalently `Sec4.HasAdmissiblePartialSums 4`).

* **Measurability** (`measurable_arcPrefix`, `measurable_arcRange`): a random curve, continuous on `[0, ∞)` and
  measurable at each time, has hitting-measurable prefixes and range (they meet an open set iff a rational time does);
  `exists_continuous_version` modifies an almost surely continuous random curve on a null set.
* **The seed line** (`seedLine W ω s = LP.traceAt s (W · ω)`, the measurable trace evaluation): for a marked chain with
  nonnegative cumulative weights it is almost surely a simple proper Loewner trace (Corollary 4.13, now unconditional:
  Zhan's transience `Zhan.zhanNonboundaryTransience` and the random restart `RandRestart.randomRestartTraceStatement`
  are proved), and `seedLineVersion` is a version continuous for every `ω` (`ae_seedLineVersion`).
* **Range determination from history determination** (`aeDeterminedSigma_comap_arcRange_of_isFieldDeterminedHistory`):
  if the killed driving history is a Borel function of the field, so is the hitting σ-algebra of the line.
* **Side values of the seed line** (`IsFullLevelLineCoupling.ae_hasSideLimits_seedLine`): PROVE-WW-B8's single-line
  side values with every input discharged except the determination of the history (Proposition 4.18's conclusion).
* **Proposition 4.18, determination, reduced to one reference coupling** (`hasFieldDeterminedHistories_four_of_nonneg`,
  `hasDeterminedFullCouplings_of_nonneg`): any two couplings with the frozen optional hull specification of a
  nonnegative word at `κ = 4` have the same joint law of field and killed history (`Sec4.isOptionalHullLawUnique_of_
  admissible`), and a full level-line coupling of such a word is one (Corollary 3.9, `isOptionalHullCoupling`); so
  determination in one coupling gives it in all ("to compare two forward couplings, couple each conditionally
  independently with one reverse coupling given `h`; the same equality makes their measurable maps agree").
* **The `κ = 4` input of Theorem 1.2 from the two-seed input** (`wwTheorem17Statement_of_twoSeed`): Astra's §D.2
  (Aux. 52–55, ruling R38) applies at `κ = 4`, so `LP.WWTheorem17Statement` needs only `LP.TwoSeedGraphInput 4`
  (Wang–Wu Proposition 4.24) and the local extensions `Determination.LocalExtensionStatement 4`; Wang–Wu's force-point
  induction (Theorem 4.25, Lemma 4.10, Corollary 2.9) is not needed for it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace QuantumZipper Metric
open scoped NNReal ENNReal

universe u v

namespace InteractingSLE.WangWu

open LQGMetric (DistOn TestOn IsZeroBoundaryGFF AEDeterminedSigma)
open LocalSets

/-! ### Hitting-measurability of random curves -/

section Measurability

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

omit mΩ in
/-- A curve continuous on `[0, ∞)` that meets an open set `U` at a time `s < t` of `[0, t]` meets it at a rational time
of `[0, t)`. -/
theorem exists_rat_mem_of_continuousOn {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Ici 0)) {U : Set ℂ} (hU : IsOpen U)
    {s t : ℝ} (hs : s ∈ Icc 0 t) (hst : s < t) (hsU : γ s ∈ U) :
    ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) < t ∧ γ q ∈ U := by
  have hnhds : γ ⁻¹' U ∈ 𝓝[Ici 0] s :=
    (hγ s (mem_Ici.2 hs.1)).preimage_mem_nhdsWithin (hU.mem_nhds hsU)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hnhds
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s < min (s + ε) t from lt_min (by linarith) hst)
  have hq0 : (0 : ℝ) ≤ q := hs.1.trans hq1.le
  refine ⟨q, hq0, lt_of_lt_of_le hq2 (min_le_right _ _), hball ⟨?_, mem_Ici.2 hq0⟩⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  have := min_le_left (s + ε) t
  constructor <;> linarith

omit mΩ in
/-- The hitting events of a prefix of a curve continuous on `[0, ∞)`. -/
theorem arcPrefix_inter_nonempty_iff {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Ici 0)) {U : Set ℂ} (hU : IsOpen U)
    (t : ℝ) : (arcPrefix γ t ∩ U).Nonempty ↔
      (0 ≤ t ∧ γ t ∈ U) ∨ ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) < t ∧ γ q ∈ U := by
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, hsU⟩
    rcases hs.2.lt_or_eq with hst | rfl
    · exact Or.inr (exists_rat_mem_of_continuousOn hγ hU hs hst hsU)
    · exact Or.inl ⟨hs.1, hsU⟩
  · rintro (⟨ht, htU⟩ | ⟨q, hq0, hqt, hqU⟩)
    · exact ⟨_, ⟨t, ⟨ht, le_rfl⟩, rfl⟩, htU⟩
    · exact ⟨_, ⟨q, ⟨hq0, hqt.le⟩, rfl⟩, hqU⟩

/-- **The prefixes of a random curve are hitting-measurable**: continuous on `[0, ∞)` for every `ω` and measurable at
each time. -/
theorem measurable_arcPrefix {γ : Ω → ℝ → ℂ} (hc : ∀ ω, ContinuousOn (γ ω) (Ici 0))
    (hm : ∀ s, Measurable fun ω => γ ω s) (t : ℝ) :
    Measurable[mΩ, hittingSigma] fun ω => arcPrefix (γ ω) t := by
  unfold hittingSigma
  refine measurable_generateFrom ?_
  rintro _ ⟨U, hU, -, rfl⟩
  have e : (fun ω => arcPrefix (γ ω) t) ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =
      {ω | 0 ≤ t ∧ γ ω t ∈ U} ∪ ⋃ q : ℚ, {ω | 0 ≤ (q : ℝ) ∧ (q : ℝ) < t ∧ γ ω q ∈ U} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_union, mem_iUnion]
    exact arcPrefix_inter_nonempty_iff (hc ω) hU t
  rw [e]
  refine MeasurableSet.union ?_ (MeasurableSet.iUnion fun q => ?_)
  · by_cases ht : 0 ≤ t
    · simp only [ht, true_and]
      exact hm t hU.measurableSet
    · simp only [ht, false_and, ofPred_false, MeasurableSet.empty]
  · by_cases hq : 0 ≤ (q : ℝ) ∧ (q : ℝ) < t
    · simp only [hq, true_and]
      exact hm q hU.measurableSet
    · simp only [← and_assoc, hq, false_and, ofPred_false, MeasurableSet.empty]

omit mΩ in
/-- The range of a curve is the union of its integer prefixes. -/
theorem arcRange_eq_iUnion_arcPrefix (γ : ℝ → ℂ) : arcRange γ = ⋃ n : ℕ, arcPrefix γ n := by
  ext z
  simp only [arcRange, arcPrefix, mem_image, mem_iUnion, mem_Ici, mem_Icc]
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨n, hn⟩ := exists_nat_ge s
    exact ⟨n, s, ⟨hs, hn⟩, rfl⟩
  · rintro ⟨n, s, hs, rfl⟩
    exact ⟨s, hs.1, rfl⟩

/-- **The range of a random curve is hitting-measurable.** -/
theorem measurable_arcRange {γ : Ω → ℝ → ℂ} (hc : ∀ ω, ContinuousOn (γ ω) (Ici 0))
    (hm : ∀ s, Measurable fun ω => γ ω s) :
    Measurable[mΩ, hittingSigma] fun ω => arcRange (γ ω) := by
  simp only [arcRange_eq_iUnion_arcPrefix]
  exact measurable_iUnion_hitting fun n => measurable_arcPrefix hc hm n

omit mΩ in
/-- The hitting events of the range of a random curve continuous on `[0, ∞)` are the rational-time events. -/
theorem preimage_arcRange_hitting {γ : Ω → ℝ → ℂ} (hc : ∀ ω, ContinuousOn (γ ω) (Ici 0)) {U : Set ℂ}
    (hU : IsOpen U) :
    (fun ω => arcRange (γ ω)) ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =
      ⋃ q : ℚ, {ω | 0 ≤ (q : ℝ) ∧ γ ω q ∈ U} := by
  ext ω
  simp only [mem_preimage, mem_ofPred_eq, mem_iUnion]
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, hsU⟩
    obtain ⟨q, hq0, -, hqU⟩ := exists_rat_mem_of_continuousOn (hc ω) hU (t := s + 1)
      ⟨mem_Ici.1 hs, by linarith⟩ (by linarith) hsU
    exact ⟨q, hq0, hqU⟩
  · rintro ⟨q, hq0, hqU⟩
    exact ⟨_, ⟨q, mem_Ici.2 hq0, rfl⟩, hqU⟩

/-- **A continuous version.** A random curve that is measurable at each time and almost surely continuous on `[0, ∞)`
agrees almost surely with one that is measurable at each time and continuous on `[0, ∞)` for every `ω`. -/
theorem exists_continuous_version {P : Measure Ω} {γ : Ω → ℝ → ℂ} (hm : ∀ s, Measurable fun ω => γ ω s)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (γ ω) (Ici 0)) :
    ∃ γ' : Ω → ℝ → ℂ, (∀ s, Measurable fun ω => γ' ω s) ∧ (∀ ω, ContinuousOn (γ' ω) (Ici 0)) ∧
      ∀ᵐ ω ∂P, γ' ω = γ ω := by
  classical
  set N : Set Ω := toMeasurable P {ω | ¬ ContinuousOn (γ ω) (Ici 0)} with hNdef
  have hN : MeasurableSet N := measurableSet_toMeasurable _ _
  have hPN : P N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact ae_iff.1 hc
  refine ⟨fun ω => if ω ∈ N then fun _ => 0 else γ ω, fun s => ?_, fun ω => ?_, ?_⟩
  · have e : (fun ω => (if ω ∈ N then (fun _ : ℝ => (0 : ℂ)) else γ ω) s) =
        fun ω => if ω ∈ N then (0 : ℂ) else γ ω s := by
      funext ω; split_ifs <;> rfl
    rw [e]
    exact Measurable.ite hN measurable_const (hm s)
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
      exact continuousOn_const
    · simp only [hω, ↓reduceIte]
      by_contra h
      exact hω (subset_toMeasurable P _ h)
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hPN] with ω hω
    simp only [hω, ↓reduceIte]

end Measurability

/-! ### Almost sure determination of a σ-algebra generated by hitting events -/

section AEDet

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The events almost surely equal to an event of `G` form a σ-algebra. -/
@[instance_reducible]
def aeDetSigma (G : MeasurableSpace Ω) (P : Measure[mΩ] Ω) : MeasurableSpace Ω where
  MeasurableSet' s := ∃ t, MeasurableSet[G] t ∧ s =ᵐ[P] t
  measurableSet_empty := ⟨∅, MeasurableSet.empty, EventuallyEq.rfl⟩
  measurableSet_compl := fun _ ⟨t, ht, hst⟩ => ⟨tᶜ, ht.compl, EventuallyEqSet.compl hst⟩
  measurableSet_iUnion := fun f hf => by
    choose t ht hft using hf
    exact ⟨⋃ i, t i, MeasurableSet.iUnion ht, EventuallyEqSet.countable_iUnion hft⟩

/-- **The hitting σ-algebra of a random set is almost surely determined by `G`** as soon as every hitting event of an
open subset of `ℍ` is almost surely a `G`-event. -/
theorem aeDeterminedSigma_comap_hitting {P : Measure Ω} {A : Ω → Set ℂ} {G : MeasurableSpace Ω}
    (h : ∀ U : Set ℂ, IsOpen U → U ⊆ H →
      ∃ t, MeasurableSet[G] t ∧ A ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =ᵐ[P] t) :
    AEDeterminedSigma (MeasurableSpace.comap A hittingSigma) G P := by
  have hle : MeasurableSpace.comap A hittingSigma ≤ aeDetSigma G P := by
    rw [hittingSigma, MeasurableSpace.comap_generateFrom]
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨S, ⟨U, hU, hUH, rfl⟩, rfl⟩
    exact h U hU hUH
  exact fun s hs => hle s hs

end AEDet

/-! ### The seed line -/

section SeedLine

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The seed line**, read from the killed driver by the measurable trace evaluation `LP.traceAt`. -/
def seedLine (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (ω : Ω) (s : ℝ) : ℂ :=
  LP.traceAt s.toNNReal fun t => killedProc ζ W t ω

theorem measurable_seedLine (hW : AdaptedBefore 𝓕 ζ W) (s : ℝ) : Measurable fun ω => seedLine ζ W ω s :=
  (LP.measurable_traceAt _).comp
    (measurable_pi_iff.2 fun t => (measurable_killedProc hW t).mono (𝓕.le t) le_rfl)

omit mΩ in
/-- A continuous generating trace on `[0, ∞)` as a simple proper arc. -/
theorem isProperArc_of_injective {η : ℝ≥0 → ℂ} (hc : Continuous η) (h0 : η 0 = 0)
    (hinj : Function.Injective η) (hH : ∀ t, 0 < t → η t ∈ H)
    (htend : Tendsto (fun t => ‖η t‖) atTop atTop) : IsProperArc fun s : ℝ => η s.toNNReal where
  cont := (hc.comp continuous_real_toNNReal).continuousOn
  inj := fun s hs s' hs' e => by
    rw [← Real.coe_toNNReal s (mem_Ici.1 hs), ← Real.coe_toNNReal s' (mem_Ici.1 hs'), hinj e]
  zero := by simpa using h0
  mem_H := fun t ht => hH _ (Real.toNNReal_pos.2 ht)
  tendsto := htend.comp tendsto_real_toNNReal_atTop

/-- **Proposition 4.18, trace part** (Lemma 4.12 and Corollary 4.13, unconditional at `κ = 4`). For a marked chain of
an ordered word with nonnegative cumulative weights, almost surely the lifetime is infinite and the seed line is the
reparametrization `s ↦ η(s⁺)` of a continuous generating trace `η` on `[0, ∞)`, a simple proper Loewner trace of the
driver whose hulls are its initial pieces. -/
theorem IsMarkedChain.ae_seedLine (hxF : IsOrderedForceWord xL xR) (hcum : HasNonnegCumWeights ρL ρR)
    (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η ∧
      seedLine ζ W ω = fun s : ℝ => η s.toNNReal) ∧
      IsLoewnerTrace (Ito.rpath (W · ω)) (seedLine ζ W ω) ∧ IsProperArc (seedLine ζ W ω) ∧
      ∀ t : ℝ≥0, fwdHull (fun s : ℝ => W s.toNNReal ω) t = seedLine ζ W ω '' Ioc 0 t := by
  filter_upwards [hE.ae_simple_transient_trace (Sec7.RandRestart.randomRestartTraceStatement (by norm_num))
    Zhan.zhanNonboundaryTransience hxF hcum, hE.2.2.2.2] with ω hω hp
  obtain ⟨hζ, -, η, hη, hinj, hH, hhull, htend⟩ := hω
  have hwc : Continuous fun t => W t ω := by
    have h := hp.2.2.2.1
    rw [hζ] at h
    exact continuousOn_univ.1 (h.mono fun t _ => show (t : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top)
  have hk : (fun t => killedProc ζ W t ω) = fun t => W t ω := funext (killedProc_of_eq_top hζ)
  have hline : seedLine ζ W ω = fun s : ℝ => η s.toNNReal := by
    funext s
    simp only [seedLine, hk]
    exact LP.traceAt_eq_of_isGeneratingTrace hη hwc.continuousOn hp.1 ENNReal.coe_lt_top
  have hηc : Continuous η :=
    continuousOn_univ.1 (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  refine ⟨hζ, ⟨η, hη, hline⟩, ?_, ?_, fun t => ?_⟩
  · rw [hline]
    exact isLoewnerTrace_of_isGeneratingTrace hη
  · rw [hline]
    exact isProperArc_of_injective hηc hη.1 hinj hH htend
  · rw [hhull t, hline]
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, ⟨NNReal.coe_pos.2 hs.1, NNReal.coe_le_coe.2 hs.2⟩, by simp⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨s.toNNReal, ⟨Real.toNNReal_pos.2 hs.1, ?_⟩, rfl⟩
      exact (Real.toNNReal_le_iff_le_coe).2 hs.2

/-- **A version of the seed line continuous for every `ω`**: measurable at each time, continuous on `[0, ∞)`, almost
surely equal to the seed line and then a simple proper Loewner trace of the driver. -/
theorem IsMarkedChain.exists_seedLineVersion (hxF : IsOrderedForceWord xL xR) (hcum : HasNonnegCumWeights ρL ρR)
    (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∃ γ : Ω → ℝ → ℂ, (∀ s, Measurable fun ω => γ ω s) ∧ (∀ ω, ContinuousOn (γ ω) (Ici 0)) ∧
      ∀ᵐ ω ∂P, γ ω = seedLine ζ W ω ∧ ζ ω = ⊤ ∧ IsLoewnerTrace (Ito.rpath (W · ω)) (γ ω) ∧
        IsProperArc (γ ω) := by
  have hae := hE.ae_seedLine hxF hcum
  obtain ⟨γ, hγm, hγc, hγe⟩ := exists_continuous_version (P := P) (measurable_seedLine hE.2.1)
    (hae.mono fun ω h => h.2.2.2.1.cont)
  refine ⟨γ, hγm, hγc, ?_⟩
  filter_upwards [hae, hγe] with ω hω he
  obtain ⟨hζ, -, htr, harc, -⟩ := hω
  rw [he]
  exact ⟨rfl, hζ, htr, harc⟩

/-- **The range of the seed line is determined by the field once the killed history is** (Proposition 4.18: "Lemma 4.1
makes the oriented forward range a function of `h`" read backwards: a field-determined history determines the line).
Every hitting event of the range is the rational-time event `⋃_q {γ(q) ∈ U}`, and almost surely
`γ(q) = traceAt q (Ψ(F))` for the Borel history map `Ψ`. -/
theorem aeDeterminedSigma_comap_arcRange_of_isFieldDeterminedHistory {F : Ω → DistOn upperHalfPlaneOpens}
    (hdet : LP.IsFieldDeterminedHistory P F W VL VR ζ) {γ : Ω → ℝ → ℂ}
    (hc : ∀ ω, ContinuousOn (γ ω) (Ici 0)) (hγ : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ γ ω = seedLine ζ W ω) :
    AEDeterminedSigma (MeasurableSpace.comap (fun ω => arcRange (γ ω)) hittingSigma)
      (MeasurableSpace.comap F inferInstance) P := by
  obtain ⟨Ψ, hΨm, hΨ⟩ := hdet
  have hline : ∀ᵐ ω ∂P, ∀ s : ℝ, γ ω s = LP.traceAt s.toNNReal (Ψ (F ω)).2.1 := by
    filter_upwards [hγ, hΨ] with ω hω hΨω
    obtain ⟨hζ, he⟩ := hω
    obtain ⟨-, hW⟩ := hΨω
    intro s
    rw [he, seedLine]
    congr 1
    funext t
    rw [killedProc_of_eq_top hζ, (hW t (by rw [hζ]; exact ENNReal.coe_lt_top)).1]
  refine aeDeterminedSigma_comap_hitting fun U hU _ => ?_
  refine ⟨F ⁻¹' ⋃ q : ℚ, {f | 0 ≤ (q : ℝ) ∧ LP.traceAt (q : ℝ).toNNReal (Ψ f).2.1 ∈ U}, ?_, ?_⟩
  · refine ⟨_, MeasurableSet.iUnion fun q => ?_, rfl⟩
    by_cases hq : (0 : ℝ) ≤ q
    · simp only [hq, true_and]
      exact ((LP.measurable_traceAt _).comp (measurable_fst.comp (measurable_snd.comp hΨm))) hU.measurableSet
    · simp only [hq, false_and, ofPred_false, MeasurableSet.empty]
  · rw [preimage_arcRange_hitting hc hU]
    filter_upwards [hline] with ω hω
    simp only [preimage_iUnion, mem_iUnion, mem_ofPred_eq, mem_preimage, hω]

/-- The comap of a field is coarser than that of the centred field (they differ by a constant distribution). -/
theorem comap_le_comap_centredField (F : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) :
    MeasurableSpace.comap F inferInstance ≤
      MeasurableSpace.comap (WholeField.centredField F u₀) inferInstance := by
  have e : F = (fun x => x - (-SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀)) ∘
      WholeField.centredField F u₀ := by
    funext ω
    simp only [Function.comp_apply, WholeField.centredField, sub_neg_eq_add, sub_add_cancel]
  conv_lhs => rw [e]
  rw [← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (WholeField.measurable_sub_dist _).comap_le

/-- **Side values of the seed line of a full level-line coupling, range form** (PROVE-WW-B8's `ae_hasSideLimits_line` with
every input discharged except the determination of the line's range by the field, which is Proposition 4.18's
conclusion in the form used by Lemma 4.5 and Propositions 4.19–4.21). For a full level-line coupling of an ordered word
with nonnegative cumulative weights, a version `γ` of the seed line continuous for every `ω`
(`IsMarkedChain.exists_seedLineVersion`) whose range has a field-determined hitting σ-algebra, the local-set mean `g`
of the line for the centred field has the side values `−λ − u₀` on the left and `λ − u₀` on the right of `γ`. -/
theorem IsFullLevelLineCoupling.ae_hasSideLimits_seedLine_of_range [IsProbabilityMeasure P]
    {F : Ω → DistOn upperHalfPlaneOpens} (hF : IsFullLevelLineCoupling xL xR ρL ρR P 𝓕 W VL VR B ζ F)
    (hxF : IsOrderedForceWord xL xR) (hcum : HasNonnegCumWeights ρL ρR) {γ : Ω → ℝ → ℂ}
    (hγm : ∀ s, Measurable fun ω => γ ω s) (hγc : ∀ ω, ContinuousOn (γ ω) (Ici 0))
    (hγ : ∀ᵐ ω ∂P, γ ω = seedLine ζ W ω)
    (hdetR : AEDeterminedSigma (MeasurableSpace.comap (fun ω => arcRange (γ ω)) hittingSigma)
      (MeasurableSpace.comap F inferInstance) P) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => arcRange (γ ω)) (WholeField.centredField F u₀) P g) :
    (∀ᵐ ω ∂P, HasLeftSideLimit (g ω) (γ ω) fun z => -wwLambda - u₀ z) ∧
      ∀ᵐ ω ∂P, HasRightSideLimit (g ω) (γ ω) fun z => wwLambda - u₀ z := by
  have hae := IsMarkedChain.ae_seedLine hxF hcum hF.1
  have htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η := by
    filter_upwards [hae] with ω hω
    obtain ⟨hζ, ⟨η, hη, -⟩, -⟩ := hω
    exact ⟨η, hζ ▸ hη⟩
  have hγ' : ∀ᵐ ω ∂P, IsLoewnerTrace (Ito.rpath (W · ω)) (γ ω) ∧ IsProperArc (γ ω) := by
    filter_upwards [hae, hγ] with ω hω he
    rw [he]
    exact ⟨hω.2.2.1, hω.2.2.2.1⟩
  exact hF.ae_hasSideLimits_line htr (hcum.not_thresholdCondition_zero hxF) (hae.mono fun ω h => h.1) hγ'
    (measurable_arcRange hγc hγm) (fun n => measurable_arcPrefix hγc hγm _) hu₀
    (fun s hs => (hdetR s hs).imp fun t ht => ⟨comap_le_comap_centredField F u₀ t ht.1, ht.2⟩) hg

/-- **Side values of the seed line of a full level-line coupling** whose killed history is a Borel function of the
field (`ae_hasSideLimits_seedLine_of_range` with the range determined by the history,
`aeDeterminedSigma_comap_arcRange_of_isFieldDeterminedHistory`). -/
theorem IsFullLevelLineCoupling.ae_hasSideLimits_seedLine [IsProbabilityMeasure P]
    {F : Ω → DistOn upperHalfPlaneOpens} (hF : IsFullLevelLineCoupling xL xR ρL ρR P 𝓕 W VL VR B ζ F)
    (hxF : IsOrderedForceWord xL xR) (hcum : HasNonnegCumWeights ρL ρR)
    (hdet : LP.IsFieldDeterminedHistory P F W VL VR ζ) {γ : Ω → ℝ → ℂ}
    (hγm : ∀ s, Measurable fun ω => γ ω s) (hγc : ∀ ω, ContinuousOn (γ ω) (Ici 0))
    (hγ : ∀ᵐ ω ∂P, γ ω = seedLine ζ W ω) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => arcRange (γ ω)) (WholeField.centredField F u₀) P g) :
    (∀ᵐ ω ∂P, HasLeftSideLimit (g ω) (γ ω) fun z => -wwLambda - u₀ z) ∧
      ∀ᵐ ω ∂P, HasRightSideLimit (g ω) (γ ω) fun z => wwLambda - u₀ z := by
  have hae := IsMarkedChain.ae_seedLine hxF hcum hF.1
  exact hF.ae_hasSideLimits_seedLine_of_range hxF hcum hγm hγc hγ
    (aeDeterminedSigma_comap_arcRange_of_isFieldDeterminedHistory hdet hγc
      (by filter_upwards [hae, hγ] with ω hω he using ⟨hω.1, he⟩)) hu₀ hg

end SeedLine

/-! ### Proposition 4.18, determination: one reference coupling suffices -/

section Reference

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **Proposition 4.18, determination, from one reference coupling.** For an ordered word with nonnegative cumulative
weights at `κ = 4` (boundary data `≤ −λ` on `ℝ₋` and `≥ λ` on `ℝ₊`), if one coupling with the frozen optional hull
specification (on a space of any universe) has a field-determined killed history, then every such coupling does: all
of them have one joint law of field and killed history (`Sec4.isOptionalHullLawUnique_of_admissible`, Aux. lemma 23
for the entire history at `κ ≤ 4` with admissible partial sums). -/
theorem hasFieldDeterminedHistories_four_of_nonneg (hxF : IsOrderedForceWord xL xR)
    (hcum : HasNonnegCumWeights ρL ρR)
    (href : ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling 4 xL xR ρL ρR P 𝓕 W VL VR B ζ h ∧ LP.IsFieldDeterminedHistory P h W VL VR ζ) :
    LP.HasFieldDeterminedHistories.{u} 4 xL xR ρL ρR :=
  Sec4.hasFieldDeterminedHistories_of_admissible_of_reference (by norm_num) le_rfl hxF
    (hcum.hasAdmissiblePartialSums hxF) href

/-- **Every full level-line coupling of a nonnegative word is an optional hull coupling** (Corollary 3.9 with the
trace and the admissible seed of Lemma 4.12 / Corollary 4.13, both unconditional for these words). -/
theorem IsFullLevelLineCoupling.isOptionalHullCoupling_of_nonneg {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {F : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hF : IsFullLevelLineCoupling xL xR ρL ρR P 𝓕 W VL VR B ζ F)
    (hxF : IsOrderedForceWord xL xR) (hcum : HasNonnegCumWeights ρL ρR) :
    IsOptionalHullCoupling 4 xL xR ρL ρR P 𝓕 W VL VR B ζ F := by
  refine hF.isOptionalHullCoupling ?_ (hcum.not_thresholdCondition_zero hxF)
  filter_upwards [IsMarkedChain.ae_seedLine hxF hcum hF.1] with ω hω
  obtain ⟨hζ, ⟨η, hη, -⟩, -⟩ := hω
  exact ⟨η, hζ ▸ hη⟩

/-- **Proposition 4.18, determination, for every full level-line coupling** of a nonnegative word (Wang–Wu Theorem
4.25's `HasDeterminedFullCouplings` for these words), from one reference optional hull coupling with a field-determined
history. -/
theorem hasDeterminedFullCouplings_of_nonneg (hxF : IsOrderedForceWord xL xR) (hcum : HasNonnegCumWeights ρL ρR)
    (href : ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling 4 xL xR ρL ρR P 𝓕 W VL VR B ζ h ∧ LP.IsFieldDeterminedHistory P h W VL VR ζ) :
    HasDeterminedFullCouplings.{u} xL xR ρL ρR := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ F hF
  exact hasFieldDeterminedHistories_four_of_nonneg.{u, v} hxF hcum href P 𝓕 W VL VR B ζ F
    (hF.isOptionalHullCoupling_of_nonneg hxF hcum)

/-- The reference may be a full level-line coupling (Corollary 3.9). -/
theorem hasFieldDeterminedHistories_four_of_nonneg_of_full (hxF : IsOrderedForceWord xL xR)
    (hcum : HasNonnegCumWeights ρL ρR)
    (href : ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (F : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsFullLevelLineCoupling xL xR ρL ρR P 𝓕 W VL VR B ζ F ∧ LP.IsFieldDeterminedHistory P F W VL VR ζ) :
    LP.HasFieldDeterminedHistories.{u} 4 xL xR ρL ρR := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, F, hF, hdet⟩ := href
  exact hasFieldDeterminedHistories_four_of_nonneg.{u, v} hxF hcum
    ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, F, hF.isOptionalHullCoupling_of_nonneg hxF hcum, hdet⟩

end Reference

/-! ### The `κ = 4` determination input from the two-seed input (Astra §D.2) -/

section TwoSeed

/-- **The `κ = 4` input of the frozen Theorem 1.2 from the two-seed input** (Astra's follow-up note §D.2, Aux. 52–55,
ruling R38, at `κ = 4`): `LP.WWTheorem17Statement` (determination for every ordered word at `κ = 4`) follows from
`LP.TwoSeedGraphInput 4` (Wang–Wu Proposition 4.24: determination and the continuous trace for the two-seed words
`SLE₄(r_L; r_R)`, `r_L, r_R > −2`) and the local extensions `Determination.LocalExtensionStatement 4` (Aux. 53 + 55).
Wang–Wu's force-point induction (Theorem 4.25, with Lemma 4.10 and Corollary 2.9) is not used. -/
theorem wwTheorem17Statement_of_twoSeed (h2 : LP.TwoSeedGraphInput.{u} 4)
    (hext : Determination.LocalExtensionStatement.{u} 4) : LP.WWTheorem17Statement.{u} :=
  fun _ _ _ _ hxF => Determination.hasFieldDeterminedHistories_of_localExtension (by norm_num) h2 hext hxF

/-- The two-seed word with nonnegative weights has nonnegative cumulative weights. -/
theorem hasNonnegCumWeights_twoSeed {rL rR : ℝ} (hL : 0 ≤ rL) (hR : 0 ≤ rR) :
    HasNonnegCumWeights (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) := by
  refine ⟨fun j => ?_, fun j => ?_⟩ <;>
  · fin_cases j
    simpa using by assumption

theorem isOrderedForceWord_twoSeed : IsOrderedForceWord LP.twoSeedXL LP.twoSeedXR :=
  ⟨fun _ _ _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl, fun _ => le_rfl⟩

/-- **The two-seed input for nonnegative weights** (the case `r_L, r_R ≥ 0` of Wang–Wu Proposition 4.24, which is
Proposition 4.18): the continuous trace (Corollary 4.13) is unconditional, and determination follows from one
reference coupling of each such word. -/
theorem twoSeed_of_nonneg {rL rR : ℝ} (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (href : ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ)
      (VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h ∧
        LP.IsFieldDeterminedHistory P h W VL VR ζ) :
    LP.HasFieldDeterminedHistories.{u} 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) ∧
      ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
        (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
        IsIntegratedSLEEvolution 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ →
          ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η := by
  refine ⟨hasFieldDeterminedHistories_four_of_nonneg.{u, v} isOrderedForceWord_twoSeed
    (hasNonnegCumWeights_twoSeed hL hR) href, fun P _ 𝓕 W VL VR B ζ hE => ?_⟩
  filter_upwards [IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR) hE]
    with ω hω
  obtain ⟨hζ, ⟨η, hη, -⟩, -⟩ := hω
  exact ⟨η, hζ ▸ hη⟩

end TwoSeed

end InteractingSLE.WangWu
