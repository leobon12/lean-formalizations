/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TransienceTrace
import InteractingSLE.WangWu.TraceTransience
import InteractingSLE.Spec.Sec4.Prob41Lemmas

/-!
# Aux. lemma 7 for `κ ≤ 4`, from transience for separated words

Packet PROVE-ZHAN-B2. Aux. lemma 7 (`Sec4.Aux7Statement`, Specification §2.2, p. 33) asserts, for an ordered force
word with admissible side partial sums (marks at `0⁻`, `0⁺` allowed): infinite lifetime, a continuous trace, and
transience. For `0 < κ ≤ 4` this file proves it from

* the transience of words whose marks are all strictly separated from the seed (`SeparatedTransienceStatement κ`,
  the remaining core: Astra §3, "Two-force transience" L1382–L1419 and "Chordal transience for an arbitrary finite
  word" L1585–L1615), and
* the restart with a random force word (`Sec7.RandomRestartTraceStatement κ`, PROVE-SEC7-C3's named input, proved by
  PROVE-RANDRESTART2).

The lifetime is Aux. lemma 6 (`Sec4.aux6Statement`), the trace is Remark 2.3 (`Zhan.IsIntegratedSLEEvolution.
ae_simple_trace`, `TransienceTrace.lean`), and transience with marks at the seed is Wang–Wu's Corollary 4.13 argument
(`WangWu.IsMarkedChain.ae_simple_transient_trace`) for every `κ ≤ 4`: at time `1` the word is separated (Aux. lemma
6), its side partial sums are still admissible because coincident marks stay coincident
(`hasAdmissiblePartialSums_of_ties`), so it is complete; the restart gives a transient trace of the shifted driver,
and the join (`Sec7.IsGeneratingTraceIcc.join`) transfers transience.

## Main results

* `SeparatedTransienceStatement κ`: the remaining core, as a named statement.
* `hasAdmissiblePartialSums_of_ties`: admissibility depends only on the order and the grouping of the marks.
* `isCompleteForceWord_of_separatedTransience`: separated admissible words are complete (`LP.IsCompleteForceWord`).
* `aux7Statement_of_separatedTransience`: `Sec4.Aux7Statement κ` for `0 < κ ≤ 4`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Zhan

variable {nL nR : ℕ}

/-- **Transience for words separated from the seed** (the core of Aux. lemma 7 and of Wang–Wu's input 8.3; Astra §3,
L1382–L1419 and L1585–L1615). For an ordered force word whose marks are all strictly separated from the seed and
whose side partial sums are admissible, almost surely every continuous generating trace on `[0, ∞)` tends to `∞`.
A named statement: it is not proved here (see `planning/handoffs/PROVE-ZHAN-B2.md`). -/
def SeparatedTransienceStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
    IsOrderedForceWord xL xR → Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR → (∀ i, xL i < 0) →
      (∀ j, 0 < xR j) → IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
          Tendsto (fun t => ‖η t‖) atTop atTop

/-! ### Admissibility depends only on the order and the grouping -/

/-- **Admissible partial sums under a coarser grouping.** If `y` is an ordered word whose marks coincide wherever those
of `x` do, admissibility of `x` gives admissibility of `y` (every side prefix of `y` is a side prefix of `x`). -/
theorem hasAdmissiblePartialSums_of_ties {k : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL yL : Fin nL → ℝ}
    {xR yR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) (hFy : IsOrderedForceWord yL yR)
    (hadm : Sec4.HasAdmissiblePartialSums k ρL ρR xL xR) (htL : ∀ i j, xL i = xL j → yL i = yL j)
    (htR : ∀ i j, xR i = xR j → yR i = yR j) : Sec4.HasAdmissiblePartialSums k ρL ρR yL yR := by
  obtain ⟨hxL, hxL0, hxR, hxR0⟩ := hF
  obtain ⟨hyL, -, hyR, -⟩ := hFy
  refine ⟨fun x hx ⟨i₀, hi₀⟩ => ?_, fun x hx ⟨j₀, hj₀⟩ => ?_⟩
  · -- left side: the set `{i | x < yL i}` is `{i | x' < xL i}` for some `x' < 0`
    by_cases hall : ∀ j, x < yL j
    · set m := Finset.univ.inf' ⟨i₀, Finset.mem_univ _⟩ xL with hm
      have hmle : ∀ i, m ≤ xL i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
      have hset : (univ.filter fun i => x < yL i) = univ.filter fun i => m - 1 < xL i := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun _ => by linarith [hmle i], fun _ => hall i⟩
      rw [hset]
      exact hadm.1 (m - 1) (by linarith [hmle i₀, hxL0 i₀]) ⟨i₀, by linarith [hmle i₀]⟩
    · push Not at hall
      have hne : (univ.filter fun j => yL j ≤ x).Nonempty := by
        obtain ⟨j, hj⟩ := hall; exact ⟨j, by simpa using hj⟩
      obtain ⟨j₁, hj₁, hmax⟩ := Finset.exists_max_image _ xL hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj₁ hmax
      have hset : (univ.filter fun i => x < yL i) = univ.filter fun i => xL j₁ < xL i := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hi
          by_contra hle
          push Not at hle
          have hij : i < j₁ := by
            by_contra hji
            push Not at hji
            linarith [hyL hji]
          have heq : xL i = xL j₁ := le_antisymm hle (hxL hij.le)
          have := htL i j₁ heq
          linarith
        · intro hi
          by_contra hle
          push Not at hle
          linarith [hmax i hle]
      rw [hset]
      have hlt : xL j₁ < xL i₀ := by
        have h := (Finset.ext_iff.1 hset i₀).1 (by simpa using hi₀)
        simpa using h
      exact hadm.1 (xL j₁) (by linarith [hxL0 i₀]) ⟨i₀, hlt⟩
  · -- right side: the set `{j | yR j ≤ x}` is `{j | xR j ≤ x'}` with `x'` its largest `xR`
    have hne : (univ.filter fun j => yR j ≤ x).Nonempty := ⟨j₀, by simpa using hj₀⟩
    obtain ⟨j₂, hj₂, hmax⟩ := Finset.exists_max_image _ xR hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj₂ hmax
    have hset : (univ.filter fun j => yR j ≤ x) = univ.filter fun j => xR j ≤ xR j₂ := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun hj => hmax j hj
      · intro hj
        by_contra hlt
        push Not at hlt
        have hji : j₂ < j := by
          by_contra hij
          push Not at hij
          linarith [hyR hij]
        have heq : xR j = xR j₂ := le_antisymm hj (hxR hji.le)
        have := htR j j₂ heq
        linarith
    rw [hset]
    exact hadm.2 (xR j₂) (hxR0 j₂) ⟨j₂, le_rfl⟩

/-! ### Complete words -/

/-- **Separated admissible words are complete** (given the core statement): every evolution of the word has a
continuous generating trace on `[0, ζ]`, `ζ = ∞`, which is transient. -/
theorem isCompleteForceWord_of_separatedTransience {κ : ℝ} (hκ : 0 < κ)
    (hS : SeparatedTransienceStatement.{u} κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hxL : ∀ i, xL i < 0) (hxR : ∀ j, 0 < xR j) : LP.IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  filter_upwards [hE.ae_exists_isGeneratingTrace_top_of_hasAdmissiblePartialSums hκ hF hadm hxL hxR,
    hS xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hxL hxR hE] with ω ⟨hζ, η, hη⟩ htr
  exact ⟨η, hζ ▸ hη, fun _ => htr η hη⟩

/-! ### The restart at time `1` -/

section Restart

variable {κ : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The **restart event at time `σ`** for a word `(xL, xR)`: the evolution is alive at time `σ`, and its force word
at time `σ` is ordered, strictly separated from the driver, and keeps the coincidences of `(xL, xR)` (written with
the killed coordinates, which are `𝓕_σ`-measurable). -/
def restartEventTies (σ : ℝ≥0) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Set Ω :=
  {ω | (σ : ℝ≥0∞) < ζ ω} ∩
    {ω | (∀ i, killedProc ζ (VL i) σ ω < killedProc ζ W σ ω) ∧
      (∀ j, killedProc ζ W σ ω < killedProc ζ (VR j) σ ω) ∧
      (∀ i j : Fin nL, i ≤ j → killedProc ζ (VL j) σ ω ≤ killedProc ζ (VL i) σ ω) ∧
      (∀ i j : Fin nR, i ≤ j → killedProc ζ (VR i) σ ω ≤ killedProc ζ (VR j) σ ω) ∧
      (∀ i j, xL i = xL j → killedProc ζ (VL i) σ ω = killedProc ζ (VL j) σ ω) ∧
      ∀ i j, xR i = xR j → killedProc ζ (VR i) σ ω = killedProc ζ (VR j) σ ω}

theorem measurableSet_restartEventTies (σ : ℝ≥0)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    MeasurableSet[𝓕 σ] (restartEventTies σ xL xR W VL VR ζ) := by
  obtain ⟨-, hW, hVL, hVR, -⟩ := hE
  have hζ : MeasurableSet[𝓕 σ] {ω | (σ : ℝ≥0∞) < ζ ω} := by
    simpa using hW σ univ MeasurableSet.univ
  have mW := measurable_killedProc hW σ
  have mL := fun i => measurable_killedProc (hVL i) σ
  have mR := fun j => measurable_killedProc (hVR j) σ
  refine hζ.inter ?_
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine (MeasurableSet.iInter fun i => measurableSet_lt (mL i) mW).inter
    ((MeasurableSet.iInter fun j => measurableSet_lt mW (mR j)).inter
      ((MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_).inter
        ((MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_).inter
          ((MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_).inter
            (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)))))
  · by_cases hij : i ≤ j
    · simpa [hij] using measurableSet_le (mL j) (mL i)
    · simp [hij]
  · by_cases hij : i ≤ j
    · simpa [hij] using measurableSet_le (mR i) (mR j)
    · simp [hij]
  · by_cases hij : xL i = xL j
    · simpa [hij] using measurableSet_eq_fun (mL i) (mL j)
    · simp [hij]
  · by_cases hij : xR i = xR j
    · simpa [hij] using measurableSet_eq_fun (mR i) (mR j)
    · simp [hij]

/-- On the restart event at `σ`, the word at `σ` seen from the driver is ordered, strictly separated from the seed,
and (if `(xL, xR)` is admissible) admissible. -/
theorem word_of_mem_restartEventTies {σ : ℝ≥0} (hF : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR) {ω : Ω}
    (hω : ω ∈ restartEventTies σ xL xR W VL VR ζ) :
    IsOrderedForceWord (fun i => VL i σ ω - W σ ω) (fun j => VR j σ ω - W σ ω) ∧
      Sec4.HasAdmissiblePartialSums κ ρL ρR (fun i => VL i σ ω - W σ ω) (fun j => VR j σ ω - W σ ω) ∧
      (∀ i, VL i σ ω - W σ ω < 0) ∧ ∀ j, 0 < VR j σ ω - W σ ω := by
  obtain ⟨h1, hsL, hsR, haL, haR, htL, htR⟩ := hω
  have hk : ∀ {X : ℝ≥0 → Ω → ℝ}, killedProc ζ X σ ω = X σ ω := fun {X} => by
    simp only [killedProc, show (σ : ℝ≥0∞) < ζ ω from h1, ↓reduceIte]
  simp only [hk] at hsL hsR haL haR htL htR
  have hFy : IsOrderedForceWord (fun i => VL i σ ω - W σ ω) (fun j => VR j σ ω - W σ ω) :=
    ⟨fun i j hij => by
        show VL j σ ω - W σ ω ≤ VL i σ ω - W σ ω
        linarith [haL i j hij],
      fun i => by
        show VL i σ ω - W σ ω ≤ 0
        linarith [hsL i],
      fun i j hij => by
        show VR i σ ω - W σ ω ≤ VR j σ ω - W σ ω
        linarith [haR i j hij],
      fun j => by
        show 0 ≤ VR j σ ω - W σ ω
        linarith [hsR j]⟩
  exact ⟨hFy, hasAdmissiblePartialSums_of_ties hF hFy hadm (fun i j h => by simp only [htL i j h])
      fun i j h => by simp only [htR i j h], fun i => by linarith [hsL i], fun j => by linarith [hsR j]⟩

/-- Almost surely (Aux. lemma 6), at every positive time the evolution of an admissible word is in the restart
event. -/
theorem IsIntegratedSLEEvolution.ae_mem_restartEventTies (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ σ : ℝ≥0, 0 < σ → ω ∈ restartEventTies σ xL xR W VL VR ζ := by
  filter_upwards [Sec4.aux6Statement hκ xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hE, hE.2.2.2.2] with ω
    ⟨hζ, hsep⟩ hp
  refine ⟨hζ, fun σ hσ => ?_⟩
  have h1 : (σ : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  have hk : ∀ {X : ℝ≥0 → Ω → ℝ}, killedProc ζ X σ ω = X σ ω := fun {X} => by
    simp only [killedProc, h1, ↓reduceIte]
  refine ⟨h1, ?_⟩
  simp only [Set.mem_ofPred_eq, hk]
  obtain ⟨hsL, hsR⟩ := hsep σ hσ
  exact ⟨hsL, hsR, fun i j hij => hp.isForcePath.antitone_vL h1 hij,
    fun i j hij => hp.isForcePath.monotone_vR h1 hij, fun i j h => hp.vL_eq_of_xL_eq h1 h,
    fun i j h => hp.vR_eq_of_xR_eq h1 h⟩

/-- **Transience with marks at the seed, from the separated case** (Wang–Wu's Corollary 4.13 argument, every
`κ ≤ 4`). For an ordered word with admissible side partial sums, almost surely `ζ = ∞`, there is a continuous
generating trace on `[0, ∞)`, and every such trace tends to `∞`. -/
theorem IsIntegratedSLEEvolution.ae_transient_of_separatedTransience (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hS : SeparatedTransienceStatement.{u} κ) (hR : Sec7.RandomRestartTraceStatement.{u} κ)
    (hF : IsOrderedForceWord xL xR) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η) ∧
      ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → Tendsto (fun t => ‖η t‖) atTop atTop := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hT := isStoppingTime_const 𝓕 (1 : ℝ≥0)
  have hAm : MeasurableSet[hT.measurableSpace] (restartEventTies 1 xL xR W VL VR ζ) := by
    rw [IsStoppingTime.measurableSpace_const]
    exact measurableSet_restartEventTies 1 hE
  have hrest := hR xL xR ρL ρR P 𝓕 W VL VR B ζ hE (fun _ => 1) hT (restartEventTies 1 xL xR W VL VR ζ) hAm
    (fun ω hω => hω.1) fun ω hω => by
      obtain ⟨hFy, hadm', hxL', hxR'⟩ := word_of_mem_restartEventTies hF hadm hω
      intro Ω' mΩ' P' _ 𝓕' W' VL' VR' B' ζ' hE'
      exact isCompleteForceWord_of_separatedTransience hκ hS hFy hadm' hxL' hxR' P' 𝓕' W' VL' VR' B' ζ' hE'
  filter_upwards [IsIntegratedSLEEvolution.ae_simple_trace hκ hκ4 hF hadm hE, hrest, hE.2.2.2.2,
    IsIntegratedSLEEvolution.ae_mem_restartEventTies hκ hF hadm hE] with ω
    ⟨hζ, _, η, hη, _⟩ hrω hp ⟨_, hmemσ⟩
  refine ⟨hζ, ⟨η, hη⟩, fun η' hη' => ?_⟩
  have hmem := hmemσ 1 one_pos
  obtain ⟨η₂, hη₂, htr₂⟩ := hrω hmem
  have hζ1 : ζ ω - ((1 : ℝ≥0) : ℝ≥0∞) = ⊤ := by rw [hζ]; exact ENNReal.top_sub_coe
  rw [hζ1] at hη₂
  have hwc : ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < ⊤} := by
    have := hp.2.2.2.1; rwa [hζ] at this
  have hw0 : (fun t => W t ω) 0 = 0 := hp.1
  have h₁ := Sec7.IsGeneratingTrace.isGeneratingTraceIcc hη' hwc hw0 (σ := 1) ENNReal.coe_lt_top
  have hwc' : ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < ((1 : ℝ≥0) : ℝ≥0∞) + ⊤} := by
    rwa [add_top]
  obtain ⟨hjoin, htj⟩ := h₁.join hwc' hw0 hη₂
  rw [add_top] at hjoin
  have heq : ∀ t : ℝ≥0, η' t = Sec7.joinTrace (fun t => W t ω) 1 η' η₂ t := fun t =>
    hη'.eq_of_le hjoin hwc hw0 le_top
  refine (htj rfl (htr₂ hζ1)).congr fun t => ?_
  rw [heq t]

/-- **Aux. lemma 7 for `0 < κ ≤ 4`**, from the core statement for separated words and the restart with a random
force word. -/
theorem aux7Statement_of_separatedTransience (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hS : SeparatedTransienceStatement.{u} κ) (hR : Sec7.RandomRestartTraceStatement.{u} κ) :
    Sec4.Aux7Statement.{u} κ := by
  intro nL nR xL xR ρL ρR Ω mΩ P 𝓕 W VL VR B ζ hF hadm hE
  exact IsIntegratedSLEEvolution.ae_transient_of_separatedTransience hκ hκ4 hS hR hF hadm hE

end Restart

end InteractingSLE.Zhan
