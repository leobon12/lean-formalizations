import InteractingSLE.Spec.Sec2.T24BrDescent

/-!
# The candidate v2 convention and almost sure lifetime changes

This scoped predicate has exactly the v2 strict-localizer and zero-indicator body.
The modification lemma also allows changing the lifetime on a null set. It is an
implementation adapter pending the statement audit, not a replacement frozen anchor.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec2.T24Bridge

/-- The strict-localizer convention in the Theorem 2.4 candidate v2. -/
def IsContLocalMartingaleBeforeV2 {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (ζ : Ω → WithTop ℝ≥0) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ᵐ ω ∂P, ContinuousOn (X · ω) {t | (t : WithTop ℝ≥0) < ζ ω}) ∧
    ∃ σ : ℕ → Ω → WithTop ℝ≥0, (∀ n, IsStoppingTime 𝓕 (σ n)) ∧
      (∀ n ω, σ n ω = 0 ∨ σ n ω < ζ ω) ∧
      (∀ᵐ ω ∂P, ∀ r : ℝ≥0, (r : WithTop ℝ≥0) < ζ ω →
        ∀ᶠ n in atTop, (r : WithTop ℝ≥0) < σ n ω) ∧
      ∀ n, Martingale (stoppedProcess (fun t => {ω | 0 < σ n ω}.indicator (X t)) (σ n)) 𝓕 P

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- Convert the `WithTop` order used by the stochastic-interval predicate to the
inherited `ENNReal` order used by Loewner lifetimes. -/
theorem ennreal_lt_of_withTop_lt {a b : ℝ≥0∞}
    (h : (a : WithTop ℝ≥0) < (b : WithTop ℝ≥0)) : a < b := by
  cases h with
  | lt_top a => exact ENNReal.coe_lt_top
  | coe_lt_coe h => exact ENNReal.coe_lt_coe.2 h

/-- The initial-event martingale adapter used in the statement certification. -/
theorem martingale_indicator_initial {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓕 P)
    {A : Set Ω} (hA : MeasurableSet[𝓕 0] A) : Martingale (fun t => A.indicator (M t)) 𝓕 P := by
  refine ⟨fun t => (hM.1 t).indicator (𝓕.mono zero_le _ hA), fun s t hst => ?_⟩
  exact (condExp_indicator (hM.integrable t) (𝓕.mono zero_le _ hA)).trans
    ((hM.2 s t hst).mono fun ω hω => by simp only [Set.indicator]; split_ifs <;> simp [hω])

/-- A strict localized process reads the observable only on its live interval. -/
theorem stoppedIndicator_congr_before {ζ σ : Ω → WithTop ℝ≥0} {X Y : ℝ≥0 → Ω → ℝ}
    {ω : Ω} (hσ : σ ω = 0 ∨ σ ω < ζ ω)
    (hXY : ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < ζ ω → X t ω = Y t ω) (t : ℝ≥0) :
    stoppedProcess (fun t => {ω | 0 < σ ω}.indicator (X t)) σ t ω =
      stoppedProcess (fun t => {ω | 0 < σ ω}.indicator (Y t)) σ t ω := by
  simp only [stoppedProcess, Set.indicator, mem_ofPred_eq]
  split_ifs with hpos
  · rcases hσ with h0 | hlt
    · rw [h0] at hpos
      exact absurd hpos (lt_irrefl _)
    · apply hXY
      rw [MartChar.coe_untopA_of_ne_top
        (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _))]
      exact (min_le_right _ _).trans_lt hlt
  · rfl

/-- Simultaneous null changes of the lifetime and of all live values preserve the v2 predicate. -/
theorem isContLocalMartingaleBeforeV2_of_ae_eq
    {ζ ζ' : Ω → WithTop ℝ≥0} {X Y : ℝ≥0 → Ω → ℝ}
    (he : ∀ᵐ ω ∂P, ζ' ω = ζ ω ∧
      ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < ζ ω → X t ω = Y t ω)
    (h : IsContLocalMartingaleBeforeV2 (usualAugmentation 𝓕 P) P ζ X) :
    IsContLocalMartingaleBeforeV2 (usualAugmentation 𝓕 P) P ζ' Y := by
  obtain ⟨hc, σ, hst, hσ, hex, hm⟩ := h
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 he)
  have hN : MeasurableSet[usualAugmentation 𝓕 P 0] N :=
    Ito.measurableSet_usualAugmentation_of_null hNm hN0 0
  have hgood : ∀ ω, ω ∉ N → ζ' ω = ζ ω ∧
      ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < ζ ω → X t ω = Y t ω := by
    intro ω hω
    by_contra hbad
    exact hω (hNsub hbad)
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  let σ' : ℕ → Ω → WithTop ℝ≥0 := fun n ω => if ω ∈ N then 0 else σ n ω
  refine ⟨?_, σ', fun n t => ?_, fun n ω => ?_, ?_, fun n => ?_⟩
  · filter_upwards [hc, hNae] with ω hω hωN
    rw [(hgood ω hωN).1]
    exact hω.congr fun t ht => ((hgood ω hωN).2 t ht).symm
  · have heq : {ω | σ' n ω ≤ t} = N ∪ ({ω | σ n ω ≤ t} ∩ Nᶜ) := by
      ext ω
      by_cases hω : ω ∈ N
      · simp only [σ', hω, ↓reduceIte, mem_ofPred_eq, mem_union, true_or, iff_true]
        exact zero_le
      · simp [σ', hω]
    rw [heq]
    exact ((usualAugmentation 𝓕 P).mono zero_le _ hN).union
      ((hst n t).inter ((usualAugmentation 𝓕 P).mono zero_le _ hN.compl))
  · by_cases hω : ω ∈ N
    · exact Or.inl (by simp [σ', hω])
    · simp only [σ', hω, ↓reduceIte]
      rw [(hgood ω hω).1]
      exact hσ n ω
  · filter_upwards [hex, hNae] with ω hω hωN r hr
    have hr' : (r : WithTop ℝ≥0) < ζ ω := (hgood ω hωN).1 ▸ hr
    simpa only [σ', hωN, ↓reduceIte] using hω r hr'
  · have heq : stoppedProcess (fun t => {ω | 0 < σ' n ω}.indicator (Y t)) (σ' n) =
        fun t => Nᶜ.indicator
          (stoppedProcess (fun t => {ω | 0 < σ n ω}.indicator (X t)) (σ n) t) := by
      funext t ω
      by_cases hω : ω ∈ N
      · simp [stoppedProcess, Set.indicator, σ', hω]
      · have hh := stoppedIndicator_congr_before (hσ n ω) (hgood ω hω).2 t
        by_cases hpos : 0 < σ n ω
        · simpa [stoppedProcess, Set.indicator, σ', hω, hpos] using hh.symm
        · simp [stoppedProcess, Set.indicator, σ', hω, hpos]
    rw [heq]
    exact martingale_indicator_initial (hm n) hN.compl

end InteractingSLE.Sec2.T24Bridge
