/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FqStep
import InteractingSLE.Spec.Supplement.SB2KcPartition

/-!
# Gluing the induction's stage laws over events of the retained past

Worker PROVE-SB2-F3LAW (round 6, D80: the gluing over the random `relOff`). At B's stage `ℓ + 2` the induction's law
is produced on several pieces of the launch event — `relOff ≥ ℓ + 2` (the base law), the root at `ℓ` (positive or
zero), the tails (`Fo.tail_step`) and the zero-lifetime stages (`Fs.zero_step`) — each with its own word. The pieces
are events of the completed retained past (`relOff` and the lifetimes before `ℓ + 2` are read from B's runs up to
`ℓ + 1`), so the words can be glued by those events and stay measurable for `aeSigma (stageMarks (ℓ + 2))`.

* `mvLaw_piecewiseOn`: two retained laws glued by any event `C` of the marks (the selector need not be either law's
  event; `Fl.mvLaw_piecewise` is the case `C = G₁`);
* **`StageLawOn`**: the induction's stage data on an event `C` of B's stage `ℓ` for a line family `(𝓖, A₁)`: the
  retained law covering the launches in `C`, the word measurable for the completed retained past, a countable set of
  word profiles (`Lv.wordProfile`: mark count and height array) containing the word's profile on the launches in `C`,
  and the left heights `hL` at every tail launch inside `C` (zero lifetimes included: the next zero-lifetime step
  reads them). With `types_of_profiles` these give the clauses of
  CANON's `Cz.SB2LowerStageLawInStatement` other than its two premises, which follow from the law and `hL`
  (`Fq.hmean_of_law`, `Fq.hheight_of_law`). Profiles (not types) are carried because a step's type set is computed
  from the incoming profiles (`Lv.wordProfile_shift_stop_mem`);
* `types_of_profiles`: countable profiles give the countable word types of every shift;
* **`stageLawOn_glue`**: two pieces glued by `C₁` (an event of the marks and of the completed retained past);
* `stageLawOn_glue'`: the same with a selector separate from the pieces' events;
* `stageLawOn_mono`: restriction to a smaller event.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Fs

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Supp8.Q3Stop Lv Lk Mf Ms

/-- **Two retained laws glued by an event of the marks.** -/
theorem mvLaw_piecewiseOn {κ : ℝ} {Ω : Type*} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (h𝓜 : 𝓜 ≤ mΩ) {A K₁ K₂ : Ω → Set ℂ} {G₁ G₂ C : Set Ω} {Y₁ Y₂ : Ω → DistOn upperHalfPlaneOpens}
    {β₁ β₂ : Ω → BoundaryWord} {M₁ M₂ : ℝ} [DecidablePred (· ∈ C)] (hC : MeasurableSet[𝓜] C)
    (h₁ : Fl.MvLaw κ 𝓜 P h A K₁ G₁ Y₁ β₁ M₁) (h₂ : Fl.MvLaw κ 𝓜 P h A K₂ G₂ Y₂ β₂ M₂) :
    Fl.MvLaw κ 𝓜 P h A (fun ω => C.piecewise K₁ K₂ ω) ((G₁ ∩ C) ∪ (G₂ \ C)) (C.piecewise Y₁ Y₂)
      (C.piecewise β₁ β₂) (max M₁ M₂) := by
  obtain ⟨hK₁m, hK₁c, hK₁p, hG₁, hK₁A, hY₁m, hY₁t, hβ₁m, hβ₁s, hM₁, hβ₁b, hl₁⟩ := h₁
  obtain ⟨hK₂m, hK₂c, hK₂p, hG₂, hK₂A, hY₂m, hY₂t, hβ₂m, hβ₂s, hM₂, hβ₂b, hl₂⟩ := h₂
  have hCΩ : MeasurableSet C := h𝓜 _ hC
  refine ⟨fun n j => ?_, fun ω => ?_, fun ω => ?_, (hG₁.inter hC).union (hG₂.diff hC), ?_,
    hY₁m.piecewise hCΩ hY₂m, ?_, hβ₁m.piecewise hC hβ₂m, fun ω => ?_, le_max_of_le_left hM₁, fun ω y hy => ?_, ?_⟩
  · have e : {ω | (Restart.dyadicSquare n j ∩ C.piecewise K₁ K₂ ω).Nonempty} =
        (C ∩ {ω | (Restart.dyadicSquare n j ∩ K₁ ω).Nonempty}) ∪
          (Cᶜ ∩ {ω | (Restart.dyadicSquare n j ∩ K₂ ω).Nonempty}) := by
      ext ω
      by_cases hω : ω ∈ C
      · simp [hω]
      · simp [hω]
    rw [e]
    exact (hC.inter (hK₁m n j)).union (hC.compl.inter (hK₂m n j))
  · by_cases hω : ω ∈ C <;> simp only [Set.piecewise, hω, ↓reduceIte] <;> first | exact hK₁c ω | exact hK₂c ω
  · by_cases hω : ω ∈ C <;> simp only [Set.piecewise, hω, ↓reduceIte] <;> first | exact hK₁p ω | exact hK₂p ω
  · filter_upwards [hK₁A, hK₂A] with ω e1 e2 hω
    rcases hω with hω | hω
    · simp only [Set.piecewise, hω.2, ↓reduceIte]; exact e1 hω.1
    · simp only [Set.piecewise, hω.2, ↓reduceIte]; exact e2 hω.1
  · filter_upwards [hY₁t, hY₂t] with ω e1 e2 hω
    rcases hω with hω | hω
    · simp only [Set.piecewise, hω.2, ↓reduceIte]; exact e1 hω.1
    · simp only [Set.piecewise, hω.2, ↓reduceIte]; exact e2 hω.1
  · by_cases hω : ω ∈ C <;> simp only [Set.piecewise, hω, ↓reduceIte] <;> first | exact hβ₁s ω | exact hβ₂s ω
  · by_cases hω : ω ∈ C
    · simp only [Set.piecewise, hω, ↓reduceIte] at hy ⊢; exact (hβ₁b ω y hy).trans (le_max_left _ _)
    · simp only [Set.piecewise, hω, ↓reduceIte] at hy ⊢; exact (hβ₂b ω y hy).trans (le_max_right _ _)
  · have hYm : Measurable (C.piecewise Y₁ Y₂) := hY₁m.piecewise hCΩ hY₂m
    have hl₁' : ∀ᵐ ω₀ ∂P, ω₀ ∈ G₁ ∩ C →
        IsGFFWithBoundaryData (condExpKernel P 𝓜 ω₀) Y₁ (β₁ ω₀).fn (β₁ ω₀).jumps := by
      filter_upwards [hl₁] with ω₀ h1 hω₀ using h1 hω₀.1
    have e1 := Fl.ae_isGFF_congr_on (P := P) h𝓜 (hG₁.inter hC) hYm hl₁' (Eventually.of_forall fun ω hω => by
      simp only [Set.piecewise, hω.2, ↓reduceIte])
    have hl₂' : ∀ᵐ ω₀ ∂P, ω₀ ∈ G₂ \ C →
        IsGFFWithBoundaryData (condExpKernel P 𝓜 ω₀) Y₂ (β₂ ω₀).fn (β₂ ω₀).jumps := by
      filter_upwards [hl₂] with ω₀ h1 hω₀ using h1 hω₀.1
    have e2 := Fl.ae_isGFF_congr_on (P := P) h𝓜 (hG₂.diff hC) hYm hl₂' (Eventually.of_forall fun ω hω => by
      simp only [Set.piecewise, hω.2, ↓reduceIte])
    filter_upwards [e1, e2] with ω₀ f1 f2 hω₀
    rcases hω₀ with hω₀ | hω₀
    · simp only [Set.piecewise, hω₀.2, ↓reduceIte]; exact f1 hω₀
    · simp only [Set.piecewise, hω₀.2, ↓reduceIte]; exact f2 hω₀

section Stage

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
  (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ)

/-- **The induction's stage data on an event `C`** of B's stage `ℓ`, for the line family `(𝓖, A₁)`, with word `β` and
word profiles `S`. See the module docstring. -/
def StageLawOn (𝓖 : Filtration ℝ≥0 mΩ) (A₁ : ℝ≥0 → Ω → Set ℂ) (C : Set Ω) (β : Ω → BoundaryWord)
    (S : Set Lv.WordProfile) : Prop :=
  (∃ (K : Ω → Set ℂ) (G : Set Ω) (Y : Ω → DistOn upperHalfPlaneOpens) (M : ℝ),
    Fl.MvLaw κ (lineFiltC P 𝓖 0) P h (A₁ 0) K G Y β M ∧
    ∀ᵐ ω ∂P, ω ∈ C → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none → ω ∈ G) ∧
  Measurable[aeSigma (stageMarks κ b jumps E u l k ℓ) P] β ∧ S.Countable ∧
  (∀ᵐ ω ∂P, ω ∈ C → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
    Lv.wordProfile (β ω) ∈ S) ∧
  ∀ᵐ ω ∂P, ω ∈ C → ω ∈ stageEvent κ b jumps E u l k ℓ →
    relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ →
    Fm.LeftAdm κ (β ω) (Fm.entry (A₁ 0 ω) (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps
      (-(Real.pi / 2)) true) (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)))

variable {κ b jumps P h E u l k ℓ}

/-- **Restriction of the stage data to a smaller event.** -/
theorem stageLawOn_mono {𝓖 : Filtration ℝ≥0 mΩ} {A₁ : ℝ≥0 → Ω → Set ℂ} {C C' : Set Ω} {β : Ω → BoundaryWord}
    {S : Set Lv.WordProfile} (hC : C' ⊆ C) (hS : StageLawOn κ b jumps P h E u l k ℓ 𝓖 A₁ C β S) :
    StageLawOn κ b jumps P h E u l k ℓ 𝓖 A₁ C' β S := by
  obtain ⟨⟨K, G, Y, M, hlaw, hcov⟩, hβm, ht, htc, hL⟩ := hS
  refine ⟨⟨K, G, Y, M, hlaw, ?_⟩, hβm, ht, ?_, ?_⟩
  · filter_upwards [hcov] with ω h1 h2 using h1 (hC h2)
  · filter_upwards [htc] with ω h1 h2 using h1 (hC h2)
  · filter_upwards [hL] with ω h1 h2 using h1 (hC h2)

/-- **Gluing the stage data of two pieces** by an event `C₁` of the line σ-algebra and of the completed retained past:
the glued word is `β₁` on `C₁` and `β₂` off it. -/
theorem stageLawOn_glue {𝓖 : Filtration ℝ≥0 mΩ} {A₁ : ℝ≥0 → Ω → Set ℂ} {C₁ C₂ : Set Ω} {β₁ β₂ : Ω → BoundaryWord}
    {T₁ T₂ : Set Lv.WordProfile} [DecidablePred (· ∈ C₁)] (hC𝓜 : MeasurableSet[lineFiltC P 𝓖 0] C₁)
    (hCm : MeasurableSet[aeSigma (stageMarks κ b jumps E u l k ℓ) P] C₁)
    (h₁ : StageLawOn κ b jumps P h E u l k ℓ 𝓖 A₁ C₁ β₁ T₁)
    (h₂ : StageLawOn κ b jumps P h E u l k ℓ 𝓖 A₁ C₂ β₂ T₂) :
    StageLawOn κ b jumps P h E u l k ℓ 𝓖 A₁ (C₁ ∪ C₂) (C₁.piecewise β₁ β₂) (T₁ ∪ T₂) := by
  obtain ⟨⟨K₁, G₁, Y₁, M₁, hlaw₁, hcov₁⟩, hβ₁m, ht₁, htc₁, hL₁⟩ := h₁
  obtain ⟨⟨K₂, G₂, Y₂, M₂, hlaw₂, hcov₂⟩, hβ₂m, ht₂, htc₂, hL₂⟩ := h₂
  refine ⟨⟨_, _, _, _, mvLaw_piecewiseOn ((lineFiltC P 𝓖).le 0) hC𝓜 hlaw₁ hlaw₂, ?_⟩,
    hβ₁m.piecewise hCm hβ₂m, ht₁.union ht₂, ?_, ?_⟩
  · filter_upwards [hcov₁, hcov₂] with ω e1 e2 hω hl
    by_cases h1 : ω ∈ C₁
    · exact Or.inl ⟨e1 h1 hl, h1⟩
    · exact Or.inr ⟨e2 (hω.resolve_left h1) hl, h1⟩
  · filter_upwards [htc₁, htc₂] with ω e1 e2 hω hl
    by_cases h1 : ω ∈ C₁
    · simp only [Set.piecewise, h1, ↓reduceIte]; exact Or.inl (e1 h1 hl)
    · simp only [Set.piecewise, h1, ↓reduceIte]; exact Or.inr (e2 (hω.resolve_left h1) hl)
  · filter_upwards [hL₁, hL₂] with ω e1 e2 hω he ho
    by_cases h1 : ω ∈ C₁
    · simp only [Set.piecewise, h1, ↓reduceIte]; exact e1 h1 he ho
    · simp only [Set.piecewise, h1, ↓reduceIte]; exact e2 (hω.resolve_left h1) he ho

/-- **Gluing two pieces valid on `D₁`, `D₂` by a separate selector `C`**: the glued data hold on
`(D₁ ∩ C) ∪ (D₂ \ C)`, with the word `β₁` on `C` and `β₂` off it. -/
theorem stageLawOn_glue' {𝓖 : Filtration ℝ≥0 mΩ} {A₁ : ℝ≥0 → Ω → Set ℂ} {D₁ D₂ C : Set Ω}
    {β₁ β₂ : Ω → BoundaryWord} {T₁ T₂ : Set Lv.WordProfile} [DecidablePred (· ∈ C)]
    (hC𝓜 : MeasurableSet[lineFiltC P 𝓖 0] C) (hCm : MeasurableSet[aeSigma (stageMarks κ b jumps E u l k ℓ) P] C)
    (h₁ : StageLawOn κ b jumps P h E u l k ℓ 𝓖 A₁ D₁ β₁ T₁)
    (h₂ : StageLawOn κ b jumps P h E u l k ℓ 𝓖 A₁ D₂ β₂ T₂) :
    StageLawOn κ b jumps P h E u l k ℓ 𝓖 A₁ ((D₁ ∩ C) ∪ (D₂ \ C)) (C.piecewise β₁ β₂) (T₁ ∪ T₂) := by
  obtain ⟨⟨K₁, G₁, Y₁, M₁, hlaw₁, hcov₁⟩, hβ₁m, ht₁, htc₁, hL₁⟩ := h₁
  obtain ⟨⟨K₂, G₂, Y₂, M₂, hlaw₂, hcov₂⟩, hβ₂m, ht₂, htc₂, hL₂⟩ := h₂
  refine ⟨⟨_, _, _, _, mvLaw_piecewiseOn ((lineFiltC P 𝓖).le 0) hC𝓜 hlaw₁ hlaw₂, ?_⟩,
    hβ₁m.piecewise hCm hβ₂m, ht₁.union ht₂, ?_, ?_⟩
  · filter_upwards [hcov₁, hcov₂] with ω e1 e2 hω hl
    rcases hω with hω | hω
    · exact Or.inl ⟨e1 hω.1 hl, hω.2⟩
    · exact Or.inr ⟨e2 hω.1 hl, hω.2⟩
  · filter_upwards [htc₁, htc₂] with ω e1 e2 hω hl
    rcases hω with hω | hω
    · simp only [Set.piecewise, hω.2, ↓reduceIte]; exact Or.inl (e1 hω.1 hl)
    · simp only [Set.piecewise, hω.2, ↓reduceIte]; exact Or.inr (e2 hω.1 hl)
  · filter_upwards [hL₁, hL₂] with ω e1 e2 hω he ho
    rcases hω with hω | hω
    · simp only [Set.piecewise, hω.2, ↓reduceIte]; exact e1 hω.1 he ho
    · simp only [Set.piecewise, hω.2, ↓reduceIte]; exact e2 hω.1 he ho

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **Countable profiles give the countable word types of every shift** (the types clause of CANON's
`Cz.SB2LowerStageLawInStatement`). -/
theorem types_of_profiles {C : Set Ω} {β : Ω → BoundaryWord} {S : Set Lv.WordProfile} (hS : S.Countable)
    (hp : ∀ᵐ ω ∂P, ω ∈ C → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      Lv.wordProfile (β ω) ∈ S) :
    (Lv.angleType κ (-(Real.pi / 2)) '' Lv.profileTypes κ S).Countable ∧
      ∀ᵐ ω ∂P, ω ∈ C → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        ∀ x : ℝ, angleWordType κ (-(Real.pi / 2)) (BoundaryWord.shiftW x (β ω)) ∈
          Lv.angleType κ (-(Real.pi / 2)) '' Lv.profileTypes κ S :=
  ⟨(Lv.countable_profileTypes κ hS).image _, by
    filter_upwards [hp] with ω hω hC hl x using Lv.angleWordType_shift_mem κ _ x (hω hC hl)⟩

end Stage

end InteractingSLE.Theorem14.SB.Fs
