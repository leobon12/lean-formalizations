/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FsGlue

/-!
# Gluing four pieces of the induction's stage data (D86)

Packet PROVE-SB2-CANON, round 9. (P1)'s step at a flow stage `ℓ'` glues four pieces of F3LAW's stage data
(`Fs.StageLawOn`): base, tail, root and zero, in this order of priority, by three selectors `Qs`, `Ts`, `Rs` (events of
the line σ-algebra and of the completed retained past). **`stageLawOn_glue4`** applies `Fs.stageLawOn_glue'` three
times; the glued word is the base word on `Qs`. **`mem_glue4`**: a sample is in the glued event as soon as it is in
the piece its selectors route it to.

No probabilistic input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cz

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Lv Lk Mf Ms

/-- **The glued event of four pieces**: base on `Qs`, then tail on `Ts`, then root on `Rs`, then zero. -/
def glue4Set {Ω : Type*} (Qs Ts Rs DB DT DR DZ : Set Ω) : Set Ω :=
  (DB ∩ Qs) ∪ (((DT ∩ Ts) ∪ (((DR ∩ Rs) ∪ (DZ \ Rs)) \ Ts)) \ Qs)

/-- **A sample routed to a piece containing it is in the glued event.** -/
theorem mem_glue4 {Ω : Type*} {Qs Ts Rs DB DT DR DZ : Set Ω} {ω : Ω} (hB : ω ∈ Qs → ω ∈ DB)
    (hT : ω ∉ Qs → ω ∈ Ts → ω ∈ DT) (hR : ω ∉ Qs → ω ∉ Ts → ω ∈ Rs → ω ∈ DR)
    (hZ : ω ∉ Qs → ω ∉ Ts → ω ∉ Rs → ω ∈ DZ) : ω ∈ glue4Set Qs Ts Rs DB DT DR DZ := by
  by_cases hq : ω ∈ Qs
  · exact Or.inl ⟨hB hq, hq⟩
  refine Or.inr ⟨?_, hq⟩
  by_cases hf : ω ∈ Ts
  · exact Or.inl ⟨hT hq hf, hf⟩
  refine Or.inr ⟨?_, hf⟩
  by_cases hr : ω ∈ Rs
  · exact Or.inl ⟨hR hq hf hr, hr⟩
  · exact Or.inr ⟨hZ hq hf hr, hr⟩

/-- **Gluing four pieces of stage data** by the selectors `Qs`, `Ts`, `Rs`; the glued word is the base word on `Qs`. -/
theorem stageLawOn_glue4 {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ' : ℕ}
    {𝓖' : MeasureTheory.Filtration ℝ≥0 mΩ} {A₁' : ℝ≥0 → Ω → Set ℂ} {Qs Ts Rs DB DT DR DZ : Set Ω}
    {βB βT βR βZ : Ω → BoundaryWord} {SB ST SR SZ : Set Lv.WordProfile}
    (hQ1 : MeasurableSet[lineFiltC P 𝓖' 0] Qs)
    (hQ2 : MeasurableSet[aeSigma (stageMarks κ b jumps E u l k ℓ') P] Qs)
    (hF1 : MeasurableSet[lineFiltC P 𝓖' 0] Ts)
    (hF2 : MeasurableSet[aeSigma (stageMarks κ b jumps E u l k ℓ') P] Ts)
    (hR1 : MeasurableSet[lineFiltC P 𝓖' 0] Rs)
    (hR2 : MeasurableSet[aeSigma (stageMarks κ b jumps E u l k ℓ') P] Rs)
    (hB : Fs.StageLawOn κ b jumps P h E u l k ℓ' 𝓖' A₁' DB βB SB)
    (hT : Fs.StageLawOn κ b jumps P h E u l k ℓ' 𝓖' A₁' DT βT ST)
    (hR : Fs.StageLawOn κ b jumps P h E u l k ℓ' 𝓖' A₁' DR βR SR)
    (hZ : Fs.StageLawOn κ b jumps P h E u l k ℓ' 𝓖' A₁' DZ βZ SZ) :
    ∃ (β : Ω → BoundaryWord) (S : Set Lv.WordProfile),
      Fs.StageLawOn κ b jumps P h E u l k ℓ' 𝓖' A₁' (glue4Set Qs Ts Rs DB DT DR DZ) β S ∧
      ∀ ω ∈ Qs, β ω = βB ω := by
  classical
  have h1 := Fs.stageLawOn_glue' hR1 hR2 hR hZ
  have h2 := Fs.stageLawOn_glue' hF1 hF2 hT h1
  have h3 := Fs.stageLawOn_glue' hQ1 hQ2 hB h2
  exact ⟨_, _, h3, fun ω hω => Set.piecewise_eq_of_mem _ _ _ hω⟩

end InteractingSLE.Theorem14.SB.Cz
