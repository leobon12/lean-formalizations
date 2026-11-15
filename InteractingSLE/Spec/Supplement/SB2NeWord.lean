/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NeHullV

/-!
# Versions of functions measurable up to null sets; F2b′'s stop word

Packet PROVE-AUX61-NOJUMP (round 22, component F). F3's word `β₁` is only measurable for `aeSigma (stageMarks) P`.
The stops need a word measurable for `lineC0 = mΩ ⊓ aeSigma (lineSigma0) P` (`Nd.StopIn.hcw`):

* **`exists_version_real`**: a real function measurable for `aeSigma 𝒢 P` agrees almost surely with a `𝒢`-measurable
  one (`g = inf {r ∈ ℚ : ω ∈ T r}` for `𝒢`-sets `T r` a.e. equal to `{f < r}`); no measurability of `f` for `mΩ` is
  needed. Then `exists_version_nat`, `exists_version_seq`, **`exists_version_word`** (`Restart.BoundaryWord = ℕ × (ℕ → ℝ) ×
  (ℕ → ℝ)`);
* **`stageMarks_le_lineC0`**, **`exists_stopWord`**: a `lineC0`-measurable word equal almost surely to
  `shiftW x₀ β₁`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Ne

section Version

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝒢 : MeasurableSpace Ω}

open Classical in
/-- **A `𝒢`-measurable version of a real function measurable up to null sets.** -/
theorem exists_version_real {f : Ω → ℝ} (hf : Measurable[LocalSets.aeSigma 𝒢 P] f) :
    ∃ g : Ω → ℝ, Measurable[𝒢] g ∧ ∀ᵐ ω ∂P, f ω = g ω := by
  have hS : ∀ r : ℚ, ∃ T : Set Ω, MeasurableSet[𝒢] T ∧ f ⁻¹' Iio (r : ℝ) =ᵐ[P] T := fun r =>
    hf measurableSet_Iio
  choose T hT hTe using hS
  set G : Ω → EReal := fun ω => ⨅ r : ℚ, if ω ∈ T r then ((r : ℝ) : EReal) else ⊤ with hG
  have hGm : Measurable[𝒢] G :=
    Measurable.iInf fun r => Measurable.ite (hT r) measurable_const measurable_const
  refine ⟨fun ω => (G ω).toReal, hGm.ereal_toReal, ?_⟩
  have hall : ∀ᵐ ω ∂P, ∀ r : ℚ, (f ω < r ↔ ω ∈ T r) := by
    rw [ae_all_iff]
    intro r
    filter_upwards [hTe r] with ω hω
    exact Iff.of_eq hω
  filter_upwards [hall] with ω hω
  have hterm : ∀ r : ℚ, (if ω ∈ T r then ((r : ℝ) : EReal) else ⊤) =
      if f ω < r then ((r : ℝ) : EReal) else ⊤ := fun r => by
    by_cases h : f ω < r
    · simp only [(hω r).1 h, h, ↓reduceIte]
    · simp only [show ω ∉ T r from fun h' => h ((hω r).2 h'), h, ↓reduceIte]
  have hlow : ((f ω : ℝ) : EReal) ≤ G ω := le_iInf fun r => by
    rw [hterm r]
    split_ifs with h
    · exact EReal.coe_le_coe_iff.2 h.le
    · exact le_top
  have hup : ∀ r : ℚ, f ω < r → G ω ≤ ((r : ℝ) : EReal) := fun r h => by
    refine (iInf_le _ r).trans ?_
    rw [hterm r]
    simp only [h, ↓reduceIte, le_refl]
  obtain ⟨r₀, hr₀⟩ := exists_rat_gt (f ω)
  have hne_top : G ω ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) (hup r₀ hr₀)
  have hne_bot : G ω ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlow
  have hco : ((G ω).toReal : EReal) = G ω := EReal.coe_toReal hne_top hne_bot
  have h1 : f ω ≤ (G ω).toReal := by
    have := hlow
    rw [← hco] at this
    exact EReal.coe_le_coe_iff.1 this
  have h2 : (G ω).toReal ≤ f ω := by
    by_contra hc
    rw [not_le] at hc
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hc
    have h3 := hup r hr1
    rw [← hco] at h3
    have h4 := EReal.coe_le_coe_iff.1 h3
    linarith
  exact le_antisymm h1 h2

theorem exists_version_nat {f : Ω → ℕ} (hf : Measurable[LocalSets.aeSigma 𝒢 P] f) :
    ∃ g : Ω → ℕ, Measurable[𝒢] g ∧ ∀ᵐ ω ∂P, f ω = g ω := by
  obtain ⟨g, hg, hfg⟩ := @exists_version_real Ω mΩ P 𝒢 (fun ω => (f ω : ℝ))
    (@Measurable.comp _ _ _ (LocalSets.aeSigma 𝒢 P) _ _ _ _ measurable_from_nat hf)
  refine ⟨fun ω => ⌊g ω⌋₊, hg.nat_floor, ?_⟩
  filter_upwards [hfg] with ω hω
  show f ω = ⌊g ω⌋₊
  rw [← hω, Nat.floor_natCast]

theorem exists_version_seq {f : Ω → ℕ → ℝ} (hf : Measurable[LocalSets.aeSigma 𝒢 P] f) :
    ∃ g : Ω → ℕ → ℝ, Measurable[𝒢] g ∧ ∀ᵐ ω ∂P, f ω = g ω := by
  have hi : ∀ i : ℕ, ∃ g : Ω → ℝ, Measurable[𝒢] g ∧ ∀ᵐ ω ∂P, f ω i = g ω := fun i =>
    @exists_version_real Ω mΩ P 𝒢 _ (@Measurable.comp _ _ _ (LocalSets.aeSigma 𝒢 P) _ _ _ _ (measurable_pi_apply i) hf)
  choose g hg hfg using hi
  refine ⟨fun ω i => g i ω, @Measurable.of_eval Ω ℕ (fun _ => ℝ) 𝒢 _ (fun ω i => g i ω) hg, ?_⟩
  filter_upwards [ae_all_iff.2 hfg] with ω hω using funext hω

/-- **A `𝒢`-measurable version of a boundary word measurable up to null sets.** -/
theorem exists_version_word {f : Ω → Restart.BoundaryWord} (hf : Measurable[LocalSets.aeSigma 𝒢 P] f) :
    ∃ g : Ω → Restart.BoundaryWord, Measurable[𝒢] g ∧ ∀ᵐ ω ∂P, f ω = g ω := by
  obtain ⟨g1, hg1, h1⟩ := @exists_version_nat Ω mΩ P 𝒢 _
    (@Measurable.comp _ _ _ (LocalSets.aeSigma 𝒢 P) _ _ _ _ measurable_fst hf)
  obtain ⟨g2, hg2, h2⟩ := @exists_version_seq Ω mΩ P 𝒢 _
    (@Measurable.comp _ _ _ (LocalSets.aeSigma 𝒢 P) _ _ _ _ (measurable_fst.comp measurable_snd) hf)
  obtain ⟨g3, hg3, h3⟩ := @exists_version_seq Ω mΩ P 𝒢 _
    (@Measurable.comp _ _ _ (LocalSets.aeSigma 𝒢 P) _ _ _ _ (measurable_snd.comp measurable_snd) hf)
  refine ⟨fun ω => (g1 ω, g2 ω, g3 ω), hg1.prodMk (hg2.prodMk hg3), ?_⟩
  filter_upwards [h1, h2, h3] with ω e1 e2 e3
  exact Prod.ext e1 (Prod.ext e2 e3)

end Version


/-! ### F2b′'s stop word -/

section Stop

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide Ms Nc Nd

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}

omit mΩ [StandardBorelSpace Ω] in
theorem stageMarks_le_lineSigma0 (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length) :
    stageMarks κ b jumps E u l k ℓ ≤ lineSigma0 κ b jumps E u l k ℓ := by
  refine sup_le_sup le_rfl ?_
  rw [← WalkSide.pastSigma_capSpec_of_le (κ := κ) (b := b) (jumps := jumps) (θ := -(Real.pi / 2))
    (τ := ((0 : ℝ≥0) : ℝ≥0∞)) hℓ.le (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) le_rfl]
  exact pastSigma_mono _ _ (Nat.le_succ ℓ)

theorem stageMarks_le_lineC0 (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤))) :
    stageMarks κ b jumps E u l k ℓ ≤ lineC0 P κ b jumps E u l k ℓ := by
  have h0 : lineSigma0 κ b jumps E u l k ℓ ≤ mΩ :=
    (lineSigma0_le_T hb hE hER hℓ hwℓ 0).trans (lineSigmaT_le hb hE hER hlθ hℓ hwℓ 0)
  have h1 : lineSigma0 κ b jumps E u l k ℓ ≤ lineC0 P κ b jumps E u l k ℓ :=
    le_inf h0 fun s hs => ⟨s, hs, EventuallyEq.rfl⟩
  exact (stageMarks_le_lineSigma0 hℓ).trans h1

/-- **F2b′'s stop word**: measurable for `lineC0`, almost surely the retained word shifted by the entry value. -/
theorem exists_stopWord (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {x₀ : Ω → ℝ} (hx₀ : Measurable[lineC0 P κ b jumps E u l k ℓ] x₀) {β₁ : Ω → Restart.BoundaryWord}
    (hβ : Measurable[LocalSets.aeSigma (stageMarks κ b jumps E u l k ℓ) P] β₁) :
    ∃ cw : Ω → Restart.BoundaryWord, Measurable[lineC0 P κ b jumps E u l k ℓ] cw ∧
      ∀ᵐ ω ∂P, cw ω = BoundaryWord.shiftW (x₀ ω) (β₁ ω) := by
  obtain ⟨β', hβ'm, hβ'⟩ := @exists_version_word Ω mΩ P (stageMarks κ b jumps E u l k ℓ) β₁ hβ
  have hβ'C : Measurable[lineC0 P κ b jumps E u l k ℓ] β' :=
    hβ'm.mono (stageMarks_le_lineC0 hb hE hER hlθ hℓ hwℓ) le_rfl
  refine ⟨fun ω => BoundaryWord.shiftW (x₀ ω) (β' ω), BoundaryWord.measurable_shiftW.comp (hx₀.prodMk hβ'C), ?_⟩
  filter_upwards [hβ'] with ω hω
  rw [hω]

end Stop

end InteractingSLE.Theorem14.SB.Ne
