/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2Part3PC
import InteractingSLE.Spec.ZhanGT4.A2Part1Crosscut

/-!
# A.2 part 3: reduction to finite physical contact

Packet PROVE-ZHAN-A2P3-PC. The finite physical-contact statements below are
remaining obligations, not theorems. Conditional adapters identify precisely
what is needed to complete `PairContactG3Statement` and `PairContactEightStatement`.
They use neither Theorem 1.2 nor Theorem 1.3.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory Bornology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A2X.P3

open QuantumZipper

/-- A finite physical contact: the precontact large hulls accumulate on an
interior point of the old small hull, or on the real line to the left of `r`.
This predicate contains no image map or image force coordinate. -/
def FinitePhysicalContact (x r : ℝ) (w₁ w₂ v₂ : ℝ≥0 → ℝ)
    (ζ₂ : ℝ≥0∞) (q : ℝ≥0) : Prop :=
  ∃ p : ℂ, p ∈ closure (preContactHulls (Strip.extPath w₂)
    (contactTime 0 (Strip.extPath w₂) (lifeEnd w₂ v₂ ζ₂) x (Strip.extPath w₁) q)) ∧
      ((p ∈ H ∧ p ∈ closure (physHull x (Strip.extPath w₁) q)) ∨
        ∃ s : ℝ, s ≤ r ∧ p = (s : ℂ))

/-- **Remaining obligation, G3.** At finite contact time, the large hulls
accumulate physically on the small hull or on `(-∞, x]`. -/
def FinitePhysicalContactG3Statement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ)
      (VL₂ : Fin 2 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
      (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞)
      (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
      (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 3 → ℝ≥0 → Ω → ℝ)
      (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      IsA2DualPairG3 κ y x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
        ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ₁ ω →
          contactTime 0 (Strip.extPath (W₂ · ω))
            (lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y (Strip.extPath (W₁ · ω)) q ≠ ⊤ →
          FinitePhysicalContact y x (W₁ · ω) (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) q

/-- **Remaining obligation, Eight.** At finite contact time, the large hulls
accumulate physically on the small hull or on `(-∞, x]`. -/
def FinitePhysicalContactEightStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ)
      (VL₂ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
      (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞)
      (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
      (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 2 → ℝ≥0 → Ω → ℝ)
      (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      IsA2DualPairEight κ x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
        ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ₁ ω →
          contactTime 0 (Strip.extPath (W₂ · ω))
            (lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x (Strip.extPath (W₁ · ω)) q ≠ ⊤ →
          FinitePhysicalContact x x (W₁ · ω) (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) q

/-- Infinite contact time supplies the unbounded alternative for any two
integrated paths; no conditional image law is needed. -/
theorem not_isBounded_preContactImage_of_paths_of_contact_eq_top
    {a₁ a₂ : ℝ} {nL₁ nR₁ nL₂ nR₂ : ℕ}
    {xL₁ ρL₁ : Fin nL₁ → ℝ} {xR₁ ρR₁ : Fin nR₁ → ℝ}
    {xL₂ ρL₂ : Fin nL₂ → ℝ} {xR₂ ρR₂ : Fin nR₂ → ℝ}
    {w₁ w₂ b₁ b₂ : ℝ≥0 → ℝ} {vL₁ : Fin nL₁ → ℝ≥0 → ℝ}
    {vR₁ : Fin nR₁ → ℝ≥0 → ℝ} {vL₂ : Fin nL₂ → ℝ≥0 → ℝ}
    {vR₂ : Fin nR₂ → ℝ≥0 → ℝ} {ζ₁ ζ₂ : ℝ≥0∞}
    (hp₁ : IsIntegratedSLEPath a₁ xL₁ xR₁ ρL₁ ρR₁ w₁ vL₁ vR₁ b₁ ζ₁)
    (hp₂ : IsIntegratedSLEPath a₂ xL₂ xR₂ ρL₂ ρR₂ w₂ vL₂ vR₂ b₂ ζ₂)
    {x : ℝ} {v₂ : ℝ≥0 → ℝ} {q : ℝ≥0} (hq : (q : ℝ≥0∞) < ζ₁)
    (hc : contactTime 0 (Strip.extPath w₂) (lifeEnd w₂ v₂ ζ₂)
      x (Strip.extPath w₁) q = ⊤) :
    ¬ IsBounded (preContactImage x w₁ w₂ v₂ ζ₂ q) := by
  have hζ₂ := lifetime_eq_top_of_contact_eq_top hc
  have hw₂ : Continuous w₂ := by
    have hh := hp₂.2.2.2.1
    rw [hζ₂] at hh
    simpa only [ENNReal.coe_lt_top, ofPred_true, continuousOn_univ] using hh
  exact not_isBounded_preContactImage_of_contact_eq_top hp₁.2.2.2.1 hp₁.1 hq hw₂ hp₂.1 hc

/-- **Conditional adapter, G3.** Only finite physical contact remains after the
capacity and boundary-extension arguments of this packet. -/
theorem pairContactG3Statement_of_finitePhysicalContact {κ : ℝ}
    (hfinite : FinitePhysicalContactG3Statement.{u} κ) : PairContactG3Statement.{u} κ := by
  intro hκ4 hκ8 y x hyx hx Ω mΩ P hP 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair q hq0
  have hsmall := A2P1.a2SmallCrosscutG3Statement κ hκ4 hκ8 y x hyx hx
    P 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair.2.1
  filter_upwards [hpair.1.ae_isIntegratedSLEPath, hpair.2.1.ae_isIntegratedSLEPath,
    hsmall, hfinite hκ4 hκ8 y x hyx hx P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂
      𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair q hq0] with ω hp₂ hp₁ hs hf hq
  by_cases hc : contactTime 0 (Strip.extPath (W₂ · ω))
      (lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y (Strip.extPath (W₁ · ω)) q = ⊤
  · exact Or.inr (Or.inl (not_isBounded_preContactImage_of_paths_of_contact_eq_top hp₁ hp₂ hq hc))
  by_cases hb : IsBounded (preContactImage y (W₁ · ω) (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) q)
  · obtain ⟨p, hpA, hpSide⟩ := hf hq hc
    obtain ⟨γ, hγ⟩ := hs
    obtain ⟨η, hη, -⟩ := hγ.2.2.2
    obtain ⟨u, hu, hucl⟩ := exists_real_le_mem_closure_physMap_image hp₁ hη hq
      (preContactHulls_subset_H _ _) (disjoint_preContactHulls _ _ _ _ _) hb
      (i := (1 : Fin 3)) (by simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using sub_nonneg.2 hyx.le)
      hpA (by simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, add_sub_cancel] using hpSide)
    exact Or.inr (Or.inr ⟨u, hu, hucl⟩)
  · exact Or.inr (Or.inl hb)

/-- **Conditional adapter, Eight.** Only finite physical contact remains. -/
theorem pairContactEightStatement_of_finitePhysicalContact {κ : ℝ}
    (hfinite : FinitePhysicalContactEightStatement.{u} κ) : PairContactEightStatement.{u} κ := by
  intro hκ8 x hx Ω mΩ P hP 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair q hq0
  have hsmall := A2P1.a2SmallCrosscutEightStatement κ hκ8 x hx
    P 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair.2.1
  filter_upwards [hpair.1.ae_isIntegratedSLEPath, hpair.2.1.ae_isIntegratedSLEPath,
    hsmall, hfinite hκ8 x hx P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂
      𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair q hq0] with ω hp₂ hp₁ hs hf hq
  by_cases hc : contactTime 0 (Strip.extPath (W₂ · ω))
      (lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x (Strip.extPath (W₁ · ω)) q = ⊤
  · exact Or.inr (Or.inl (not_isBounded_preContactImage_of_paths_of_contact_eq_top hp₁ hp₂ hq hc))
  by_cases hb : IsBounded (preContactImage x (W₁ · ω) (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) q)
  · obtain ⟨p, hpA, hpSide⟩ := hf hq hc
    obtain ⟨γ, hγ⟩ := hs
    obtain ⟨η, hη, -⟩ := hγ.2.2.2
    obtain ⟨u, hu, hucl⟩ := exists_real_le_mem_closure_physMap_image hp₁ hη hq
      (preContactHulls_subset_H _ _) (disjoint_preContactHulls _ _ _ _ _) hb
      (i := (0 : Fin 2)) (by simp only [Matrix.cons_val_zero, le_refl])
      hpA (by simpa only [Matrix.cons_val_zero, add_zero] using hpSide)
    exact Or.inr (Or.inr ⟨u, hu, hucl⟩)
  · exact Or.inr (Or.inl hb)

end InteractingSLE.ZhanGT4.A2X.P3
