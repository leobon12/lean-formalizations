/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2Part2Count

/-!
# A.2, part 2: the large hull lies on the bounded side of the small crosscut

Packet PROVE-ZHAN-A2P2. Source: Astra, *Follow-up proofs and dependency audit*, §A.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L537–L561; R38, R53). The targets are
`A2X.A2HullInsideG3Statement` (`4 < κ < 8`) and `A2X.A2HullInsideEightStatement` (`κ ≥ 8`) of
`Spec/ZhanGT4/CrosscutA2.lean`.

The source's proof of part 2 has two steps:

1. (L548–L553, **the conditional separation**) "Condition on a stopped large-curve prefix before lifetime. The
   conditional small curve in its complement has exactly the same endpoint configuration, with the large tip
   replacing `x₂`. This conditional image is maximal at first contact. … Thus the small strip endpoint theorem applies
   to the completed conditional image. Its endpoint lies strictly between `W₂` and `g₂(p₂)`, so its crosscut
   separates the large tip from infinity."
2. (L555–L561, **the countable argument**) "If a large-curve point escapes the closed bounded side of `J`, choose a
   rational polygonal crosscut `α` … Stop the large curve at its first hit of `α ∪ γ` … The countable union over
   `α, γ` has probability zero."

Step 2 is proved here in full (`A2Part2Count.lean`, `A2Part2Domain.lean`). Step 1, at the stopping times step 2 uses
(the first hit of a compact subset of `ℍ` inside the strip life of the inner mark), is the named statement
**`A2TipSepG3Statement`** / **`A2TipSepEightStatement`**: almost surely, at that first hit, the tip is separated from
`∞` by the small crosscut (`TipSeparated`). It is not proved here (see the handoff
`planning/handoffs/PROVE-ZHAN-A2P2.md`: maximality at first contact, the strip endpoint theorem for the conditional
image, and making the pathwise first hit a stopping time of the large curve's filtration); `tipSeparated_of_image`
reduces it to the statement that the centred image of the small curve before contact contains a crosscut from a
negative to a positive point.

## Main results

* `a2HullInsideG3Statement_of_tipSep : A2TipSepG3Statement κ → A2X.A2HullInsideG3Statement κ`;
* `a2HullInsideEightStatement_of_tipSep : A2TipSepEightStatement κ → A2X.A2HullInsideEightStatement κ`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A2Part2

open QuantumZipper

/-! ### The conditional separation at first hits (A.2 L548–L553) -/

/-- **A.2, part 2, step 1, (G3)** (L548–L553, at the stopping times of L558): for every (G3) dual pair and every
compact `L ⊆ ℍ`, almost surely, if the large hulls first meet `L` at a time `s` of the strip life of the inner mark
`x`, then the large tip at time `s` is separated from `∞` by every small crosscut `J = γ((0, 1))`. -/
def A2TipSepG3Statement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
      (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
      (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 3 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      A2X.IsA2DualPairG3 κ y x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
        ∀ L : Set ℂ, IsCompact L → L ⊆ H →
          ∀ᵐ ω ∂P, ∀ s : ℝ≥0, IsFirstHit (Strip.extPath (W₂ · ω)) L s →
            Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) s →
              ∀ γ : ℝ → ℂ, A2X.IsSmallCrosscut y (W₁ · ω) (ζ₁ ω) γ →
                TipSeparated (Strip.extPath (W₂ · ω)) s (γ '' Ioo 0 1)

/-- **A.2, part 2, step 1, (Eight)** (L548–L553 with §A.3.1): the (Eight) analogue of `A2TipSepG3Statement`. -/
def A2TipSepEightStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
      (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
      (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 2 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      A2X.IsA2DualPairEight κ x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
        ∀ L : Set ℂ, IsCompact L → L ⊆ H →
          ∀ᵐ ω ∂P, ∀ s : ℝ≥0, IsFirstHit (Strip.extPath (W₂ · ω)) L s →
            Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) s →
              ∀ γ : ℝ → ℂ, A2X.IsSmallCrosscut x (W₁ · ω) (ζ₁ ω) γ →
                TipSeparated (Strip.extPath (W₂ · ω)) s (γ '' Ioo 0 1)

/-! ### The countable argument (A.2 L555–L561) -/

/-- The countably many compact sets of the countable argument: the closed good rational chains of `ℍ`. A statement
holding almost surely for each compact `L ⊆ ℍ` holds almost surely for all of them at once. -/
theorem ae_forall_goodChain {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Q : Set ℂ → Ω → Prop}
    (h : ∀ L : Set ℂ, IsCompact L → L ⊆ H → ∀ᵐ ω ∂P, Q L ω) :
    ∀ᵐ ω ∂P, ∀ F : Finset (ℚ × ℚ × ℚ), IsGoodChain H F → Q (chainClosed F) ω := by
  rw [ae_all_iff]
  intro F
  by_cases hF : IsGoodChain H F
  · filter_upwards [h (chainClosed F) (isCompact_chainClosed F) hF.chainClosed_subset] with ω hω
    exact fun _ => hω
  · exact Eventually.of_forall fun ω hF' => absurd hF' hF

/-- **A.2, part 2, (G3)** (`A2X.A2HullInsideG3Statement`) from the conditional separation at first hits: for every
(G3) dual pair, almost surely the large hull before its first force collision misses the unbounded side of the small
crosscut. -/
theorem a2HullInsideG3Statement_of_tipSep {κ : ℝ} (h : A2TipSepG3Statement.{u} κ) :
    A2X.A2HullInsideG3Statement.{u} κ := by
  intro hκ4 hκ8 y x hyx hx Ω mΩ P hP 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair
  have hall := ae_forall_goodChain (h hκ4 hκ8 y x hyx hx P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair)
  filter_upwards [hall, hpair.1.2.2.2.2] with ω hω hp γ hγ
  obtain ⟨D, hD⟩ := exists_isCrosscutDomain hγ.1 (by rw [hγ.2.1]; linarith [hγ.2.2.1])
  exact ⟨D, hD, disjoint_lifeHullClosure_of_tipSeparated hp.2.2.2.1 hp.1 hD
    fun F hF s hs hl => hω F hF s hs hl γ hγ⟩

/-- **A.2, part 2, (Eight)** (`A2X.A2HullInsideEightStatement`) from the conditional separation at first hits. -/
theorem a2HullInsideEightStatement_of_tipSep {κ : ℝ} (h : A2TipSepEightStatement.{u} κ) :
    A2X.A2HullInsideEightStatement.{u} κ := by
  intro hκ8 x hx Ω mΩ P hP 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair
  have hall := ae_forall_goodChain (h hκ8 x hx P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair)
  filter_upwards [hall, hpair.1.2.2.2.2] with ω hω hp γ hγ
  obtain ⟨D, hD⟩ := exists_isCrosscutDomain hγ.1 (by rw [hγ.2.1]; linarith [hγ.2.2.1])
  exact ⟨D, hD, disjoint_lifeHullClosure_of_tipSeparated hp.2.2.2.1 hp.1 hD
    fun F hF s hs hl => hω F hF s hs hl γ hγ⟩

/-- `∀ κ` form (G3), as consumed through `A2X.forall_fourForceCrosscutG3LifeStatement_of_dual`. -/
theorem forall_a2HullInsideG3Statement_of_tipSep (h : ∀ κ : ℝ, A2TipSepG3Statement.{u} κ) :
    ∀ κ : ℝ, A2X.A2HullInsideG3Statement.{u} κ :=
  fun κ => a2HullInsideG3Statement_of_tipSep (h κ)

/-- `∀ κ` form (Eight), as consumed through `A2X.forall_threeForceCrosscutEightStatement_of_dual`. -/
theorem forall_a2HullInsideEightStatement_of_tipSep (h : ∀ κ : ℝ, A2TipSepEightStatement.{u} κ) :
    ∀ κ : ℝ, A2X.A2HullInsideEightStatement.{u} κ :=
  fun κ => a2HullInsideEightStatement_of_tipSep (h κ)

end InteractingSLE.ZhanGT4.A2Part2
