/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux97ProofIdent
import InteractingSLE.Spec.Supplement.W5CommonSeed

/-!
# Theorem W5's common-seed comparison needs only the seed germ of Aux. lemma 97's identification

Packet PROVE-AUX97-B. Sources: Aux. lemma 97's proof (`source/spec/p289-336.md` L553–L576, pp. 326–327); Theorem W5's
proof, common-seed paragraph (`source/spec/p529-576.md` L133, p. 534: "transfer the entire pair stopped in a small seed
neighborhood … Choose `a₀ ∈ (0, A)` so small that the first prefix through `a₀` is within this comparison
neighborhood").

W5 consumes Aux. lemma 97 only at arbitrarily small positive prefixes (`Supp9.W5CommonSeedStatement`). For that the
per-angle identification is needed only on a random positive initial time interval, not up to the exit from a ball of
a prescribed radius:

* **`Aux97GermIdentStatement`** (named input): `Aux97LocalIdentStatement` with the agreement only on a positive
  initial interval `[0, δ]` (on `{0 < ζ}`). It is the form a local change of measure through a positive driving stop
  (Aux. lemma 55's local stop) supplies, with no restart;
* `aux97GermIdent_of_localIdent`: it follows from `Aux97LocalIdentStatement` (a path continuous at its seed `0`
  leaves `B̄(0, R/2)` only after a positive time, `ballExit_pos`);
* **`Supp9.w5CommonSeedStatement_of_germIdent`**: `Prop74OrderStatement → Aux97GermIdentStatement →
  W5CommonSeedStatement` (recentering at the common seed as in `Supp9.w5CommonSeedStatement_of_aux97`; Proposition 7.4
  for the two flow lines of the common recoded field under `Q`; prefix congruence; `P ≪ Q`);
* `Supp9D.w5Statement_of_germIdent`: Theorem W5 with `W5CommonSeedStatement` replaced by these two inputs.

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

/-- **Named input: Aux. lemma 97's per-angle identification on a seed germ.** As `Aux97LocalIdentStatement` (one
probability measure `Q` equivalent to `P` and one field `X` that is a GFF with the two-height data `prop74Data (−b₋) b₊`
under `Q`, both chosen before the angle), but for each non-threshold angle `θ` and each angle-`θ` flow line `η` of `h`
from `0` the flow line `η'` of `X` under `Q` agrees with `η` only on a random positive initial interval: `Q`-almost
surely on `{0 < ζ}` there is `δ > 0`, strictly before both lifetimes, with `η = η'` on `[0, δ]`. -/
def Aux97GermIdentStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ R bm bp : ℝ, 0 < R → (∀ y ∈ Ioo (-R) 0, b y = bm) → (∀ y ∈ Ioo 0 R, b y = bp) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∃ (Q : Measure Ω) (X : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsProbabilityMeasure Q ∧ P ≪ Q ∧ Q ≪ P ∧
      IsGFFWithBoundaryData Q X (prop74Data (-bm) bp) {0} ∧
      ∀ θ : ℝ, ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b jumps 0 θ) (flowLineRhoR κ b jumps 0 θ) 0
          (flowLineXL b jumps 0) (flowLineXR b jumps 0) →
        ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps 0 θ P h η ζ →
        ∃ (η' : Ω → ℝ≥0 → ℂ) (ζ' : Ω → ℝ≥0∞), IsFlowLine κ (prop74Data (-bm) bp) {0} 0 θ Q X η' ζ' ∧
          ∀ᵐ ω ∂Q, 0 < ζ ω → ∃ δ : ℝ≥0, 0 < δ ∧ (δ : ℝ≥0∞) < ζ ω ∧ (δ : ℝ≥0∞) < ζ' ω ∧
            ∀ t ≤ δ, η ω t = η' ω t

/-- The germ form of the identification is implied by the ball-exit form (with the radius `R/2`): on `{0 < ζ}` the
trace starts at `0` and is continuous at `0`, so it leaves `B̄(0, R/2)` only after a positive time. -/
theorem aux97GermIdent_of_localIdent (hid : Aux97LocalIdentStatement.{u}) : Aux97GermIdentStatement.{u} := by
  intro κ hκ hκ4 b J hb R bm bp hR hbm hbp Ω _ P _ h hh
  obtain ⟨Q, X, hQ, hPQ, hQP, hX, hloc⟩ :=
    hid κ hκ hκ4 b J hb R bm bp hR hbm hbp (R / 2) (half_pos hR) (half_lt_self hR) P h hh
  refine ⟨Q, X, hQ, hPQ, hQP, hX, fun θ hT η ζ hη => ?_⟩
  obtain ⟨η', ζ', hη', hag⟩ := hloc θ hT η ζ hη
  refine ⟨η', ζ', hη', ?_⟩
  obtain ⟨_h', _𝓕, _W, _VL, _VR, _B, _htr, _hcpl, htrace⟩ := hη
  filter_upwards [hag, hQP.ae_le htrace] with ω hω ht hζ
  have h0 : (fun t => η ω t - ((0 : ℝ) : ℂ)) = η ω := by
    funext t
    rw [Complex.ofReal_zero, sub_zero]
  have hex : 0 < ballExit (R / 2) (η ω) := by
    have hpos := ballExit_pos (half_pos hR) ht.1 hζ ht.2.1
    rwa [h0] at hpos
  obtain ⟨δ, hδ0, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (lt_min hex hζ)
  have hδe : (δ : ℝ≥0∞) ≤ ballExit (R / 2) (η ω) := (hδ.trans_le (min_le_left _ _)).le
  have hδζ : (δ : ℝ≥0∞) < ζ ω := hδ.trans_le (min_le_right _ _)
  refine ⟨δ, ENNReal.coe_pos.1 hδ0, hδζ, (hω δ hδe hδζ).1, fun t ht => ?_⟩
  have ht' : (t : ℝ≥0∞) ≤ δ := ENNReal.coe_le_coe.2 ht
  exact (hω t (le_trans ht' hδe) (lt_of_le_of_lt ht' hδζ)).2

end Sec7

namespace Supp9

/-- **Theorem W5's common-seed comparison from Proposition 7.4 and the germ identification** (p. 534, with p. 327):
recenter the two flow lines at their common seed `x`; if a seed is at the continuation threshold its lifetime is `0`
almost surely and the claim is vacuous; otherwise the data are the two seed heights on `(−R, 0) ∪ (0, R)`, and under
the common measure `Q` the two recentered paths agree on positive initial intervals with two flow lines of one field `X`
with the two-height data, which Proposition 7.4 orders; translate back and use `P ≪ Q`. -/
theorem w5CommonSeedStatement_of_germIdent (h74 : Sec7.Prop74OrderStatement.{u})
    (hg : Sec7.Aux97GermIdentStatement.{u}) : W5CommonSeedStatement.{u} := by
  intro κ hκ hκ4 b J hb x θ₁ θ₂ hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  have hb₀ : IsPiecewiseConstantBoundaryData (fun y => b (y + x)) (J.image (· - x)) :=
    Exist.isPiecewiseConstant_comp_add hb x
  have hh₀ := IsGFFWithBoundaryData.recenter hb x hh
  have hη₁' := IsFlowLine.recenter hη₁
  have hη₂' := IsFlowLine.recenter hη₂
  -- inadmissible seeds: the lifetime is `0` almost surely
  by_cases hT₁ : ForceWord.ThresholdCondition (flowLineRhoL κ (fun y => b (y + x)) (J.image (· - x)) 0 θ₁)
      (flowLineRhoR κ (fun y => b (y + x)) (J.image (· - x)) 0 θ₁) 0
      (flowLineXL (fun y => b (y + x)) (J.image (· - x)) 0) (flowLineXR (fun y => b (y + x)) (J.image (· - x)) 0)
  · obtain ⟨_h', _𝓕, _W, _VL, _VR, _B, _htr, hcpl, _htrace⟩ := hη₁'
    filter_upwards [IsIntegratedSLEEvolution.ae_lifetime_eq_zero_of_threshold hcpl.1 hT₁] with ω hω h1 _
    exact absurd hω h1.ne'
  by_cases hT₂ : ForceWord.ThresholdCondition (flowLineRhoL κ (fun y => b (y + x)) (J.image (· - x)) 0 θ₂)
      (flowLineRhoR κ (fun y => b (y + x)) (J.image (· - x)) 0 θ₂) 0
      (flowLineXL (fun y => b (y + x)) (J.image (· - x)) 0) (flowLineXR (fun y => b (y + x)) (J.image (· - x)) 0)
  · obtain ⟨_h', _𝓕, _W, _VL, _VR, _B, _htr, hcpl, _htrace⟩ := hη₂'
    filter_upwards [IsIntegratedSLEEvolution.ae_lifetime_eq_zero_of_threshold hcpl.1 hT₂] with ω hω _ h2
    exact absurd hω h2.ne'
  -- the seed neighbourhood: no jump candidate in `(−R, 0) ∪ (0, R)`
  obtain ⟨R, hR, hRJ⟩ := Supp7.exists_pos_forall_notMem (J.image (· - x)) 0
  have hleft : ∀ y ∈ Ioo (-R) 0, b (y + x) = b (-R / 2 + x) := fun y hy =>
    Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb₀ (a := -R) (c := 0)
      (fun z hz => by simpa only [zero_sub] using (hRJ z hz).2) ⟨by linarith, by linarith⟩ hy
  have hright : ∀ y ∈ Ioo 0 R, b (y + x) = b (R / 2 + x) := fun y hy =>
    Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb₀ (a := 0) (c := R)
      (fun z hz => by simpa only [zero_add] using (hRJ z hz).1) ⟨by linarith, by linarith⟩ hy
  -- one common measure and field; the two germ identifications
  obtain ⟨Q, X, hQ, hPQ, -, hX, hloc⟩ :=
    hg κ hκ hκ4 (fun y => b (y + x)) (J.image (· - x)) hb₀ R (b (-R / 2 + x)) (b (R / 2 + x)) hR hleft hright
      P _ hh₀
  have := hQ
  obtain ⟨η₁', ζ₁', hf₁, hag₁⟩ := hloc θ₁ hT₁ _ ζ₁ hη₁'
  obtain ⟨η₂', ζ₂', hf₂, hag₂⟩ := hloc θ₂ hT₂ _ ζ₂ hη₂'
  -- Proposition 7.4 for the two flow lines of `X`
  obtain ⟨hA₁, hA₂⟩ := Sec7.prop74_angles hκ hκ4 hR hleft hright hT₁ hT₂
  have hord := h74 κ hκ hκ4 _ _ θ₁ θ₂ hθ hA₁ hA₂ Q X hX η₁' η₂' ζ₁' ζ₂' hf₁ hf₂
  refine hPQ.ae_le ?_
  filter_upwards [hord, hag₁, hag₂] with ω hω g₁ g₂ hζ₁ hζ₂
  obtain ⟨a₀, ha₀, ha₀ζ, ha₀ζ', ha₀e⟩ := g₁ hζ₁
  obtain ⟨c₀, hc₀, hc₀ζ, hc₀ζ', hc₀e⟩ := g₂ hζ₂
  refine ⟨a₀, c₀, ha₀, ha₀ζ, hc₀, hc₀ζ, HasOrderedProperCompletions.of_sub_real x ?_⟩
  exact Sec7.HasOrderedProperCompletions.congr_prefix (fun t ht => (ha₀e t ht).symm)
    (fun t ht => (hc₀e t ht).symm) (hω a₀ c₀ ha₀ζ' hc₀ζ')

end Supp9

namespace Supp9D

/-- **Theorem W5** (Theorem 1.5's interface 3) from G12 (source form), W0b, Lemma 7.7, the two retained-pair carriers,
**Proposition 7.4's ordering clause** and **the germ form of Aux. lemma 97's per-angle identification** (which give the
common-seed comparison, `Supp9.w5CommonSeedStatement_of_germIdent`). -/
theorem w5Statement_of_germIdent (hG12 : Supp7.G12EvolStatement.{u}) (hW0b : Supp9.W0bStatement.{u})
    (h77 : Supp10.Lemma77Statement.{0}) (hJ : JointRetainedPairStatement.{u})
    (hL : RetainedLocalCompletionStatement.{u}) (h74 : Sec7.Prop74OrderStatement.{u})
    (hg : Sec7.Aux97GermIdentStatement.{u}) : Theorem15.W5Statement.{u} :=
  w5Statement_of_g12Evol hG12 hW0b h77 hJ hL (Supp9.w5CommonSeedStatement_of_germIdent h74 hg)

end Supp9D

end InteractingSLE
