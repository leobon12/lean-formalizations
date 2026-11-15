/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.W5CommonSeedShift
import InteractingSLE.Spec.Supplement.G12Statement
import InteractingSLE.Spec.Sec2.AssemblyTheorem
import InteractingSLE.Spec.Sec7.Aux97
import InteractingSLE.Spec.Supplement.S9EAssembly

/-!
# Theorem W5's common-seed comparison from Aux. lemma 97

Packet PROVE-AUX97. Source: the proof of Theorem W5, "Proof: initial order and the first possible loss"
(`source/spec/p529-576.md` L133, p. 534): "For a common seed, use the joint local comparison in Aux. lemma 97 with the
two-height field matching the two original seed heights. Proposition 7.4 supplies complete proper ordered reference
paths. One common Cameron–Martin density and the determining graphs, as in G1, transfer the entire pair stopped in a
small seed neighborhood. Hence the two original stopped prefixes have actual ordered proper completions. Choose
`a₀ ∈ (0, A)` so small that the first prefix through `a₀` is within this comparison neighborhood."

**`Supp9.w5CommonSeedStatement_of_aux97`**: `Sec7.Aux97Statement → Supp9.W5CommonSeedStatement`. The Cameron–Martin
transfer and Proposition 7.4 quoted above are the proof of Aux. lemma 97 itself (p. 327); what W5 adds, and what is
proved here, is:

1. **recentering** at the common seed `x` (`IsFlowLine.recenter`, `IsGFFWithBoundaryData.recenter`): the two flow
   lines minus `x` are flow lines from `0` of `h(· + x)`, whose data `b(· + x)` is piecewise constant;
2. **the seed neighbourhood**: a radius `R > 0` with no jump candidate of `b(· + x)` in `(−R, 0) ∪ (0, R)`, so the
   data are the two original seed heights there (`Supp7.exists_pos_forall_notMem`,
   `Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant`); the comparison radius is `r = R/2`;
3. **inadmissible seeds**: if a seed group of either flow line is at the continuation threshold, its lifetime is `0`
   almost surely (`IsIntegratedSLEEvolution.ae_lifetime_eq_zero_of_threshold`) and W5's assertion is vacuous;
4. **positive prefixes inside the comparison neighbourhood**: on `{0 < ζᵢ}` each recentered trace starts at `0` and is
   continuous there, so it leaves `B̄(0, r)` only after a positive time (`Sec7.ballExit_pos`); any positive
   `a₀ < min(exit, ζ₁)`, `c₀ < min(exit, ζ₂)` work;
5. **translating back** the ordered proper completions (`HasOrderedProperCompletions.of_sub_real`).

`Supp9D.w5Statement_of_aux97`: Theorem W5 (`Theorem15.W5Statement`) with the input `W5CommonSeedStatement` replaced by
the source statement `Sec7.Aux97Statement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp9

/-- **Theorem W5's common-seed comparison from Aux. lemma 97** (p. 534): Aux. lemma 97 (stated for flow lines from `0`)
implies `W5CommonSeedStatement` (two flow lines from a common real seed `x` at angles `θ₁ < θ₂` have, almost surely
when both lifetimes are positive, positive prefixes strictly before the lifetimes with ordered proper completions). -/
theorem w5CommonSeedStatement_of_aux97 (h97 : Sec7.Aux97Statement.{u}) : W5CommonSeedStatement.{u} := by
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
  have key := h97 κ hκ hκ4 (fun y => b (y + x)) (J.image (· - x)) hb₀ R (b (-R / 2 + x)) (b (R / 2 + x)) hR
    hleft hright θ₁ θ₂ hθ hT₁ hT₂ (R / 2) (half_pos hR) (half_lt_self hR) P _ hh₀ _ _ ζ₁ ζ₂ hη₁' hη₂'
  -- the recentered traces
  obtain ⟨_h₁, _𝓕₁, W₁, _VL₁, _VR₁, _B₁, _htr₁, _hcpl₁, htrace₁⟩ := hη₁
  obtain ⟨_h₂, _𝓕₂, W₂, _VL₂, _VR₂, _B₂, _htr₂, _hcpl₂, htrace₂⟩ := hη₂
  filter_upwards [key, htrace₁, htrace₂] with ω hk ht₁ ht₂ hζ₁ hζ₂
  have he₁ : 0 < Sec7.ballExit (R / 2) (fun t => η₁ ω t - x) :=
    Sec7.ballExit_pos (half_pos hR) ht₁.1 hζ₁ ht₁.2.1
  have he₂ : 0 < Sec7.ballExit (R / 2) (fun t => η₂ ω t - x) :=
    Sec7.ballExit_pos (half_pos hR) ht₂.1 hζ₂ ht₂.2.1
  obtain ⟨a₀, ha₀, ha₀'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (lt_min he₁ hζ₁)
  obtain ⟨c₀, hc₀, hc₀'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (lt_min he₂ hζ₂)
  refine ⟨a₀, c₀, ENNReal.coe_pos.1 ha₀, lt_of_lt_of_le ha₀' (min_le_right _ _), ENNReal.coe_pos.1 hc₀,
    lt_of_lt_of_le hc₀' (min_le_right _ _), ?_⟩
  exact HasOrderedProperCompletions.of_sub_real x (hk a₀ c₀ (le_of_lt (lt_of_lt_of_le ha₀' (min_le_left _ _)))
    (lt_of_lt_of_le ha₀' (min_le_right _ _)) (le_of_lt (lt_of_lt_of_le hc₀' (min_le_left _ _)))
    (lt_of_lt_of_le hc₀' (min_le_right _ _)))

end Supp9

namespace Supp9D

/-- **Theorem W5** (Theorem 1.5's interface 3) from G12 (source form), W0b, Lemma 7.7, the two retained-pair carriers
and **Aux. lemma 97** (which gives the common-seed comparison, `Supp9.w5CommonSeedStatement_of_aux97`). -/
theorem w5Statement_of_aux97 (hG12 : Supp7.G12EvolStatement.{u}) (hW0b : Supp9.W0bStatement.{u})
    (h77 : Supp10.Lemma77Statement.{0}) (hJ : JointRetainedPairStatement.{u})
    (hL : RetainedLocalCompletionStatement.{u}) (h97 : Sec7.Aux97Statement.{u}) :
    Theorem15.W5Statement.{u} :=
  w5Statement_of_g12Evol hG12 hW0b h77 hJ hL (Supp9.w5CommonSeedStatement_of_aux97 h97)

end Supp9D

end InteractingSLE
