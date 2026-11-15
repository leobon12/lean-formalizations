/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripSysField
import InteractingSLE.Spec.Supplement.GW1

/-!
# Lemma GW0: almost-sure absence of a threshold and admissibility

Packet PROVE-T14-GW. Lemma GW0 (`source/spec/p577-624.md` L922–L928, p. 617):

> "For a finite-force word with its indicated integrated continuation rule, the continuation threshold is almost
> surely not hit if and only if every side cumulative group is greater than `−2`. An inadmissible seed gives zero
> available lifetime. If both initial seed groups are admissible, any first inadmissible separated group is reached at
> a finite continuation threshold with positive probability."

What is proved here, on the frozen `IsIntegratedSLEEvolution` (lifetime `ζ` = the continuation threshold):

* **the seed** (`IsIntegratedSLEPath.lifetime_eq_zero_iff`): the lifetime is `0` exactly when the seed satisfies the
  threshold condition ("An inadmissible seed gives zero available lifetime", and the maximal-lifetime converse);
* **the backward implication** (`ae_lifetime_eq_top_of_neg_two_lt`): if every group-end partial sum on both sides
  exceeds `−2`, the lifetime is almost surely infinite (the source: "Conversely, if every cumulative exceeds `−2`, the
  integrated finite-force system has no continuation threshold, and the complete nonexplosion theorem gives its infinite
  available lifetime"; Aux. lemma 6's argument, landed);
* **the equivalence** (`ae_lifetime_eq_top_iff`) from the forward implication, which is the named input
  `GW0ForwardStatement` (its proof is "the bounded-reference part of BR3": a target change to the first bad mark, LP11's
  complete transient path, GB5 and Aux. 108's finite-energy cutoff — not formalized);
* **the use in Theorem 1.4** (`counterflow_admissible`): in the setting of Theorem 1.4 (a centred counterflow with
  almost surely infinite lifetime), every side partial sum of the counterflow word is `> −2`, which is the
  admissibility hypothesis of GB6 (`Supp8.GB6.GB6FirstContactStatement`). The flow-line word has strictly ordered
  marks, so every index is a group end (`flowLineXL_lt`, `flowLineXR_lt`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW0

/-! ### The seed -/

/-- **The lifetime is zero exactly at an inadmissible seed** (GW0: "An inadmissible seed gives zero available
lifetime"; the maximal lifetime gives the converse). -/
theorem lifetime_eq_zero_iff {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) :
    ζ = 0 ↔ ForceWord.ThresholdCondition ρL ρR 0 xL xR := by
  refine ⟨h.isForcePath.threshold_of_eq_zero, fun hthr => ?_⟩
  by_contra hne
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ := by rw [ENNReal.coe_zero]; exact pos_iff_ne_zero.2 hne
  obtain ⟨hw0, hvL0, hvR0, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnot, -, -⟩ := h
  have e1 : (fun i => vL i 0) = xL := funext hvL0
  have e2 : (fun i => vR i 0) = xR := funext hvR0
  exact hnot 0 h0 (by rw [hw0, e1, e2]; exact hthr)

/-! ### The backward implication -/

/-- A finite family of reals `> −2` has a common lower bound `> −2`. -/
theorem exists_neg_two_lt_le {n : ℕ} (s : Fin n → ℝ) (p : Fin n → Prop) (h : ∀ j, p j → -2 < s j) :
    ∃ c : ℝ, -2 < c ∧ ∀ j, p j → c ≤ s j := by
  classical
  by_cases hne : (Finset.univ.filter p).Nonempty
  · set m := ((Finset.univ.filter p).image s).min' (hne.image s) with hm
    obtain ⟨j₀, hj₀, hj₀m⟩ := Finset.mem_image.1 (((Finset.univ.filter p).image s).min'_mem (hne.image s))
    refine ⟨m, ?_, fun j hj => ?_⟩
    · rw [hm, ← hj₀m]; exact h j₀ (Finset.mem_filter.1 hj₀).2
    · exact Finset.min'_le _ _ (Finset.mem_image.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩, rfl⟩)
  · refine ⟨-1, by norm_num, fun j hj => absurd ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩⟩ hne⟩

/-- The group-end admissibility of the left side of a word (`x_j` strictly beyond every later mark). -/
def LeftGroupEndsAdmissible {nL : ℕ} (xL ρL : Fin nL → ℝ) : Prop :=
  ∀ j : Fin nL, (∀ i, j < i → xL i < xL j) → -2 < ∑ i ∈ univ.filter (fun i => i ≤ j), ρL i

/-- The group-end admissibility of the right side of a word. -/
def RightGroupEndsAdmissible {nR : ℕ} (xR ρR : Fin nR → ℝ) : Prop :=
  ∀ j : Fin nR, (∀ i, j < i → xR j < xR i) → -2 < ∑ i ∈ univ.filter (fun i => i ≤ j), ρR i

/-- **GW0, backward implication**: if every group-end partial sum on both sides exceeds `−2`, the lifetime is
almost surely infinite. -/
theorem ae_lifetime_eq_top_of_neg_two_lt {k : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hword : IsOrderedForceWord xL xR)
    (hL : LeftGroupEndsAdmissible xL ρL) (hR : RightGroupEndsAdmissible xR ρR)
    (h : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) : ∀ᵐ ω ∂P, ζ ω = ⊤ := by
  obtain ⟨cL, hcL, hcL'⟩ := exists_neg_two_lt_le (fun j => ∑ i ∈ univ.filter (fun i => i ≤ j), ρL i)
    (fun j => ∀ i, j < i → (-xL) j < (-xL) i) fun j hj => hL j fun i hi => by
      have := hj i hi; simp only [Pi.neg_apply] at this; linarith
  obtain ⟨cR, hcR, hcR'⟩ := exists_neg_two_lt_le (fun j => ∑ i ∈ univ.filter (fun i => i ≤ j), ρR i)
    (fun j => ∀ i, j < i → xR j < xR i) hR
  refine Sec7.StripSysField.ae_lifetime_eq_top_of_groupEndSums (c := min cL cR) (lt_min hcL hcR) hword
    (fun j hj => (min_le_left _ _).trans (hcL' j hj)) (fun j hj => (min_le_right _ _).trans (hcR' j hj)) h

/-! ### The forward implication (named input) and the equivalence -/

/-- **Named input: Lemma GW0, forward implication** (p. 617; proof: "the bounded-reference part of BR3, before its
final contradiction with an almost-sure boundary hit": a first bad group is reached at a finite continuation
threshold with positive probability): for `k > 4` and an ordered finite force word, if an integrated `SLE_k(ρ)`
evolution has almost surely infinite lifetime, then every side group-end partial sum exceeds `−2`. -/
def GW0ForwardStatement : Prop :=
  ∀ (k : ℝ), 4 < k → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ → (∀ᵐ ω ∂P, ζ ω = ⊤) →
        LeftGroupEndsAdmissible xL ρL ∧ RightGroupEndsAdmissible xR ρR

/-- **Lemma GW0** (the equivalence, from its forward implication): for `k > 4` and an ordered finite force word, the
lifetime of an integrated `SLE_k(ρ)` evolution is almost surely infinite if and only if every side group-end partial
sum exceeds `−2`. -/
theorem ae_lifetime_eq_top_iff (hGW0 : GW0ForwardStatement.{u}) {k : ℝ} (hk : 4 < k) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hword : IsOrderedForceWord xL xR) (h : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    (∀ᵐ ω ∂P, ζ ω = ⊤) ↔ LeftGroupEndsAdmissible xL ρL ∧ RightGroupEndsAdmissible xR ρR :=
  ⟨hGW0 k hk xL xR ρL ρR hword P 𝓕 W VL VR B ζ h, fun ⟨hL, hR⟩ =>
    ae_lifetime_eq_top_of_neg_two_lt hword hL hR h⟩

/-! ### The counterflow word of Theorem 1.4 -/

/-- The left marks of a flow-line word are strictly decreasing. -/
theorem flowLineXL_lt (b : ℝ → ℝ) (jumps : Finset ℝ) (x : ℝ) {i j : Fin (flowLineNL b jumps x)} (hij : i < j) :
    flowLineXL b jumps x j < flowLineXL b jumps x i := by
  set SL := (PiecewiseConstantBoundaryData.jumpSet b jumps).filter (· < x) with hSL
  have hL : ∀ k, SL.orderEmbOfFin rfl k - x < 0 := fun k =>
    sub_neg.2 (Finset.mem_filter.1 (SL.orderEmbOfFin_mem rfl k)).2
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
  · exact absurd hij (lt_irrefl _)
  · exact hL _
  · exact absurd hij (not_lt.2 (Fin.zero_le _))
  · show SL.orderEmbOfFin rfl (Fin.rev j') - x < SL.orderEmbOfFin rfl (Fin.rev i') - x
    exact sub_lt_sub_right ((SL.orderEmbOfFin rfl).strictMono (Fin.rev_lt_rev.2 (Fin.succ_lt_succ_iff.1 hij))) x

/-- The right marks of a flow-line word are strictly increasing. -/
theorem flowLineXR_lt (b : ℝ → ℝ) (jumps : Finset ℝ) (x : ℝ) {i j : Fin (flowLineNR b jumps x)} (hij : i < j) :
    flowLineXR b jumps x i < flowLineXR b jumps x j := by
  set SR := (PiecewiseConstantBoundaryData.jumpSet b jumps).filter (x < ·) with hSR
  have hR : ∀ k, 0 < SR.orderEmbOfFin rfl k - x := fun k =>
    sub_pos.2 (Finset.mem_filter.1 (SR.orderEmbOfFin_mem rfl k)).2
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
  · exact absurd hij (lt_irrefl _)
  · exact hR _
  · exact absurd hij (not_lt.2 (Fin.zero_le _))
  · show SR.orderEmbOfFin rfl i' - x < SR.orderEmbOfFin rfl j' - x
    exact sub_lt_sub_right ((SR.orderEmbOfFin rfl).strictMono (Fin.succ_lt_succ_iff.1 hij)) x

/-- **The counterflow word is admissible** (GW0 applied to the counterflow, the hypothesis of GB6: "suppose the
original counterflow … has a finite boundary force word with every side partial sum strictly greater than `−2`"): for
`κ ∈ (0, 4)`, if `W` drives the angle-`0` flow line at parameter `16/κ` of a field with piecewise-constant data `b'`
(the frozen counterflow witness) with almost surely infinite lifetime, then every side partial sum of its word exceeds
`−2`, in the form of `Supp8.GB6.GB6FirstContactStatement`. -/
theorem counterflow_admissible (hGW0 : GW0ForwardStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b' : ℝ → ℝ} {J' : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    (∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) ∧
    (∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l) := by
  obtain ⟨_, 𝓕, VL, VR, B, -, hC⟩ := hcf
  have hk : 4 < 16 / κ := by rw [lt_div_iff₀ hκ]; linarith
  obtain ⟨hL, hR⟩ := hGW0 (16 / κ) hk _ _ _ _ (Theorem15.isOrderedForceWord_flowLine b' J' 0) P 𝓕 W VL VR B ζ hC.1 hζ
  exact ⟨fun i => hL i fun j hij => flowLineXL_lt b' J' 0 hij,
    fun i => hR i fun j hij => flowLineXR_lt b' J' 0 hij⟩

end GW0

end Theorem14

end InteractingSLE
