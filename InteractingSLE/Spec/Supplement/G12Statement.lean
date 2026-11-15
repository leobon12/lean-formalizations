/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9Propagation
import InteractingSLE.Spec.Sec4.Prob41Flow
import InteractingSLE.Spec.Theorem15Inputs

/-!
# Lemma G12 in the source's form: integrated evolutions, and the flow-line form from it

Packet PROVE-W5-REST2. Specification supplement §7.9, Lemma G12 (p. 504, `source/spec/p481-528.md` L574–L599):

> Consider any original finite-force `SLE_κ` path, continued only through its original lifetime and with its
> continuous finite terminal value included. Let `x_j > 0` be a distinct nonseed original right mark, after
> amalgamating coincident original marks, and let `S_j = Σ_{k ≤ j} ρ_{k,R}` include the right seed group when
> present. If `S_j > d_*`, the path does not visit `x_j`. The reflected assertion holds for a left mark.

W0a's proof (p. 528) applies it to a point which need not be a mark: "If a seed is not already a boundary jump for
the other flow, retain it as a passive zero-weight mark; this does not change the driving law or the displayed
cumulative weight." `G12EvolStatement` is therefore stated for every real point `y ≠ 0` (a mark, or a passive point
whose cumulative weight is that of the marks before it), on any integrated evolution of an ordered force word:

* `G12EvolStatement`: the source statement (both sides);
* `rightLim_sub_rightLim`, `leftLim_sub_leftLim`: telescoping of the one-sided limits of piecewise-constant data
  over the jump candidates between two points;
* `sum_filter_flowLineXR_le`, `sum_filter_flowLineXL_ge`: the cumulative weight of the flow-line word (any seed
  `x`, any angle `θ`) up to and including a point `y` is the conversion of the outward height `b(y^±) + θχ`;
* `g12FlowStatement_of_evol`: **`G12FlowStatement`** (the form consumed by W0a, `S9Propagation.lean`) from
  `G12EvolStatement`; `w0aStatement_of_g12Evol`: Corollary W0a from it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE

namespace Supp7

open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)
open Sec4

/-! ### The statement -/

/-- **Lemma G12 for integrated evolutions** (supplement §7.9, p. 504; with W0a's passive marks, p. 528). For
`0 < κ < 4`, an integrated `SLE_κ(ρ)` evolution of an ordered force word and a continuous generating trace `η` on
`[0, ζ]` (the terminal value included): a real point `y > 0` whose right cumulative weight
`Σ_{x_{i,R} ≤ y} ρ_{i,R}` (the right seed group included) exceeds `d_* = κ/2 − 4` is almost surely never visited;
reflected, a point `y < 0` whose left cumulative weight `Σ_{x_{i,L} ≥ y} ρ_{i,L}` exceeds `d_*` is almost surely never
visited. -/
def G12EvolStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
    ∀ η : Ω → ℝ≥0 → ℂ, (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) →
    ∀ y : ℝ,
      (0 < y → κ / 2 - 4 < ∑ i ∈ univ.filter (fun i => xR i ≤ y), ρR i →
        ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y) ∧
      (y < 0 → κ / 2 - 4 < ∑ i ∈ univ.filter (fun i => y ≤ xL i), ρL i →
        ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y)

/-! ### Telescoping of the one-sided limits -/

variable {b : ℝ → ℝ} {J : Finset ℝ}

/-- Near every point the data is constant on each side, off the jump candidates. -/
theorem exists_pos_forall_notMem (J : Finset ℝ) (x : ℝ) :
    ∃ δ > 0, ∀ z ∈ J, z ∉ Ioo x (x + δ) ∧ z ∉ Ioo (x - δ) x := by
  set S : Finset ℝ := insert 1 ((J.filter (· ≠ x)).image fun z => |z - x|) with hS
  have hpos : ∀ s ∈ S, 0 < s := by
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact one_pos
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hs
      exact abs_pos.2 (sub_ne_zero.2 (Finset.mem_filter.1 hz).2)
  refine ⟨S.min' (Finset.insert_nonempty _ _), hpos _ (S.min'_mem _), fun z hz => ?_⟩
  by_cases hzx : z = x
  · subst hzx
    exact ⟨fun h => lt_irrefl _ h.1, fun h => lt_irrefl _ h.2⟩
  have hle : S.min' (Finset.insert_nonempty _ _) ≤ |z - x| :=
    S.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨z, Finset.mem_filter.2 ⟨hz, hzx⟩, rfl⟩))
  constructor
  · rintro ⟨h1, h2⟩
    rw [abs_of_pos (sub_pos.2 h1)] at hle
    linarith
  · rintro ⟨h1, h2⟩
    rw [abs_of_neg (sub_neg.2 h2)] at hle
    linarith

/-- The right limit is the value just to the right, the left limit the value just to the left. -/
theorem exists_pos_eq_lims (hb : IsPiecewiseConstantBoundaryData b J) (x : ℝ) :
    ∃ δ > 0, ∀ ε, 0 < ε → ε < δ → x + ε ∉ J ∧ x - ε ∉ J ∧ b (x + ε) = rightLim b x ∧
      b (x - ε) = leftLim b x := by
  obtain ⟨δ, hδ, hJ⟩ := exists_pos_forall_notMem J x
  refine ⟨δ, hδ, fun ε hε hεδ => ?_⟩
  have h1 : x + ε ∈ Ioo x (x + δ) := ⟨by linarith, by linarith⟩
  have h2 : x - ε ∈ Ioo (x - δ) x := ⟨by linarith, by linarith⟩
  refine ⟨fun h => (hJ _ h).1 h1, fun h => (hJ _ h).2 h2, ?_, ?_⟩
  · exact (rightLim_eq_of_forall (by linarith : x < x + δ) fun t ht =>
      eq_of_mem_Ioo_of_isPiecewiseConstant hb (fun z hz => (hJ z hz).1) h1 ht).symm
  · exact (leftLim_eq_of_forall (by linarith : x - δ < x) fun t ht =>
      eq_of_mem_Ioo_of_isPiecewiseConstant hb (fun z hz => (hJ z hz).2) h2 ht).symm

/-- **Right telescoping.** For `x < y`, `b(y⁺) − b(x⁺) = Σ_{z ∈ J ∩ (x, y]} (b(z⁺) − b(z⁻))`. -/
theorem rightLim_sub_rightLim (hb : IsPiecewiseConstantBoundaryData b J) {x y : ℝ} (hxy : x < y) :
    rightLim b y - rightLim b x =
      ∑ z ∈ J.filter (fun z => x < z ∧ z ≤ y), (rightLim b z - leftLim b z) := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := exists_pos_eq_lims hb x
  obtain ⟨δ₂, hδ₂, h₂⟩ := exists_pos_eq_lims hb y
  set ε := min (min δ₁ δ₂) (y - x) / 2 with hε
  have hm : 0 < min (min δ₁ δ₂) (y - x) := lt_min (lt_min hδ₁ hδ₂) (sub_pos.2 hxy)
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hε1 : ε < δ₁ := by
    rw [hε]; linarith [min_le_left (min δ₁ δ₂) (y - x), min_le_left δ₁ δ₂]
  have hε2 : ε < δ₂ := by
    rw [hε]; linarith [min_le_left (min δ₁ δ₂) (y - x), min_le_right δ₁ δ₂]
  have hεxy : ε < y - x := by rw [hε]; linarith [min_le_right (min δ₁ δ₂) (y - x)]
  obtain ⟨hxJ, -, hxr, -⟩ := h₁ ε hε0 hε1
  obtain ⟨hyJ, -, hyr, -⟩ := h₂ ε hε0 hε2
  have h := sub_eq_sum_of_isPiecewiseConstant hb _ (by linarith : x + ε < y + ε) hxJ hyJ rfl
  rw [← hxr, ← hyr, h]
  refine Finset.sum_congr (Finset.filter_congr fun z hz => ?_) fun _ _ => rfl
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by linarith, ?_⟩
    by_contra hzy
    rw [not_le] at hzy
    -- `z ∈ (y, y + ε)` contradicts the choice of `ε`
    have : y + (z - y) ∉ J := (h₂ (z - y) (by linarith) (by linarith)).1
    rw [add_sub_cancel] at this
    exact this hz
  · rintro ⟨h1, h2⟩
    refine ⟨?_, by linarith⟩
    by_contra hzx
    rw [not_lt] at hzx
    have : x + (z - x) ∉ J := (h₁ (z - x) (by linarith) (by linarith)).1
    rw [add_sub_cancel] at this
    exact this hz

/-- **Left telescoping.** For `y < x`, `b(x⁻) − b(y⁻) = Σ_{z ∈ J ∩ [y, x)} (b(z⁺) − b(z⁻))`. -/
theorem leftLim_sub_leftLim (hb : IsPiecewiseConstantBoundaryData b J) {x y : ℝ} (hyx : y < x) :
    leftLim b x - leftLim b y =
      ∑ z ∈ J.filter (fun z => y ≤ z ∧ z < x), (rightLim b z - leftLim b z) := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := exists_pos_eq_lims hb x
  obtain ⟨δ₂, hδ₂, h₂⟩ := exists_pos_eq_lims hb y
  set ε := min (min δ₁ δ₂) (x - y) / 2 with hε
  have hm : 0 < min (min δ₁ δ₂) (x - y) := lt_min (lt_min hδ₁ hδ₂) (sub_pos.2 hyx)
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hε1 : ε < δ₁ := by
    rw [hε]; linarith [min_le_left (min δ₁ δ₂) (x - y), min_le_left δ₁ δ₂]
  have hε2 : ε < δ₂ := by
    rw [hε]; linarith [min_le_left (min δ₁ δ₂) (x - y), min_le_right δ₁ δ₂]
  have hεxy : ε < x - y := by rw [hε]; linarith [min_le_right (min δ₁ δ₂) (x - y)]
  obtain ⟨-, hxJ, -, hxl⟩ := h₁ ε hε0 hε1
  obtain ⟨-, hyJ, -, hyl⟩ := h₂ ε hε0 hε2
  have h := sub_eq_sum_of_isPiecewiseConstant hb _ (by linarith : y - ε < x - ε) hyJ hxJ rfl
  rw [← hxl, ← hyl, h]
  refine Finset.sum_congr (Finset.filter_congr fun z hz => ?_) fun _ _ => rfl
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, by linarith⟩
    by_contra hzy
    rw [not_le] at hzy
    have : y - (y - z) ∉ J := (h₂ (y - z) (by linarith) (by linarith)).2.1
    rw [sub_sub_cancel] at this
    exact this hz
  · rintro ⟨h1, h2⟩
    refine ⟨by linarith, ?_⟩
    by_contra hzx
    rw [not_lt] at hzx
    have : x - (x - z) ∉ J := (h₁ (x - z) (by linarith) (by linarith)).2.1
    rw [sub_sub_cancel] at this
    exact this hz

/-! ### The cumulative weights of the flow-line word -/

/-- Splitting off the seed mark of a `Fin.cons` word (left prefixes, non-strict). -/
theorem sum_filter_ge_cons {n : ℕ} (p₀ a : ℝ) (p f : Fin n → ℝ) (x : ℝ) :
    ∑ i ∈ univ.filter (fun i => x ≤ (Fin.cons p₀ p : Fin (n + 1) → ℝ) i),
        (Fin.cons a f : Fin (n + 1) → ℝ) i =
      (if x ≤ p₀ then a else 0) + ∑ j ∈ univ.filter (fun j => x ≤ p j), f j := by
  rw [Finset.sum_filter, Fin.sum_univ_succ, Finset.sum_filter]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- **The right cumulative weight of the flow-line word** from any seed `x` at any angle `θ`, up to and including
the point `y > x`, is `(b(y⁺) + θχ)/λ − 1`. -/
theorem sum_filter_flowLineXR_le {κ : ℝ} (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    {x y : ℝ} (θ : ℝ) (hxy : x < y) :
    ∑ i ∈ univ.filter (fun i => flowLineXR b J x i ≤ y - x), flowLineRhoR κ b J x θ i =
      cumWeightRight κ (rightLim b y + θ * chiC κ) := by
  have hΛ : sleLambda κ ≠ 0 := (sleLambda_pos hκ).ne'
  unfold flowLineXR flowLineRhoR flowLineNR
  rw [sum_filter_le_cons]
  simp only [sub_nonneg.2 hxy.le, ↓reduceIte]
  have h := sum_filter_orderEmbOfFin ((jumpSet b J).filter (x < ·)) (fun z => z - x ≤ y - x)
    (fun z => (rightLim b z - leftLim b z) / sleLambda κ)
  rw [h, ← Finset.sum_div, Finset.filter_filter, sum_jumpSet_filter]
  have hf : J.filter (fun z => x < z ∧ z - x ≤ y - x) = J.filter (fun z => x < z ∧ z ≤ y) :=
    Finset.filter_congr fun z _ => and_congr_right fun _ => sub_le_sub_iff_right x
  rw [hf, ← rightLim_sub_rightLim hb hxy]
  unfold cumWeightRight
  field_simp
  ring

/-- **The left cumulative weight of the flow-line word** from any seed `x` at any angle `θ`, down to and including
the point `y < x`, is `−(b(y⁻) + θχ)/λ − 1`. -/
theorem sum_filter_flowLineXL_ge {κ : ℝ} (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    {x y : ℝ} (θ : ℝ) (hyx : y < x) :
    ∑ i ∈ univ.filter (fun i => y - x ≤ flowLineXL b J x i), flowLineRhoL κ b J x θ i =
      cumWeightLeft κ (leftLim b y + θ * chiC κ) := by
  have hΛ : sleLambda κ ≠ 0 := (sleLambda_pos hκ).ne'
  unfold flowLineXL flowLineRhoL flowLineNL
  rw [sum_filter_ge_cons]
  simp only [sub_nonpos.2 hyx.le, ↓reduceIte]
  have h := sum_filter_orderEmbOfFin_rev ((jumpSet b J).filter (· < x)) (fun z => y - x ≤ z - x)
    (fun z => (rightLim b z - leftLim b z) / sleLambda κ)
  rw [h, ← Finset.sum_div, Finset.filter_filter, sum_jumpSet_filter]
  have hf : J.filter (fun z => z < x ∧ y - x ≤ z - x) = J.filter (fun z => y ≤ z ∧ z < x) :=
    Finset.filter_congr fun z _ => by rw [sub_le_sub_iff_right, and_comm]
  rw [hf, ← leftLim_sub_leftLim hb hyx]
  unfold cumWeightLeft
  field_simp
  ring

/-! ### The flow-line form -/

/-- **`G12FlowStatement` from the source form.** A flow line from `x` at angle `θ` is, after translating by `x`, the
generating trace of an integrated evolution of the flow-line word (frozen `IsFlowLine`); the cumulative weight of
that word up to `y − x` is the displayed `S` (`sum_filter_flowLineXR_le`, `sum_filter_flowLineXL_ge`). -/
theorem g12FlowStatement_of_evol (hG12 : G12EvolStatement.{u}) : Supp9.G12FlowStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x θ y Ω _ P _ h _ η ζ hη
  obtain ⟨_h', 𝓕, W, VL, VR, B, -, hcpl, htr⟩ := hη
  have hG := hG12 κ hκ hκ4 _ _ _ _ (Theorem15.isOrderedForceWord_flowLine b jumps x) P 𝓕 W VL VR B ζ
    hcpl.1 (fun ω t => η ω t - x) htr (y - x)
  have key : ∀ ω t, η ω t = y → η ω t - x = ((y - x : ℝ) : ℂ) := fun ω t he => by
    rw [he]; push_cast; ring
  refine ⟨fun hxy hS => ?_, fun hyx hS => ?_⟩
  · filter_upwards [hG.1 (sub_pos.2 hxy) (by rwa [sum_filter_flowLineXR_le hκ hb θ hxy])] with ω hω t ht he
    exact hω t ht (key ω t he)
  · filter_upwards [hG.2 (sub_neg.2 hyx) (by rwa [sum_filter_flowLineXL_ge hκ hb θ hyx])] with ω hω t ht he
    exact hω t ht (key ω t he)

/-- **Corollary W0a from the source form of G12** (`Supp9.w0aStatement_of_g12`, through the flow-line form). -/
theorem w0aStatement_of_g12Evol (hG12 : G12EvolStatement.{u}) : Supp9.W0aStatement.{u} :=
  Supp9.w0aStatement_of_g12 (g12FlowStatement_of_evol hG12)

end Supp7

end InteractingSLE
