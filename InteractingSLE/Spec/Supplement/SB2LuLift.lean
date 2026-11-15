/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LuAcc
import InteractingSLE.Spec.Supplement.SB2LqRange

/-!
# SB2(2)'s physical sets: the lift image of the actual walk

Packet PROVE-SB2-LIFTSET (target 2, the lift half). Let `β₀` be a proper parametrization of the actual lower walk
`B`, visiting `R` at `t_L`, and `γ` a lift curve of its tail (`IsTailLiftCurve`: `c⁻¹` has the boundary value
`β₀ (t_L + s)` at `γ s − m`). The relative walk's physical set should be `range γ` (`SB2LowerRelWalkRangeStatement`).
This file reads `range γ` piece by piece:

* **`liftImage β₀ t_L γ S`** `= γ '' {s | β₀ (t_L + s) ∈ S}`: the lift of the part of `S` on the tail.
  `range_eq_liftImage_range`, `liftImage_union`, `liftImage_biUnion`, `liftImage_mono`;
* **`liftImage_ofReal`** (connectors): the lift image of a real connector `a` is `ι '' (a ∩ Ici R)` ("Genuine real
  connectors outside the old real base are transported by positive reflection; [...] retain only its remaining
  part", supplement p. 631), given that the head of `β₀` has real points `≤ R`, its tail real points `≥ R`, and the
  lift curve reads the untouched ray through `ι` (`lift_eq_of_rayChartInj`, from **`RayChartInj`**, itself from
  the forward chart by `rayChartInj_of_continuousWithinAt`);
* **`liftImage_subset_of_head`**: a set on the head `β₀ '' [0, t_L]` lifts into `{γ 0}` (the erased initial
  portion: "the erased initial portion lies in `K_A`");
* **`LiftRel`** ((L4): the relative piece's physical points are the lift image of the actual piece's) and
  **`range_eq_of_decomp`**: if the two physical sets decompose into start parts, pieces paired by `LiftRel` and
  connectors (relative ones the `ι`-images of the actual ones), and the relative start part is the lift image of the
  actual one, then `range γ` is the relative physical set;
* **`liftImage_start_arc`**, **`liftImage_start_piece`**: the start parts in the two cases of the visit to `R`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw GW1W GW1Bookkeep
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-! ### The lift image -/

/-- **The lift image of a set `S`** along the tail of `β₀` after `t_L`: the points `γ s` of the lift curve at the
times `s` at which the tail `β₀ (t_L + s)` lies in `S`. -/
def liftImage (β₀ : ℝ≥0 → ℂ) (tL : ℝ≥0) (γ : ℝ≥0 → ℂ) (S : Set ℂ) : Set ℂ := γ '' {s | β₀ (tL + s) ∈ S}

variable {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- The lift image of a union. -/
theorem liftImage_union (S T : Set ℂ) : liftImage β₀ tL γ (S ∪ T) = liftImage β₀ tL γ S ∪ liftImage β₀ tL γ T := by
  unfold liftImage
  rw [← image_union]
  rfl

/-- The lift image of a union over a list. -/
theorem liftImage_biUnion {α : Type*} (l : List α) (f : α → Set ℂ) :
    liftImage β₀ tL γ (⋃ q ∈ l, f q) = ⋃ q ∈ l, liftImage β₀ tL γ (f q) := by
  unfold liftImage
  ext z
  simp only [mem_image, mem_iUnion, mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨s, ⟨q, hq, hs⟩, rfl⟩
    exact ⟨q, hq, s, hs, rfl⟩
  · rintro ⟨q, hq, s, hs, rfl⟩
    exact ⟨s, ⟨q, hq, hs⟩, rfl⟩

/-- The lift image is monotone. -/
theorem liftImage_mono {S T : Set ℂ} (h : S ⊆ T) : liftImage β₀ tL γ S ⊆ liftImage β₀ tL γ T :=
  image_mono fun _ hs => h hs

/-- The lift curve is the lift image of the range of `β₀`. -/
theorem range_eq_liftImage_range : range γ = liftImage β₀ tL γ (range β₀) := by
  unfold liftImage
  rw [show {s | β₀ (tL + s) ∈ range β₀} = univ from eq_univ_of_forall fun s => ⟨tL + s, rfl⟩, image_univ]

/-- Lift images of a family of pieces related by the lift relation. -/
theorem biUnion_eq_of_forall₂ {f₁ f₂ : Pc → Set ℂ} {Y₁ Y₂ : List Pc}
    (h : List.Forall₂ (fun q₁ q₂ => f₂ q₂ = liftImage β₀ tL γ (f₁ q₁)) Y₁ Y₂) :
    (⋃ q ∈ Y₂, f₂ q) = ⋃ q ∈ Y₁, liftImage β₀ tL γ (f₁ q) := by
  induction h with
  | nil => simp
  | cons hq _ ih =>
    simp only [List.mem_cons, iUnion_or, iUnion_union_distrib, iUnion_iUnion_eq_left]
    rw [ih, hq]

/-- **The prefix before the start contributes only the starting point**: if it lies on the head `β₀ '' [0, t_L]` of
the actual walk (and `β₀` is injective), its lift image is at most `{γ 0}`. -/
theorem liftImage_subset_of_head (hβ : Function.Injective β₀) {P : Set ℂ} (hP : P ⊆ β₀ '' Iic tL) :
    liftImage β₀ tL γ P ⊆ {γ 0} := by
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨t, ht, he⟩ := hP hs
  have h1 : t = tL + s := hβ he
  have hs0 : s = 0 := by
    have : tL + s ≤ tL := h1 ▸ ht
    exact le_antisymm (by simpa using this) zero_le
  rw [hs0]
  rfl


/-! ### Connectors and the untouched ray -/

variable {R : ℝ} {ι : ℝ → ℝ}

/-- The tail of an injective `β₀` revisits `β₀ t_L` only at `s = 0`. -/
theorem eq_zero_of_tail_eq (hβ : Function.Injective β₀) {s : ℝ≥0} (h : β₀ (tL + s) = β₀ tL) : s = 0 := by
  have := hβ h
  simpa using this

/-- **The lift image of a real connector** is the `ι`-image of its part right of `R`. Hypotheses: the head of `β₀`
(through its visit to `R` at `t_L`) has real points `≤ R`, its tail has real points `≥ R`, the lift curve reads the
untouched ray through `ι` (`γ s = ι x` when the tail is at `x > R`), and the points of the connector right of `R` are
points of `β₀`. -/
theorem liftImage_ofReal (hβ : Function.Injective β₀) (hβL : β₀ tL = R) (hγ0 : γ 0 = 0) (hι0 : ι R = 0)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) (htail : ∀ s, ∀ x : ℝ, β₀ (tL + s) = x → R ≤ x)
    (hray : ∀ s, ∀ x : ℝ, R < x → β₀ (tL + s) = x → γ s = ι x) {a : Set ℝ}
    (ha : ∀ x ∈ a, R ≤ x → (x : ℂ) ∈ range β₀) :
    liftImage β₀ tL γ (((↑) : ℝ → ℂ) '' a) = ((↑) : ℝ → ℂ) '' (ι '' (a ∩ Ici R)) := by
  ext z
  constructor
  · rintro ⟨s, ⟨x, hxa, hx⟩, rfl⟩
    have hRx : R ≤ x := htail s x hx.symm
    rcases eq_or_lt_of_le hRx with hxR | hxR
    · have hs : s = 0 := eq_zero_of_tail_eq hβ (by rw [← hx, hβL, hxR])
      subst hs
      exact ⟨ι x, ⟨x, ⟨hxa, hRx⟩, rfl⟩, by rw [hγ0, ← hxR, hι0, Complex.ofReal_zero]⟩
    · exact ⟨ι x, ⟨x, ⟨hxa, hRx⟩, rfl⟩, (hray s x hxR hx.symm).symm⟩
  · rintro ⟨_, ⟨x, ⟨hxa, hRx⟩, rfl⟩, rfl⟩
    have hRx : R ≤ x := hRx
    obtain ⟨t, ht⟩ := ha x hxa hRx
    have htL : tL ≤ t := by
      by_contra hlt
      push Not at hlt
      have hxR : x ≤ R := hhead t hlt.le x ht
      have hxR' : x = R := le_antisymm hxR hRx
      rw [hxR', ← hβL] at ht
      exact absurd (hβ ht) hlt.ne
    obtain ⟨s, rfl⟩ : ∃ s, t = tL + s := ⟨t - tL, (add_tsub_cancel_of_le htL).symm⟩
    refine ⟨s, ⟨x, hxa, ht.symm⟩, ?_⟩
    rcases eq_or_lt_of_le hRx with hxR | hxR
    · have hs : s = 0 := eq_zero_of_tail_eq hβ (by rw [ht, hβL, hxR])
      subst hs
      rw [hγ0, ← hxR, hι0, Complex.ofReal_zero]
    · exact hray s x hxR ht

/-- **The ray of the chart is injective through `ι`**: every point of `ℍ̄` at which `c⁻¹` has the boundary value
`x > R` is the real point `ι x − m`. -/
def RayChartInj (c : Chart) (R m : ℝ) (ι : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, R < x → ∀ w : ℂ, 0 ≤ w.im → Tendsto c.2.1 (𝓝[H] w) (𝓝 (x : ℂ)) → w = ((ι x - m : ℝ) : ℂ)

/-- **The lift curve reads the untouched ray through `ι`.** -/
theorem lift_eq_of_rayChartInj {c : Chart} {m : ℝ} (hγ : IsTailLiftCurve c R m β₀ tL γ)
    (hinj : RayChartInj c R m ι) : ∀ s, ∀ x : ℝ, R < x → β₀ (tL + s) = x → γ s = ι x := by
  intro s x hRx hx
  have hT := hγ.2.2.2 s
  rw [hx] at hT
  have hw : 0 ≤ (γ s - (m : ℂ)).im := by
    simpa using hγ.2.1.2.2.1 s
  have := hinj x hRx _ hw hT
  rw [Complex.ofReal_sub] at this
  simpa using this

/-- **`RayChartInj` from the forward chart** (`injAt_of_continuousWithinAt`): if `c⁻¹` maps `ℍ` into `ℍ` with left
inverse `c.1`, has a continuous extension `ĝ` to `ℍ̄` that is its boundary limit everywhere, and at each `x > R` the
forward chart is continuous within `ℍ` with value `ι x − m` and `ĝ (ι x − m) = x`. -/
theorem rayChartInj_of_continuousWithinAt {c : Chart} {m : ℝ} {ĝ : ℂ → ℂ} (hgH : MapsTo c.2.1 H H)
    (hfg : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hĝ : ContinuousOn ĝ Hbar) (hgg : EqOn ĝ c.2.1 H)
    (hlim : ∀ q ∈ Hbar, Tendsto c.2.1 (𝓝[H] q) (𝓝 (ĝ q)))
    (hf : ∀ x : ℝ, R < x → ContinuousWithinAt c.1 H x) (hfx : ∀ x : ℝ, R < x → c.1 x = ((ι x - m : ℝ) : ℂ))
    (hĝx : ∀ x : ℝ, R < x → ĝ ((ι x - m : ℝ) : ℂ) = x) : RayChartInj c R m ι := by
  intro x hRx w hw hT
  have hwH : w ∈ Hbar := hw
  have : (𝓝[H] w).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, show closure H = Hbar from Complex.closure_setOfPred_lt_im 0]
    exact hwH
  have hgw : ĝ w = x := tendsto_nhds_unique (hlim w hwH) hT
  exact injAt_of_continuousWithinAt hgH hfg hĝ hgg (by simp) (hĝx x hRx) (hf x hRx) (hfx x hRx) w hwH
    (by rw [hgw, hĝx x hRx])

/-! ### The range identity -/

/-- **The lift relation of two recorded pieces**: the relative piece's physical points are the lift image of the
actual piece's ((L4)). -/
def LiftRel (β₀ : ℝ≥0 → ℂ) (tL : ℝ≥0) (γ : ℝ≥0 → ℂ) (q₁ q₂ : Pc) : Prop :=
  q₂.1.tipSet q₂.2.1 q₂.2.2 = liftImage β₀ tL γ (q₁.1.tipSet q₁.2.1 q₁.2.2)

/-- **The range identity from a decomposition** (deterministic): if the actual physical set `P₁` (the range of `β₀`)
and the relative one `P₂` decompose into a start part, paired pieces and connectors, with the relative start part,
pieces and connectors the lift images of the actual ones, then the lift curve's range is `P₂`. -/
theorem range_eq_of_decomp {P₁ P₂ Q₁ Q₂ : Set ℂ} {X : List (Set ℝ)} {Y₁ Y₂ : List Pc} (hβr : range β₀ = P₁)
    (hP₁ : P₁ = Q₁ ∪ (⋃ q ∈ Y₁, q.1.tipSet q.2.1 q.2.2) ∪ ⋃ a ∈ X, ((↑) : ℝ → ℂ) '' a)
    (hP₂ : P₂ = Q₂ ∪ (⋃ q ∈ Y₂, q.1.tipSet q.2.1 q.2.2) ∪ ⋃ a ∈ X, ((↑) : ℝ → ℂ) '' (ι '' (a ∩ Ici R)))
    (hY : List.Forall₂ (LiftRel β₀ tL γ) Y₁ Y₂) (hQ : liftImage β₀ tL γ Q₁ = Q₂)
    (hX : ∀ a ∈ X, liftImage β₀ tL γ (((↑) : ℝ → ℂ) '' a) = ((↑) : ℝ → ℂ) '' (ι '' (a ∩ Ici R))) :
    range γ = P₂ := by
  rw [range_eq_liftImage_range (β₀ := β₀) (tL := tL), hβr, hP₁, liftImage_union, liftImage_union,
    liftImage_biUnion, liftImage_biUnion, hQ, hP₂, biUnion_eq_of_forall₂ hY]
  congr 1
  exact iUnion₂_congr fun a ha => hX a ha


/-! ### The start parts -/

/-- **The start part when `R` lies on an actual connector `a`**: the lift image of the actual prefix before the
connector (on the head) together with the connector is `{0}` with the `ι`-image of the connector right of `R`. -/
theorem liftImage_start_arc (hβ : Function.Injective β₀) (hβL : β₀ tL = R) (hγ0 : γ 0 = 0) (hι0 : ι R = 0)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) (htail : ∀ s, ∀ x : ℝ, β₀ (tL + s) = x → R ≤ x)
    (hray : ∀ s, ∀ x : ℝ, R < x → β₀ (tL + s) = x → γ s = ι x) {P₀ : Set ℂ} (hP₀ : P₀ ⊆ β₀ '' Iic tL)
    {a : Set ℝ} (hRa : R ∈ a) (ha : ∀ x ∈ a, R ≤ x → (x : ℂ) ∈ range β₀) :
    liftImage β₀ tL γ (P₀ ∪ ((↑) : ℝ → ℂ) '' a) = {0} ∪ ((↑) : ℝ → ℂ) '' (ι '' (a ∩ Ici R)) := by
  rw [liftImage_union, liftImage_ofReal hβ hβL hγ0 hι0 hhead htail hray ha]
  have h0 : (0 : ℂ) ∈ ((↑) : ℝ → ℂ) '' (ι '' (a ∩ Ici R)) :=
    ⟨ι R, ⟨R, ⟨hRa, mem_Ici.2 le_rfl⟩, rfl⟩, by rw [hι0, Complex.ofReal_zero]⟩
  have hP := liftImage_subset_of_head (γ := γ) hβ hP₀
  rw [hγ0] at hP
  refine Subset.antisymm (union_subset (hP.trans subset_union_left) subset_union_right)
    (union_subset ?_ subset_union_right)
  rw [singleton_subset_iff]
  exact Or.inr h0

/-- **The start part when `R` lies on an actual piece `T₁`**: if the relative first piece `T₂` is the lift image of
`T₁` and the actual prefix before the piece lies on the head, the lift image of the prefix with the piece is `{0}`
with `T₂`. -/
theorem liftImage_start_piece (hβ : Function.Injective β₀) (hγ0 : γ 0 = 0) {P₀ T₁ T₂ : Set ℂ}
    (hP₀ : P₀ ⊆ β₀ '' Iic tL) (hT : T₂ = liftImage β₀ tL γ T₁) (hR : β₀ tL ∈ P₀ ∪ T₁) :
    liftImage β₀ tL γ (P₀ ∪ T₁) = {0} ∪ T₂ := by
  have h0 : (0 : ℂ) ∈ liftImage β₀ tL γ (P₀ ∪ T₁) := ⟨0, by simpa using hR, hγ0⟩
  have hP := liftImage_subset_of_head (γ := γ) hβ hP₀
  rw [hγ0] at hP
  refine Subset.antisymm ?_ (union_subset (singleton_subset_iff.2 h0) ?_)
  · rw [liftImage_union, ← hT]
    exact union_subset (hP.trans subset_union_left) subset_union_right
  · rw [hT]
    exact liftImage_mono subset_union_right

end InteractingSLE.Theorem14.SB.Lk
