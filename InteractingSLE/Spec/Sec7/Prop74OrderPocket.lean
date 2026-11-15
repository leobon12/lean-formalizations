/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71Four
import InteractingSLE.Spec.Sec7.Prop74Order
import InteractingSLE.Spec.Supplement.S9BOrder

/-!
# Proposition 7.4's order: the reference from two middle curves in one pocket

Packet PROVE-PROP74. Source: p. 243 ("Applying the same component-pair construction simultaneously to finitely many
middle flow lines proves the following monotonicity statement"), §7.1 setup and Lemma 7.1 (pp. 221–225), Figure 7.1.

**The construction.** Given the data `(a, b)` of Proposition 7.4 and angles `θ₁ < θ₂` with its bounds, put
`α₂ = (a + λ)/χ` and `α₁ = −(λ + b)/χ`, so that `α₁ < θ₁ < θ₂ < α₂`. Take the four-curve space
(`Lemma71Four.IsFourCurveSpace`: a GFF with large data `(A, B)` and its flow lines `β = η_{α₂}`, `γ₂ = η_{θ₂}`,
`γ₁ = η_{θ₁}`, `α = η_{α₁}`, ordered by Proposition 5.5). In a pocket `C` between the outer curves with chart
`ψ : C → ℍ`, the pocket field `h_ψ = h ∘ ψ⁻¹ − χ arg (ψ⁻¹)′` has the data `λ − α₂χ = −a` on `ℝ₋` and `−λ − α₁χ = b` on
`ℝ₊` (Figure 7.1, right), and Lemma 7.1, applied to both middle curves with the same pocket and chart, says that the
mapped segments `ψ(γᵢ ∩ C̄)` are the angle-`θᵢ` flow lines of `h_ψ`, complete simple curves tending to `∞`. This is the
named input **`Lemma71TwoMiddleStatement`**, stated with the extended inverse chart `G = ψ⁻¹ : ℍ̄ → C̄` (Remark 6.14's
Jordan boundary homeomorphism) and with the mapped segments described by `G (range η'ᵢ) = range γᵢ ∩ G(ℍ̄)` (the visit
of `γᵢ` to the closed pocket, p. 224).

**The order step (proved here).** The order `γ₂ ≤ γ₁` passes to the mapped segments
(`range_subset_closedLeftSide_of_pocket`): a point `w` of `η'₂` on the open right side of `η'₁` is joined, inside that
side and inside `ℍ̄`, to a positive real point `x` (first exit from `ℍ`,
`Prop55Half.exists_ofReal_mem_closure_of_joinedIn`); `G` maps this connected set off the closed curve of `γ₁` (the
visit description and injectivity of `G`), so `G w` (a point of `γ₂`, on the left of `γ₁`) and `G x` (a point of the
right flank `α`) lie on the same side of `γ₁`; but no point of `α` is on the left side of `γ₁`
(`disjoint_range_leftSide`, the order `γ₁ ≤ α` seen from the right curve).

## Main results

* `pos_of_ofReal_mem_rightSide`, `disjoint_range_leftSide`: planar facts for proper curves (`Supp9B` Jordan sides);
* **`range_subset_closedLeftSide_of_pocket`**: the order passes to the mapped segments (deterministic);
* `Lemma71TwoMiddleStatement` (**named input**: Lemma 7.1 for two middle curves in one pocket);
* **`prop74RefStatement_of_twoMiddle`**: the reference of Proposition 7.4 (`Prop74Order.Prop74RefStatement`) from the
  §4.2 reference, Proposition 5.5 in `ℍ` and the named input;
* **`prop74OrderStatement_of_twoMiddle`**: `Prop74OrderStatement` from these and Lemma 7.5's universal determining
  function; `prop74OrderStatement_of_twoMiddle_exists`: the same with Proposition 5.5 in its one-coupling form.

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal Real
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Sec7.Prop74Pocket

open Supp9B Sec5.Prop55Half

/-! ### Planar facts -/

section Planar

variable {γ α : ℝ≥0 → ℂ}

/-- A real point on the open right side of a proper curve from `0` is positive. -/
theorem pos_of_ofReal_mem_rightSide (hγ : IsProperCurve γ) (h0 : γ 0 = 0) {x : ℝ}
    (hx : (x : ℂ) ∈ rightSide γ) : 0 < x := by
  have hγ0 : (γ 0).im = 0 := by rw [h0]; simp
  have hnS : (x : ℂ) ∉ seedRayClosure γ := connectedComponentIn_subset _ _ hx
  rcases lt_trichotomy x 0 with hlt | heq | hgt
  · have hL := ofReal_mem_leftSide hγ.2.2.1 hγ0 (by rw [h0]; simpa using hlt) hnS
    exact absurd hx (Set.disjoint_left.1 (disjoint_leftSide_rightSide hγ hγ0) hL)
  · exact absurd (Or.inl ⟨0, by rw [h0, heq]; simp⟩ : (x : ℂ) ∈ seedRayClosure γ) hnS
  · exact hgt

/-- **The order seen from the right curve.** For proper curves `γ`, `α` from a common real seed, if `γ` lies in the
closed left side of `α`, then no point of `α` is on the open left side of `γ`. Proof: a point of `α` on the left side
of `γ` is a limit of points of the right side of `α`, so that (connected) side meets the left side of `γ`; it also
contains the common right reference point, on the right side of `γ`; so it meets the closed curve of `γ` — not on the
common ray, so at a point of `γ`, which is then not in the closed left side of `α`. -/
theorem disjoint_range_leftSide (hγ : IsProperCurve γ) (hα : IsProperCurve α) (h0 : γ 0 = α 0)
    (hγ0 : (γ 0).im = 0) (hsub : range γ ⊆ closedLeftSide α) : Disjoint (range α) (leftSide γ) := by
  have hα0 : (α 0).im = 0 := h0 ▸ hγ0
  have hdγ := disjoint_leftSide_rightSide hγ hγ0
  have hdα := disjoint_leftSide_rightSide hα hα0
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨s, rfl⟩ hL
  obtain ⟨q, hqL, hqR⟩ : (leftSide γ ∩ rightSide α).Nonempty :=
    mem_closure_iff.1 (seedRayClosure_subset_closure_rightSide hα hα0 (Or.inl ⟨s, rfl⟩)) _ (isOpen_leftSide hγ) hL
  have hrefR : α 0 + 1 - I ∈ rightSide γ := by
    rw [← h0]; exact rightRef_mem_rightSide hγ.2.2.1 hγ0
  by_cases hmeet : (rightSide α ∩ seedRayClosure γ).Nonempty
  · obtain ⟨u, huR, huS⟩ := hmeet
    have huS' : u ∉ seedRayClosure α := connectedComponentIn_subset _ _ huR
    have huL' : u ∉ leftSide α := fun h => Set.disjoint_left.1 hdα h huR
    rcases huS with ⟨r, rfl⟩ | hr
    · have h := hsub ⟨r, rfl⟩
      rw [closedLeftSide_eq] at h
      rcases h with h | h
      · exact huL' h
      · exact huS' h
    · exact huS' (Or.inr (by rw [← h0]; exact hr))
  · have hsub' : rightSide α ⊆ leftSide γ ∪ rightSide γ := by
      rw [← compl_seedRayClosure_eq hγ hγ0]
      exact fun v hv hvS => hmeet ⟨v, hv, hvS⟩
    rcases (isPreconnected_connectedComponentIn (F := (seedRayClosure α)ᶜ)).subset_or_subset
      (isOpen_leftSide hγ) (isOpen_rightSide hγ) hdγ hsub' with h | h
    · exact Set.disjoint_left.1 hdγ (h (rightRef_mem_rightSide hα.2.2.1 hα0)) hrefR
    · exact Set.disjoint_left.1 hdγ hqL (h hqR)

/-- **First exit to the positive real axis.** A point `w ∈ ℍ̄` on the open right side of a proper curve from `0` lies,
together with some real point `x`, in a preconnected subset of `ℍ̄` contained in that side. -/
theorem exists_preconnected_to_real (hγ : IsProperCurve γ) (h0 : γ 0 = 0) {w : ℂ} (hwH : w ∈ Hbar)
    (hwR : w ∈ rightSide γ) :
    ∃ (T : Set ℂ) (x : ℝ), IsPreconnected T ∧ w ∈ T ∧ (x : ℂ) ∈ T ∧ T ⊆ Hbar ∧ T ⊆ rightSide γ := by
  have hγ0 : (γ 0).im = 0 := by rw [h0]; simp
  by_cases hw : w ∈ H
  · set S := seedRayClosure γ with hS
    have hwS : w ∉ S := connectedComponentIn_subset _ _ hwR
    have hRo : IsOpen (rightSide γ) := isOpen_rightSide hγ
    have hRconn : IsConnected (rightSide γ) :=
      isConnected_connectedComponentIn_iff.2 (lowerRight_subset_compl hγ.2.2.1 (right_ref_mem_lowerRight hγ0))
    have hJ : JoinedIn (rightSide γ) w (γ 0 + 1 - I) :=
      ((hRo.isConnected_iff_isPathConnected).1 hRconn).joinedIn w hwR _
        (rightRef_mem_rightSide hγ.2.2.1 hγ0)
    have hneg : (γ 0 + 1 - I).im < 0 := by simp [hγ0]
    obtain ⟨x, hxR, hxcl⟩ := exists_ofReal_mem_closure_of_joinedIn hw hneg
      (connectedComponentIn_subset (seedRayClosure γ)ᶜ _) hJ
    set K := connectedComponentIn (H \ S) w with hK
    have hKR : K ⊆ rightSide γ := by
      have e : rightSide γ = connectedComponentIn Sᶜ w := connectedComponentIn_eq hwR
      rw [e]
      exact isPreconnected_connectedComponentIn.subset_connectedComponentIn (mem_connectedComponentIn ⟨hw, hwS⟩)
        ((connectedComponentIn_subset _ _).trans (sdiff_subset_compl _ _))
    refine ⟨insert (x : ℂ) K, x, isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
      (insert_subset hxcl subset_closure), mem_insert_of_mem _ (mem_connectedComponentIn ⟨hw, hwS⟩),
      mem_insert _ _, insert_subset (by simp [Hbar]) fun z hz => ?_, insert_subset hxR hKR⟩
    exact show (0 : ℝ) ≤ z.im from le_of_lt (show 0 < z.im from (connectedComponentIn_subset _ _ hz).1)
  · have him : w.im = 0 := le_antisymm (not_lt.1 hw) hwH
    have e : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [him])
    refine ⟨{w}, w.re, isPreconnected_singleton, mem_singleton _, by rw [← e]; exact mem_singleton _,
      singleton_subset_iff.2 hwH, singleton_subset_iff.2 hwR⟩

end Planar

/-! ### The order passes to the mapped segments -/

/-- **The order of two middle curves passes to their mapped segments in a pocket** (deterministic). Let `γ₁`, `α` be
simple proper curves from `0` off `ℝ ∖ {0}`, `γ₂` a curve with `γ₂ ≤ γ₁ ≤ α` (closed left sides), and `G : ℍ̄ → ℂ`
continuous and injective with `G(ℍ) ⊆ ℍ` and `G(x) ∈ α` for `x > 0` (the extended inverse chart of a pocket whose
right boundary arc lies on `α`). If `η'₁` is a proper curve from `0` whose `G`-image is exactly the part of `γ₁` in
`G(ℍ̄)`, and `η'₂` is a curve in `ℍ̄` whose `G`-image lies on `γ₂`, then `η'₂` lies in the closed left side of `η'₁`. -/
theorem range_subset_closedLeftSide_of_pocket {γ₁ γ₂ α η₁ η₂ : ℝ≥0 → ℂ} {G : ℂ → ℂ}
    (hγ₁ : IsSeedProper γ₁) (hα : IsSeedProper α) (h21 : range γ₂ ⊆ closedLeftSide γ₁)
    (h1α : range γ₁ ⊆ closedLeftSide α) (hGc : ContinuousOn G Hbar) (hGinj : InjOn G Hbar)
    (hGH : MapsTo G H H) (hGR : ∀ x : ℝ, 0 < x → G x ∈ range α)
    (h₁ : IsProperCurve η₁) (h₁0 : η₁ 0 = 0) (h₂ : ∀ t, 0 ≤ (η₂ t).im)
    (himg₁ : G '' range η₁ = range γ₁ ∩ G '' Hbar) (himg₂ : G '' range η₂ ⊆ range γ₂) :
    range η₂ ⊆ closedLeftSide η₁ := by
  have hγ₁P := hγ₁.isProperCurve
  have hαP := hα.isProperCurve
  have h1im0 : (γ₁ 0).im = 0 := hγ₁.im_zero
  have h'0 : (η₁ 0).im = 0 := by rw [h₁0]; simp
  -- `G` keeps the right side of `η₁` (in `ℍ̄`) off the closed curve of `γ₁`
  have key : ∀ z ∈ Hbar, z ∈ rightSide η₁ → G z ∉ seedRayClosure γ₁ := by
    intro z hz hzR hS
    have hzS : z ∉ seedRayClosure η₁ := connectedComponentIn_subset _ _ hzR
    have hcurve : G z ∉ range γ₁ := by
      intro hG1
      have hmem : G z ∈ G '' range η₁ := himg₁ ▸ ⟨hG1, z, hz, rfl⟩
      obtain ⟨_, ⟨r, rfl⟩, hr⟩ := hmem
      exact hzS (Or.inl ⟨r, hGinj (h₁.2.2.1 r) hz hr⟩)
    rcases hS with hS | ⟨-, him⟩
    · exact hcurve hS
    · rw [hγ₁.2.2.1, Complex.zero_im] at him
      by_cases hzH : z ∈ H
      · exact absurd (hGH hzH) (not_lt.2 him)
      · have hzim : z.im = 0 := le_antisymm (not_lt.1 hzH) hz
        have e : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hzim])
        have hx0 : 0 < z.re := pos_of_ofReal_mem_rightSide h₁ h₁0 (e ▸ hzR)
        obtain ⟨s, hs⟩ := hGR z.re hx0
        rw [← e] at hs
        rcases eq_zero_or_pos s with hs0 | hs0
        · exact hcurve ⟨0, by rw [hγ₁.2.2.1, ← hs, hs0, hα.2.2.1]⟩
        · have hsH : α s ∈ H := hα.2.2.2.1 s hs0
          rw [hs] at hsH
          exact absurd hsH (not_lt.2 him)
  rintro _ ⟨t, rfl⟩
  by_contra hnot
  rw [closedLeftSide_eq] at hnot
  have hwH : η₂ t ∈ Hbar := h₂ t
  have hwR : η₂ t ∈ rightSide η₁ := by
    have h : η₂ t ∈ (seedRayClosure η₁)ᶜ := fun h => hnot (Or.inr h)
    rw [compl_seedRayClosure_eq h₁ h'0] at h
    exact h.resolve_left fun h' => hnot (Or.inl h')
  -- `G (η₂ t)` is a point of `γ₂`, hence on the open left side of `γ₁`
  have hGw : G (η₂ t) ∈ leftSide γ₁ := by
    have h1 : G (η₂ t) ∈ closedLeftSide γ₁ := h21 (himg₂ ⟨η₂ t, ⟨t, rfl⟩, rfl⟩)
    rw [closedLeftSide_eq] at h1
    exact h1.resolve_right (key _ hwH hwR)
  obtain ⟨T, x, hTc, hwT, hxT, hTH, hTR⟩ := exists_preconnected_to_real h₁ h₁0 hwH hwR
  have hx0 : 0 < x := pos_of_ofReal_mem_rightSide h₁ h₁0 (hTR hxT)
  have hGT : G '' T ⊆ leftSide γ₁ ∪ rightSide γ₁ := by
    rintro _ ⟨z, hz, rfl⟩
    rw [← compl_seedRayClosure_eq hγ₁P h1im0]
    exact key z (hTH hz) (hTR hz)
  have hd := disjoint_leftSide_rightSide hγ₁P h1im0
  rcases (hTc.image G (hGc.mono hTH)).subset_or_subset (isOpen_leftSide hγ₁P) (isOpen_rightSide hγ₁P) hd hGT
    with h | h
  · exact Set.disjoint_left.1 (disjoint_range_leftSide hγ₁P hαP (by rw [hγ₁.2.2.1, hα.2.2.1]) h1im0 h1α)
      (hGR x hx0) (h ⟨x, hxT, rfl⟩)
  · exact Set.disjoint_left.1 hd hGw (h ⟨_, hwT, rfl⟩)

/-! ### The named input and the assembly -/

/-- **Named input: Lemma 7.1 for two middle curves in one pocket** (specification p. 243: "Applying the same
component-pair construction simultaneously to finitely many middle flow lines"; §7.1 setup, Lemma 7.1 and its proof,
pp. 221–225; Figure 7.1). For `0 < κ < 4`, outer angles `α₁ < α₂`, middle angles `α₁ < θ₁ < θ₂ < α₂` and boundary values
with (5.2) for the outer pair, on **every** four-curve space there are, for one pocket `C` between the outer curves
`β = η_{α₂}` and `α = η_{α₁}`:
* the extended inverse chart `G = ψ⁻¹ : ℍ̄ → C̄` — continuous and injective on `ℍ̄`, `G(ℍ) ⊆ ℍ`, the negative axis to
  the left flank `β`, the positive axis to the right flank `α` (Remark 6.14's Jordan boundary homeomorphism);
* the pocket field `h_ψ = h ∘ ψ⁻¹ − χ arg (ψ⁻¹)′`, a GFF with the data `λ − α₂χ` on `ℝ₋` and `−λ − α₁χ` on `ℝ₊`
  (Figure 7.1, right; part of the coupling specification of Lemma 7.1);
* for `i = 1, 2`, the mapped middle segment `η'ᵢ = ψ(γᵢ ∩ C̄)`, reparametrized by capacity: the angle-`θᵢ` flow line of
  `h_ψ` from `0` (Lemma 7.1 for the middle curve `γᵢ`, after the angle shift by `θᵢ`; its seed weights
  `(α₂ − θᵢ)χ/λ − 2` and `(θᵢ − α₁)χ/λ − 2` are (CPF2)), with infinite lifetime, a continuous simple curve in `ℍ̄`
  tending to `∞` (Lemma 7.1: "a continuous simple path in `ℍ̄` and tends to `∞` at the end of its capacity lifetime"),
  whose `G`-image is exactly the part of `γᵢ` in the closed pocket (p. 224: `γ([σ_D, τ_D]) ⊆ D̄`, no visit outside
  `[σ_D, τ_D]`). -/
def Lemma71TwoMiddleStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ α₁ θ₁ θ₂ α₂ A B : ℝ, α₁ < θ₁ → θ₁ < θ₂ → θ₂ < α₂ →
    sleLambda κ - π * chiC κ + α₂ * chiC κ ≤ A → sleLambda κ - α₁ * chiC κ ≤ B →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) (β γ₂ γ₁ α : Ω → ℝ≥0 → ℂ) (ζβ ζ₂ ζ₁ ζα : Ω → ℝ≥0∞),
      Lemma71Four.IsFourCurveSpace κ α₁ θ₁ θ₂ α₂ A B P h u₀ β γ₂ γ₁ α ζβ ζ₂ ζ₁ ζα →
    ∃ (G : Ω → ℂ → ℂ) (hψ : Ω → DistOn upperHalfPlaneOpens) (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ'₁ ζ'₂ : Ω → ℝ≥0∞),
      IsGFFWithBoundaryData P hψ (prop74Data (α₂ * chiC κ - sleLambda κ) (-sleLambda κ - α₁ * chiC κ)) {0} ∧
      IsFlowLine κ (prop74Data (α₂ * chiC κ - sleLambda κ) (-sleLambda κ - α₁ * chiC κ)) {0} 0 θ₁ P hψ η₁ ζ'₁ ∧
      IsFlowLine κ (prop74Data (α₂ * chiC κ - sleLambda κ) (-sleLambda κ - α₁ * chiC κ)) {0} 0 θ₂ P hψ η₂ ζ'₂ ∧
      ∀ᵐ ω ∂P, ζ'₁ ω = ⊤ ∧ ζ'₂ ω = ⊤ ∧ IsProperCurve (η₁ ω) ∧ IsProperCurve (η₂ ω) ∧
        ContinuousOn (G ω) Hbar ∧ InjOn (G ω) Hbar ∧ MapsTo (G ω) H H ∧
        (∀ x : ℝ, x < 0 → G ω x ∈ range (β ω)) ∧ (∀ x : ℝ, 0 < x → G ω x ∈ range (α ω)) ∧
        G ω '' range (η₁ ω) = range (γ₁ ω) ∩ G ω '' Hbar ∧ G ω '' range (η₂ ω) = range (γ₂ ω) ∩ G ω '' Hbar

/-- A flow line from `x` starts at `x`, almost surely. -/
theorem IsFlowLine.ae_apply_zero {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {x θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLine κ b J x θ P h η ζ) : ∀ᵐ ω ∂P, η ω 0 = x := by
  obtain ⟨_, _, _, _, _, _, _, _, htr⟩ := hfl
  filter_upwards [htr] with ω hω
  have h0 := hω.1
  simp only [sub_eq_zero] at h0
  exact h0

/-- **The reference of Proposition 7.4 from two middle curves in one pocket.** With `α₂ = (a + λ)/χ`,
`α₁ = −(λ + b)/χ` and `(A, B)` the smallest values with (5.2) for the outer pair, the four-curve space exists
(`Lemma71Four.exists_isFourCurveSpace`); the named input gives the pocket field, with the data `(a, b)`, and its two
flow lines, complete proper curves; their order is `range_subset_closedLeftSide_of_pocket`. Conditional helper. -/
theorem prop74RefStatement_of_twoMiddle (href : Lemma71H.Cond44ReferenceStatement.{u})
    (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) (h2m : Lemma71TwoMiddleStatement.{u}) :
    Prop74Order.Prop74RefStatement.{u} := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 h1 h2
  have hχ := Sec4.chiC_pos hκ hκ4
  obtain ⟨Ω, mΩ, P, hP, h, u₀, β, γ₂, γ₁, α, ζβ, ζ₂, ζ₁, ζα, hS⟩ :=
    Lemma71Four.exists_isFourCurveSpace href h55 hκ hκ4 h1 h12 h2 le_rfl le_rfl
  obtain ⟨G, hψ, η₁, η₂, ζ'₁, ζ'₂, hψG, hη₁, hη₂, hae⟩ :=
    h2m κ hκ hκ4 _ θ₁ θ₂ _ _ _ h1 h12 h2 le_rfl le_rfl P h u₀ β γ₂ γ₁ α ζβ ζ₂ ζ₁ ζα hS
  have ea : (a + sleLambda κ) / chiC κ * chiC κ - sleLambda κ = a := by
    rw [div_mul_cancel₀ _ hχ.ne']; ring
  have eb : -sleLambda κ - -(sleLambda κ + b) / chiC κ * chiC κ = b := by
    rw [div_mul_cancel₀ _ hχ.ne']; ring
  rw [ea, eb] at hψG hη₁ hη₂
  refine ⟨Ω, mΩ, P, hP, hψ, η₁, η₂, ζ'₁, ζ'₂, hψG, hη₁, hη₂, ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hSae⟩ := hS
  filter_upwards [hae, hSae, IsFlowLine.ae_apply_zero hη₁] with ω hω hSω h0
  obtain ⟨hz₁, hz₂, hp₁, hp₂, hGc, hGi, hGH, -, hGR, hi₁, hi₂⟩ := hω
  obtain ⟨-, -, -, -, -, -, e₁, eα, -, -, -, o21, -, o1α⟩ := hSω
  refine ⟨hz₁, hz₂, hp₁.1, hp₁.2.1, hp₁.2.2.1, hp₁.2.2.2, hp₂.1, hp₂.2.1, hp₂.2.2.1, hp₂.2.2.2, ?_⟩
  exact range_subset_closedLeftSide_of_pocket e₁ eα o21 o1α hGc hGi hGH hGR hp₁ (by simpa using h0) hp₂.2.2.1 hi₁
    (hi₂.subset.trans inter_subset_left)

/-- **Proposition 7.4's order** (`Prop74OrderStatement`) from Lemma 7.5's universal determining function, the §4.2
reference, Proposition 5.5 in `ℍ` and Lemma 7.1 for two middle curves in one pocket. Conditional helper. -/
theorem prop74OrderStatement_of_twoMiddle (h75 : Theorem15.Lemma75Statement.{u})
    (href : Lemma71H.Cond44ReferenceStatement.{u}) (h55 : Lemma71H.Prop55HalfPlaneStatement.{u})
    (h2m : Lemma71TwoMiddleStatement.{u}) : Prop74OrderStatement.{u} :=
  Prop74Order.prop74OrderStatement_of_ref h75 (prop74RefStatement_of_twoMiddle href h55 h2m)

/-- `prop74OrderStatement_of_twoMiddle` with Proposition 5.5 in its one-coupling form
(`Prop55Half.Prop55HalfExistsStatement`, through the landed `prop55HalfPlaneStatement_of_exists`). -/
theorem prop74OrderStatement_of_twoMiddle_exists (h75 : Theorem15.Lemma75Statement.{u})
    (href : Lemma71H.Cond44ReferenceStatement.{u}) (hex : Prop55HalfExistsStatement.{u})
    (h2m : Lemma71TwoMiddleStatement.{u}) : Prop74OrderStatement.{u} :=
  prop74OrderStatement_of_twoMiddle h75 href (prop55HalfPlaneStatement_of_exists href hex) h2m

end InteractingSLE.Sec7.Prop74Pocket
