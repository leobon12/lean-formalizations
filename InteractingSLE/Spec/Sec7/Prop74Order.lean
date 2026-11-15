/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop55Half
import InteractingSLE.Spec.Theorem15Inputs

/-!
# Proposition 7.4's order: the law step

Packet PROVE-PROP74. Source: Proposition 7.4 (`source/spec/p241-288.md` L56–L64, p. 244) and the two sentences before
it (p. 243): "The flow lines with constant boundary heights on the two real half-lines are consequently well-defined
path-valued functions of their fields in the original coupling class. Applying the same component-pair construction
simultaneously to finitely many middle flow lines proves the following monotonicity statement for these functions."

So the proof has two parts:

* **the reference** — one coupling of the GFF with the data of Figure 7.1 and its two flow lines `η_{θ₁}`, `η_{θ₂}`,
  in which they are complete simple proper curves with `η_{θ₂}` in the closed left side of `η_{θ₁}` (the images of two
  ordered middle flow lines in one pocket of the component-pair construction; `Prop74OrderPocket.lean`). This is the
  named statement **`Prop74RefStatement`**;
* **the law step** (this file) — "well-defined path-valued functions of their fields": one Borel map `Φᵢ` of the field
  gives `η_{θᵢ}` in every coupling (`Theorem15.Lemma75Statement`, the universal determining function); the order of
  the two complete curves is a Borel event on the dyadic codes of `(Φ₁ f, Φ₂ f)` (`ordCodeSet`), so it holds for almost
  every field under the common GFF law, hence in every coupling. A complete curve is its own proper completion of each
  of its prefixes, which gives the W0 form of `Prop74OrderStatement`.

## Main results

* `IsCompleteOrderedPair α β` and `IsCompleteOrderedPair.hasOrderedProperCompletions`;
* `ordCodeSet`, `measurableSet_ordCodeSet`, `mem_ordCodeSet_iff`;
* `ae_isCompleteOrderedPair_of_map`: the transfer along the field law;
* **`prop74OrderStatement_of_ref`**: `Lemma75Statement → Prop74RefStatement → Prop74OrderStatement`.

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Sec7.Prop74Order

open Theorem15D5

/-! ### Complete ordered pairs -/

/-- **Two complete ordered curves**: both continuous, injective, in the closed upper half-plane and tending to `∞`,
and the range of the second in the closed left side of the first (the frozen W0 notion). -/
def IsCompleteOrderedPair (α β : ℝ≥0 → ℂ) : Prop :=
  Continuous α ∧ Function.Injective α ∧ (∀ t, 0 ≤ (α t).im) ∧ Tendsto (fun t => ‖α t‖) atTop atTop ∧
    Continuous β ∧ Function.Injective β ∧ (∀ t, 0 ≤ (β t).im) ∧ Tendsto (fun t => ‖β t‖) atTop atTop ∧
    range β ⊆ closedLeftSide α

/-- A complete ordered pair has ordered proper completions of all its prefixes: each curve is its own completion. -/
theorem IsCompleteOrderedPair.hasOrderedProperCompletions {α β : ℝ≥0 → ℂ} (h : IsCompleteOrderedPair α β)
    (s t : ℝ≥0) : HasOrderedProperCompletions α s β t :=
  ⟨α, β, ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun _ _ => rfl⟩,
    ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, fun _ _ => rfl⟩, h.2.2.2.2.2.2.2.2⟩

/-! ### The Borel event on codes -/

/-- The Borel set of code pairs of two complete ordered curves: `Prop55Half.orderCodeSet` (uniformly continuous codes,
the first proper, the second in the closed left side of the first) together with the countable forms of injectivity,
`0 ≤ Im` and properness of both. -/
def ordCodeSet : Set (CCode × CCode) :=
  Sec5.Prop55Half.orderCodeSet ∩ {x | InjC x.1 ∧ ImC x.1 ∧ InjC x.2 ∧ ImC x.2 ∧ PropC x.2}

theorem measurableSet_ordCodeSet : MeasurableSet ordCodeSet := by
  refine Sec5.Prop55Half.measurableSet_orderCodeSet.inter (measurableSet_setOfPred.mpr ?_)
  have m1 : Measurable fun x : CCode × CCode => x.1 := measurable_fst
  have m2 : Measurable fun x : CCode × CCode => x.2 := measurable_snd
  exact (measurable_injC.comp m1).and <| (measurable_imC.comp m1).and <| (measurable_injC.comp m2).and <|
    (measurable_imC.comp m2).and (measurable_propC.comp m2)

/-- For continuous paths, the code pair is in `ordCodeSet` iff the paths form a complete ordered pair. -/
theorem mem_ordCodeSet_iff {α β : ℝ≥0 → ℂ} (hα : Continuous α) (hβ : Continuous β) :
    (encC α, encC β) ∈ ordCodeSet ↔ IsCompleteOrderedPair α β := by
  have g₁ := goodAll_encC hα
  have g₂ := goodAll_encC hβ
  have e₁ := decC_encC_of_continuous hα
  have e₂ := decC_encC_of_continuous hβ
  have i₁ : Function.Injective α ↔ InjC (encC α) := by rw [← injective_iff_injC g₁, e₁]
  have i₂ : Function.Injective β ↔ InjC (encC β) := by rw [← injective_iff_injC g₂, e₂]
  have m₁ : (∀ t, 0 ≤ (α t).im) ↔ ImC (encC α) := by rw [← im_nonneg_iff_imC g₁, e₁]
  have m₂ : (∀ t, 0 ≤ (β t).im) ↔ ImC (encC β) := by rw [← im_nonneg_iff_imC g₂, e₂]
  have p₁ : Tendsto (fun t => ‖α t‖) atTop atTop ↔ PropC (encC α) := by rw [← tendsto_norm_iff_propC g₁, e₁]
  have p₂ : Tendsto (fun t => ‖β t‖) atTop atTop ↔ PropC (encC β) := by rw [← tendsto_norm_iff_propC g₂, e₂]
  constructor
  · rintro ⟨hO, hI₁, hM₁, hI₂, hM₂, hP₂⟩
    have hT₁ : Tendsto (fun t => ‖α t‖) atTop atTop := p₁.2 hO.2.1
    exact ⟨hα, i₁.2 hI₁, m₁.2 hM₁, hT₁, hβ, i₂.2 hI₂, m₂.2 hM₂, p₂.2 hP₂,
      (Sec5.Prop55Half.mem_orderCodeSet_iff hα hT₁ hβ).1 hO⟩
  · rintro ⟨-, hI₁, hM₁, hT₁, -, hI₂, hM₂, hT₂, hsub⟩
    exact ⟨(Sec5.Prop55Half.mem_orderCodeSet_iff hα hT₁ hβ).2 hsub, i₁.1 hI₁, m₁.1 hM₁, i₂.1 hI₂, m₂.1 hM₂,
      p₂.1 hT₂⟩

/-! ### Transfer along the field law -/

section Law

variable {F : Type*} [MeasurableSpace F] {Φ₁ Φ₂ : F → ℝ≥0∞ × (ℝ≥0 → ℂ)}

/-- **Complete ordered pairs of two Borel functions of the field transfer along the field law.** If, for a field
`h₀`, almost surely both lifetimes `(Φᵢ h₀).1` are `⊤` and the paths `(Φᵢ h₀).2` form a complete ordered pair, and a
field `h` has the same law, then almost surely both lifetimes of `h` are `⊤` and its two paths form a complete ordered
pair as soon as they are continuous. -/
theorem ae_isCompleteOrderedPair_of_map (hΦ₁ : Measurable Φ₁) (hΦ₂ : Measurable Φ₂)
    {Ω Ω₀ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀] {P : Measure Ω} {P₀ : Measure Ω₀}
    {h : Ω → F} {h₀ : Ω₀ → F} (hhm : Measurable h) (hh₀m : Measurable h₀) (hlaw : P.map h = P₀.map h₀)
    (href : ∀ᵐ ω₀ ∂P₀, (Φ₁ (h₀ ω₀)).1 = ⊤ ∧ (Φ₂ (h₀ ω₀)).1 = ⊤ ∧
      IsCompleteOrderedPair (Φ₁ (h₀ ω₀)).2 (Φ₂ (h₀ ω₀)).2) :
    ∀ᵐ ω ∂P, (Φ₁ (h ω)).1 = ⊤ ∧ (Φ₂ (h ω)).1 = ⊤ ∧
      (Continuous (Φ₁ (h ω)).2 → Continuous (Φ₂ (h ω)).2 →
        IsCompleteOrderedPair (Φ₁ (h ω)).2 (Φ₂ (h ω)).2) := by
  set c : F → CCode × CCode := fun f => (encC (Φ₁ f).2, encC (Φ₂ f).2) with hc
  have hcm : Measurable c :=
    (Sec5.Prop55Half.measurable_encC_comp fun t => (measurable_pi_apply t).comp (measurable_snd.comp hΦ₁)).prodMk
      (Sec5.Prop55Half.measurable_encC_comp fun t => (measurable_pi_apply t).comp (measurable_snd.comp hΦ₂))
  set G : Set F := (fun f => (Φ₁ f).1) ⁻¹' {⊤} ∩ (fun f => (Φ₂ f).1) ⁻¹' {⊤} ∩ c ⁻¹' ordCodeSet with hG
  have hGm : MeasurableSet G :=
    (((measurableSet_singleton ⊤).preimage (measurable_fst.comp hΦ₁)).inter
      ((measurableSet_singleton ⊤).preimage (measurable_fst.comp hΦ₂))).inter (hcm measurableSet_ordCodeSet)
  have h₀G : ∀ᵐ ω₀ ∂P₀, h₀ ω₀ ∈ G := by
    filter_upwards [href] with ω₀ hω
    exact ⟨⟨hω.1, hω.2.1⟩, (mem_ordCodeSet_iff hω.2.2.1 hω.2.2.2.2.2.2.1).2 hω.2.2⟩
  have hμG : ∀ᵐ f ∂(P₀.map h₀), f ∈ G := (ae_map_iff hh₀m.aemeasurable hGm).2 h₀G
  rw [← hlaw] at hμG
  have hG' : ∀ᵐ ω ∂P, h ω ∈ G := (ae_map_iff hhm.aemeasurable hGm).1 hμG
  filter_upwards [hG'] with ω hω
  exact ⟨hω.1.1, hω.1.2, fun c₁ c₂ => (mem_ordCodeSet_iff c₁ c₂).1 hω.2⟩

end Law

/-! ### The assembly -/

section Assembly

/-- The singleton jump set as a coerced `Finset` (the form of `Theorem15.Lemma75Statement`). -/
theorem isGFFWithBoundaryData_coe_singleton {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {g : ℝ → ℝ} (hh : IsGFFWithBoundaryData P h g ({0} : Set ℝ)) :
    IsGFFWithBoundaryData P h g ((({0} : Finset ℝ)) : Set ℝ) := by
  rwa [Finset.coe_singleton]

/-- An angle-`θ` flow line from `x` is almost surely continuous up to its lifetime (the generating-trace clause). -/
theorem IsFlowLine.ae_continuousOn {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {x θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLine κ b J x θ P h η ζ) : ∀ᵐ ω ∂P, ContinuousOn (η ω) {t | (t : ℝ≥0∞) ≤ ζ ω} := by
  obtain ⟨_, _, _, _, _, _, _, _, htr⟩ := hfl
  filter_upwards [htr] with ω hω
  exact (hω.2.1.add (continuousOn_const (c := (x : ℂ)))).congr fun t _ => (sub_add_cancel (η ω t) (x : ℂ)).symm

/-- **Named input: the reference coupling of Proposition 7.4** (p. 243: the component-pair construction applied
simultaneously to two middle flow lines; `Prop74OrderPocket.lean` derives it from Lemma 7.1 for two middle curves). For
`0 < κ < 4`, the data of Figure 7.1 (`−a` on `ℝ₋`, `b` on `ℝ₊`) and angles `θ₁ < θ₂` with Proposition 7.4's bounds,
**some** probability space carries a GFF `h` with these data and two flow lines `η_{θ₁}`, `η_{θ₂}` of `h` from `0`
which almost surely have infinite lifetimes and form a complete ordered pair (`η_{θ₂}` in the closed left side of
`η_{θ₁}`). -/
def Prop74RefStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ a b θ₁ θ₂ : ℝ, θ₁ < θ₂ →
    -(sleLambda κ + b) / chiC κ < θ₁ → θ₂ < (a + sleLambda κ) / chiC κ →
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (h : Ω → DistOn upperHalfPlaneOpens) (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsGFFWithBoundaryData P h (prop74Data a b) {0} ∧
      IsFlowLine κ (prop74Data a b) {0} 0 θ₁ P h η₁ ζ₁ ∧ IsFlowLine κ (prop74Data a b) {0} 0 θ₂ P h η₂ ζ₂ ∧
      ∀ᵐ ω ∂P, ζ₁ ω = ⊤ ∧ ζ₂ ω = ⊤ ∧ IsCompleteOrderedPair (η₁ ω) (η₂ ω)

/-- **Proposition 7.4's order (`Prop74OrderStatement`) from the reference coupling and Lemma 7.5's universal
determining function.** Lemma 7.5 gives Borel maps `Φ₁`, `Φ₂` of the field with `η_{θᵢ} = Φᵢ(h)` up to the lifetime in
every coupling; in the reference the lifetimes are infinite and the curves a complete ordered pair, so (the two fields
having the same law) the same holds for `(Φ₁ h, Φ₂ h)` in every coupling, where the paths are the flow lines (they
are continuous up to the infinite lifetime). Each complete curve is a proper completion of each of its prefixes. -/
theorem prop74OrderStatement_of_ref (h75 : Theorem15.Lemma75Statement.{u}) (href : Prop74RefStatement.{u}) :
    Prop74OrderStatement.{u} := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 h1 h2 Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  have hbpc := isPiecewiseConstant_prop74Data a b
  obtain ⟨Φ₁, hΦ₁m, hΦ₁⟩ := h75 κ hκ hκ4 (prop74Data a b) {0} hbpc 0 θ₁
  obtain ⟨Φ₂, hΦ₂m, hΦ₂⟩ := h75 κ hκ hκ4 (prop74Data a b) {0} hbpc 0 θ₂
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, h₀, α₀, β₀, ζα, ζβ, hh₀, hα₀, hβ₀, hord⟩ := href κ hκ hκ4 a b θ₁ θ₂ h12 h1 h2
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hbpc
  have hu₀' : IsBoundedHarmonicExtension (prop74Data a b) ({0} : Set ℝ) u₀ := by
    simpa only [Finset.coe_singleton] using hu₀
  have hlaw : P.map h = P₀.map h₀ := Exist.map_eq_of_isGFFWithBoundaryData hh hh₀ hu₀'
  have hh₀' := isGFFWithBoundaryData_coe_singleton hh₀
  have hh' := isGFFWithBoundaryData_coe_singleton hh
  have href' : ∀ᵐ ω₀ ∂P₀, (Φ₁ (h₀ ω₀)).1 = ⊤ ∧ (Φ₂ (h₀ ω₀)).1 = ⊤ ∧
      IsCompleteOrderedPair (Φ₁ (h₀ ω₀)).2 (Φ₂ (h₀ ω₀)).2 := by
    filter_upwards [hord, hΦ₁ P₀ h₀ hh₀' α₀ ζα hα₀, hΦ₂ P₀ h₀ hh₀' β₀ ζβ hβ₀] with ω₀ hω e₁ e₂
    obtain ⟨hζα, hζβ, hp⟩ := hω
    have f₁ : (Φ₁ (h₀ ω₀)).2 = α₀ ω₀ := funext fun t => e₁.2 t (by rw [hζα]; exact le_top)
    have f₂ : (Φ₂ (h₀ ω₀)).2 = β₀ ω₀ := funext fun t => e₂.2 t (by rw [hζβ]; exact le_top)
    rw [f₁, f₂]
    exact ⟨e₁.1.trans hζα, e₂.1.trans hζβ, hp⟩
  have htr := ae_isCompleteOrderedPair_of_map hΦ₁m hΦ₂m hh.1 hh₀.1 hlaw href'
  filter_upwards [htr, hΦ₁ P h hh' η₁ ζ₁ hη₁, hΦ₂ P h hh' η₂ ζ₂ hη₂, IsFlowLine.ae_continuousOn hη₁,
    IsFlowLine.ae_continuousOn hη₂] with ω hω e₁ e₂ c₁ c₂ s t _ _
  have hζ₁ : ζ₁ ω = ⊤ := e₁.1.symm.trans hω.1
  have hζ₂ : ζ₂ ω = ⊤ := e₂.1.symm.trans hω.2.1
  have f₁ : (Φ₁ (h ω)).2 = η₁ ω := funext fun t => e₁.2 t (by rw [hζ₁]; exact le_top)
  have f₂ : (Φ₂ (h ω)).2 = η₂ ω := funext fun t => e₂.2 t (by rw [hζ₂]; exact le_top)
  have hc₁ : Continuous (η₁ ω) := by
    rw [← continuousOn_univ]
    exact c₁.mono fun t _ => show (t : ℝ≥0∞) ≤ ζ₁ ω by rw [hζ₁]; exact le_top
  have hc₂ : Continuous (η₂ ω) := by
    rw [← continuousOn_univ]
    exact c₂.mono fun t _ => show (t : ℝ≥0∞) ≤ ζ₂ ω by rw [hζ₂]; exact le_top
  have hp := hω.2.2
  rw [f₁, f₂] at hp
  exact (hp hc₁ hc₂).hasOrderedProperCompletions s t

end Assembly

end InteractingSLE.Sec7.Prop74Order
