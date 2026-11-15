/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop55HalfSide
import InteractingSLE.Spec.Sec7.Lemma71HInputs
import InteractingSLE.Spec.Sec7.Lemma71GFlow
import InteractingSLE.Spec.Zhan.TransienceTrace
import InteractingSLE.Spec.Supplement.LPTrace
import InteractingSLE.Spec.Theorem15D5Code
import InteractingSLE.Spec.Sec5.Prop51CondDet
import InteractingSLE.Spec.Sec4.Prob41Charts

/-!
# Proposition 5.5 in `ℍ` from one coupling

Packet PROVE-SEC5-K (specification p. 135, Proposition 5.5, last sentence of its statement and of its proof). The
consumer `Lemma71H.Prop55HalfPlaneStatement` asks, for **every** coupling of a GFF `h` on `ℍ` with the data of Figure
7.1 (`−a` on `ℝ₋`, `b` on `ℝ₊`) and two of its flow lines `η_{θ₁}`, `η_{θ₂}` from `0` (`θ₁ < θ₂`, bounds (5.2)), that
almost surely `η_{θ₂}` lies in the closed left side of `η_{θ₁}` (frozen W0 order). This file reduces it to:

* the reference of §4.2 (`Lemma71H.Cond44ReferenceStatement`, already a named input of the same consumer): both flow
  words satisfy (4.4), so one Borel map of the field gives every flow line of every coupling
  (`Lemma75Bridge.exists_flowLineMap_of_admissible`, Aux. lemma 23);
* **`Prop55HalfExistsStatement`**: for each such datum, **one** coupling of `h` with its two flow lines in which
  almost surely no point of `η_{θ₁}` is strictly on the left of `η_{θ₂}` (the strict-side form that the proof of
  Proposition 5.5 produces: `η_{θ₁}` is in the left boundary of a counterflow line which passes to the right of
  `η_{θ₂}`). Any convenient probability space may be used, e.g. one carrying the counterflow line with the flow lines
  realized as functions of the field.

Steps proved here:

* **regularity** (`IsFlowLine.ae_isSeedProper`): in Remark 4.1's regime a flow line from `0` almost surely has infinite
  lifetime and is a simple proper curve from `0` (`Zhan.IsIntegratedSLEEvolution.ae_simple_trace`, uniqueness of
  generating traces, `Lemma71G.IsFlowLine.ae_tendsto_angle`);
* **the planar step** (`Prop55HalfSide.lean`): strict-side order ⇒ closed-left-side order for simple proper curves;
* **the law step** (`ae_range_subset_closedLeftSide_of_map_eq`): the closed-side order of two Borel functions of the
  field is a Borel event on the good set of continuous proper curves (dyadic codes, `Theorem15D5`), so it transfers
  between any two fields with the same law;
* **`prop55HalfPlaneStatement_of_exists`**: the assembly.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Sec5

namespace Prop55Half

open Theorem15D5

/-! ### Regularity of the flow lines -/

section Regular

variable {k : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **An angle-`θ` flow line from `0` in Remark 4.1's regime is almost surely a simple proper curve from `0`, with
infinite lifetime** (Remark 2.3 for `κ ≤ 4`: the injective trace of `Zhan.IsIntegratedSLEEvolution.ae_simple_trace`
is the flow line by uniqueness of generating traces; transience by `Lemma71G.IsFlowLine.ae_tendsto_angle`). -/
theorem IsFlowLine.ae_isSeedProper (hk : 0 < k) (hk4 : k ≤ 4) (hb : IsPiecewiseConstantBoundaryData b J) {θ : ℝ}
    (hL : ∀ x : ℝ, x < 0 → x ∉ J → b x + θ * chiC k ≤ -sleLambda k + π * chiC k)
    (hR : ∀ x : ℝ, 0 < x → x ∉ J → sleLambda k - π * chiC k ≤ b x + θ * chiC k)
    (hfl : IsFlowLine k b J 0 θ P h η ζ) : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsSeedProper (η ω) := by
  obtain ⟨𝓕, W, VL, VR, B, hev, htr⟩ := Sec7.Lemma71G.IsFlowLine.exists_evolution_angle hfl
  have hword := Theorem15.isOrderedForceWord_flowLine b J 0
  have hadm := Sec7.Lemma71G.hasAdmissiblePartialSums_flowLine_angle hk hb θ hL hR
  filter_upwards [Zhan.IsIntegratedSLEEvolution.ae_simple_trace hk hk4 hword hadm hev, htr, hev.2.2.2.2,
    Sec7.Lemma71G.IsFlowLine.ae_tendsto_angle hk hk4 hb hL hR hfl] with ω h1 h2 h3 h4
  obtain ⟨hζ, -, η', hη', hinj, hH, -⟩ := h1
  rw [hζ] at h2 h3
  have heq : η ω = η' := funext fun t => h2.eq_of_le hη' h3.2.2.2.1 h3.1 le_top
  have hc : Continuous η' := by
    have hc' := hη'.2.1
    simp only [le_top, ofPred_true] at hc'
    exact continuousOn_univ.1 hc'
  rw [heq] at h4 ⊢
  exact ⟨hζ, hc, hinj, hη'.1, hH, h4.2.2⟩

end Regular

/-! ### The closed-side order through dyadic codes -/

section Codes

/-- The Borel set of pairs of codes `(q₁, q₂)` of continuous paths, the first tending to `∞`, such that every
dyadic value of the second is in the closed left side of the first (`Theorem15D5.mem_closedLeftSide_decC_iff`). -/
def orderCodeSet : Set (CCode × CCode) :=
  {x | GoodAll x.1 ∧ PropC x.1 ∧ GoodAll x.2 ∧ ∀ n k, x.2 n k ∈ closure (range (seedFamily x.1)) ∨
    ∃ j, Reach (closure (range (seedFamily x.1)))ᶜ (x.1 0 0 - 1 - Complex.I) j (x.2 n k)}

theorem measurableSet_orderCodeSet : MeasurableSet orderCodeSet := by
  have m1 : Measurable fun x : CCode × CCode => x.1 := measurable_fst
  have m2 : Measurable fun x : CCode × CCode => x.2 := measurable_snd
  have hc1 : ∀ n k, Measurable fun x : CCode × CCode => x.1 n k := fun n k => (measurable_coord n k).comp m1
  have hc2 : ∀ n k, Measurable fun x : CCode × CCode => x.2 n k := fun n k => (measurable_coord n k).comp m2
  have hfam : ∀ i, Measurable fun x : CCode × CCode => seedFamily x.1 i := measurable_seedFamily hc1
  have hw : Measurable fun x : CCode × CCode => x.1 0 0 - 1 - Complex.I :=
    ((hc1 0 0).sub measurable_const).sub measurable_const
  refine measurableSet_setOfPred.mpr ?_
  refine (measurable_goodAll.comp m1).and <| (measurable_propC.comp m1).and <| (measurable_goodAll.comp m2).and ?_
  refine Measurable.forall fun n => Measurable.forall fun k => ?_
  exact (measurableSet_setOfPred.mp (measurableSet_mem_closure_range hfam (hc2 n k))).or
    (Measurable.exists fun j => measurableSet_setOfPred.mp (measurableSet_reach hfam hw j (hc2 n k)))

/-- For a continuous path `α` tending to `∞` and a continuous path `β`, the code of `(α, β)` is in `orderCodeSet`
iff `β` lies in the closed left side of `α`. -/
theorem mem_orderCodeSet_iff {α β : ℝ≥0 → ℂ} (hα : Continuous α) (hαT : Tendsto (fun t => ‖α t‖) atTop atTop)
    (hβ : Continuous β) : (encC α, encC β) ∈ orderCodeSet ↔ range β ⊆ closedLeftSide α := by
  have g₁ := goodAll_encC hα
  have g₂ := goodAll_encC hβ
  have e₁ := decC_encC_of_continuous hα
  have e₂ := decC_encC_of_continuous hβ
  have p₁ : PropC (encC α) := (tendsto_norm_iff_propC g₁).1 (by rw [e₁]; exact hαT)
  have key : range β ⊆ closedLeftSide α ↔ ∀ n k, encC β n k ∈ closedLeftSide (decC (encC α)) := by
    rw [← range_subset_closedLeftSide_iff g₁ p₁ g₂, e₁, e₂]
  rw [key]
  constructor
  · rintro ⟨-, -, -, h⟩ n k
    exact (mem_closedLeftSide_decC_iff g₁ p₁ _).2 (h n k)
  · intro h
    exact ⟨g₁, p₁, g₂, fun n k => (mem_closedLeftSide_decC_iff g₁ p₁ _).1 (h n k)⟩

/-- The code map is measurable. -/
theorem measurable_encC_comp {X : Type*} [MeasurableSpace X] {g : X → ℝ≥0 → ℂ}
    (hg : ∀ t, Measurable fun x => g x t) : Measurable fun x => encC (g x) :=
  Measurable.of_eval fun n => Measurable.of_eval fun k => hg (Sec2.Assembly.dyad n k)

end Codes

/-! ### Transfer of the order between fields with the same law -/

section Law

variable {F : Type*} [MeasurableSpace F] {Φ₁ Φ₂ : F → ℝ≥0∞ × (ℝ≥0 → ℂ)}

/-- **The closed-side order of two Borel functions of the field transfers along the field law.** Let `Φ₁`, `Φ₂` be
measurable maps from the field space to (lifetime, path). If, for a field `h₀`, almost surely the path `(Φ₁ h₀).2` is
continuous and tends to `∞`, `(Φ₂ h₀).2` is continuous and lies in its closed left side, and a field `h` has the same
law, then the same order holds almost surely for `h` wherever its two paths are continuous and the first tends to
`∞`. -/
theorem ae_range_subset_closedLeftSide_of_map_eq (hΦ₁ : Measurable Φ₁) (hΦ₂ : Measurable Φ₂)
    {Ω Ω₀ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀] {P : Measure Ω} {P₀ : Measure Ω₀}
    {h : Ω → F} {h₀ : Ω₀ → F} (hhm : Measurable h) (hh₀m : Measurable h₀) (hlaw : P.map h = P₀.map h₀)
    (href : ∀ᵐ ω₀ ∂P₀, Continuous (Φ₁ (h₀ ω₀)).2 ∧ Tendsto (fun t => ‖(Φ₁ (h₀ ω₀)).2 t‖) atTop atTop ∧
      Continuous (Φ₂ (h₀ ω₀)).2 ∧ range (Φ₂ (h₀ ω₀)).2 ⊆ closedLeftSide (Φ₁ (h₀ ω₀)).2)
    (hreg : ∀ᵐ ω ∂P, Continuous (Φ₁ (h ω)).2 ∧ Tendsto (fun t => ‖(Φ₁ (h ω)).2 t‖) atTop atTop ∧
      Continuous (Φ₂ (h ω)).2) :
    ∀ᵐ ω ∂P, range (Φ₂ (h ω)).2 ⊆ closedLeftSide (Φ₁ (h ω)).2 := by
  set c : F → CCode × CCode := fun f => (encC (Φ₁ f).2, encC (Φ₂ f).2) with hc
  have hcm : Measurable c :=
    (measurable_encC_comp fun t => (measurable_pi_apply t).comp (measurable_snd.comp hΦ₁)).prodMk
      (measurable_encC_comp fun t => (measurable_pi_apply t).comp (measurable_snd.comp hΦ₂))
  set G : Set F := c ⁻¹' orderCodeSet with hG
  have hGm : MeasurableSet G := hcm measurableSet_orderCodeSet
  have h₀G : ∀ᵐ ω₀ ∂P₀, h₀ ω₀ ∈ G := by
    filter_upwards [href] with ω₀ hω
    exact (mem_orderCodeSet_iff hω.1 hω.2.1 hω.2.2.1).2 hω.2.2.2
  have hμG : ∀ᵐ f ∂(P₀.map h₀), f ∈ G := (ae_map_iff hh₀m.aemeasurable hGm).2 h₀G
  rw [← hlaw] at hμG
  have hG' : ∀ᵐ ω ∂P, h ω ∈ G := (ae_map_iff hhm.aemeasurable hGm).1 hμG
  filter_upwards [hG', hreg] with ω hω hr
  exact (mem_orderCodeSet_iff hr.1 hr.2.1 hr.2.2).1 hω

end Law

/-! ### Proposition 5.5 in `ℍ` -/

section Assembly

open Sec7 (prop74Data)

/-- **The strict-side order gives the frozen order, almost surely, in every coupling** (regularity and the planar
step). For `0 < κ < 4`, the data of Figure 7.1 and angles `θ₁ < θ₂` with the bounds (5.2), if in some coupling of the
GFF with its two flow lines almost surely no point of `η_{θ₁}` is strictly on the left of `η_{θ₂}`, then almost surely
both lifetimes are infinite and `η_{θ₂}` lies in the closed left side of `η_{θ₁}`. -/
theorem ae_range_subset_closedLeftSide_of_liesRightOf {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {a b θ₁ θ₂ : ℝ}
    (h12 : θ₁ < θ₂) (hb : sleLambda κ - θ₁ * chiC κ ≤ b) (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ (prop74Data a b) {0} 0 θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ (prop74Data a b) {0} 0 θ₂ P h η₂ ζ₂)
    (hlies : ∀ᵐ ω ∂P, LiesRightOf (range (η₁ ω)) (range (η₂ ω))) :
    ∀ᵐ ω ∂P, ζ₁ ω = ⊤ ∧ ζ₂ ω = ⊤ ∧ IsSeedProper (η₁ ω) ∧ IsSeedProper (η₂ ω) ∧
      range (η₂ ω) ⊆ closedLeftSide (η₁ ω) := by
  have hχ := Sec4.chiC_pos hκ hκ4
  have hπχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le hχ.le
  have hb41 : sleLambda κ - π * chiC κ - θ₁ * chiC κ ≤ b := by linarith
  have hbpc := Sec7.isPiecewiseConstant_prop74Data a b
  obtain ⟨hL₁, hR₁⟩ := Sec7.Lemma71G.prop74Data_remark41 hκ hκ4 le_rfl h12.le ha hb41
  obtain ⟨hL₂, hR₂⟩ := Sec7.Lemma71G.prop74Data_remark41 hκ hκ4 h12.le le_rfl ha hb41
  filter_upwards [IsFlowLine.ae_isSeedProper hκ hκ4.le hbpc hL₁ hR₁ hη₁,
    IsFlowLine.ae_isSeedProper hκ hκ4.le hbpc hL₂ hR₂ hη₂, hlies] with ω r₁ r₂ hl
  exact ⟨r₁.1, r₂.1, r₁.2, r₂.2, range_subset_closedLeftSide_of_liesRightOf r₁.2 r₂.2 hl⟩

/-- **Proposition 5.5 in `ℍ`, strict-side form, every coupling** (the form the proof of Proposition 5.5 produces:
"`η_{θ₁}` is contained in the left boundary of `η′_{θ₁}`", which passes to the right of `η_{θ₂}`). Named statement. -/
def Prop55HalfStrictStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ a b θ₁ θ₂ : ℝ, θ₁ < θ₂ →
    sleLambda κ - θ₁ * chiC κ ≤ b → sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h (prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ) →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ (prop74Data a b) {0} 0 θ₁ P h η₁ ζ₁ → IsFlowLine κ (prop74Data a b) {0} 0 θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, LiesRightOf (range (η₁ ω)) (range (η₂ ω))

/-- `Prop55HalfPlaneStatement` (frozen W0 order, every coupling) from the strict-side form (every coupling). -/
theorem prop55HalfPlaneStatement_of_strict (h55 : Prop55HalfStrictStatement.{u}) :
    Sec7.Lemma71H.Prop55HalfPlaneStatement.{u} := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 hb ha Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  filter_upwards [ae_range_subset_closedLeftSide_of_liesRightOf hκ hκ4 h12 hb ha hη₁ hη₂
    (h55 κ hκ hκ4 a b θ₁ θ₂ h12 hb ha P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂)] with ω hω _ _
  exact hω.2.2.2.2

/-- **Named input: Proposition 5.5 in `ℍ` for one coupling** (specification p. 135, proof of Proposition 5.5: the
order is proved for the flow lines of `h` coupled with the counterflow line `η′_{θ₁}`). For `0 < κ < 4`, the data of
Figure 7.1 (`−a` on `ℝ₋`, `b` on `ℝ₊`) and angles `θ₁ < θ₂` with the bounds (5.2), **some** probability space carries a
GFF `h` with these data and two flow lines `η_{θ₁}`, `η_{θ₂}` of `h` from `0` such that almost surely no point of
`η_{θ₁}` is strictly on the left of `η_{θ₂}`. Not proved here (see `planning/handoffs/PROVE-SEC5-K.md`). -/
def Prop55HalfExistsStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ a b θ₁ θ₂ : ℝ, θ₁ < θ₂ →
    sleLambda κ - θ₁ * chiC κ ≤ b → sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a →
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (h : Ω → DistOn upperHalfPlaneOpens) (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsGFFWithBoundaryData P h (prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ) ∧
      IsFlowLine κ (prop74Data a b) {0} 0 θ₁ P h η₁ ζ₁ ∧ IsFlowLine κ (prop74Data a b) {0} 0 θ₂ P h η₂ ζ₂ ∧
      ∀ᵐ ω ∂P, LiesRightOf (range (η₁ ω)) (range (η₂ ω))

/-- **Proposition 5.5 in `ℍ` (the consumer's form) from one coupling and the §4.2 reference.** Both flow words
satisfy (4.4), so the reference gives Borel maps `Φ₁`, `Φ₂` of the field with `η_{θᵢ} = Φᵢ(h)` in every coupling
(Aux. lemma 23); in the given coupling the closed-side order holds almost surely (strict-side order, regularity, planar
step), so it holds for `μ`-almost every field `f` on the Borel good set of codes, and hence in every coupling. -/
theorem prop55HalfPlaneStatement_of_exists (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u})
    (hex : Prop55HalfExistsStatement.{u}) : Sec7.Lemma71H.Prop55HalfPlaneStatement.{u} := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 hb ha Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  have hχ := Sec4.chiC_pos hκ hκ4
  have h12χ : θ₁ * chiC κ < θ₂ * chiC κ := mul_lt_mul_of_pos_right h12 hχ
  have hF := Theorem15.isOrderedForceWord_flowLine (prop74Data a b) {0} 0
  have hbpc := Sec7.isPiecewiseConstant_prop74Data a b
  -- the two flow-line maps (Aux. lemma 23 and the §4.2 reference)
  have h44₁ := Sec7.Lemma71H.cond44_flowLine_prop74Data (θ := θ₁) hκ (a := a) (b := b) (by linarith) hb
  have h44₂ := Sec7.Lemma71H.cond44_flowLine_prop74Data (θ := θ₂) hκ (a := a) (b := b) ha (by linarith)
  obtain ⟨Φ₁, hΦ₁m, hΦ₁⟩ := Lemma75Bridge.exists_flowLineMap_of_admissible hκ hκ4.le
    (Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44₁) (href κ hκ hκ4 _ _ _ _ hF h44₁)
  obtain ⟨Φ₂, hΦ₂m, hΦ₂⟩ := Lemma75Bridge.exists_flowLineMap_of_admissible hκ hκ4.le
    (Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44₂) (href κ hκ hκ4 _ _ _ _ hF h44₂)
  -- the coupling of the named input
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, h₀, α₀, β₀, ζα, ζβ, hh₀, hα₀, hβ₀, hlies⟩ := hex κ hκ hκ4 a b θ₁ θ₂ h12 hb ha
  -- the two fields have the same law
  obtain ⟨u, hu, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hbpc
  have hlaw : P.map h = P₀.map h₀ := Exist.map_eq_of_isGFFWithBoundaryData hh hh₀ hu
  -- the order on the reference space, read through the maps
  have href' : ∀ᵐ ω₀ ∂P₀, Continuous (Φ₁ (h₀ ω₀)).2 ∧ Tendsto (fun t => ‖(Φ₁ (h₀ ω₀)).2 t‖) atTop atTop ∧
      Continuous (Φ₂ (h₀ ω₀)).2 ∧ range (Φ₂ (h₀ ω₀)).2 ⊆ closedLeftSide (Φ₁ (h₀ ω₀)).2 := by
    filter_upwards [ae_range_subset_closedLeftSide_of_liesRightOf hκ hκ4 h12 hb ha hα₀ hβ₀ hlies,
      hΦ₁ P₀ h₀ hh₀ α₀ ζα hα₀, hΦ₂ P₀ h₀ hh₀ β₀ ζβ hβ₀] with ω₀ hω e₁ e₂
    obtain ⟨hζα, hζβ, pα, pβ, hord⟩ := hω
    have f₁ : (Φ₁ (h₀ ω₀)).2 = α₀ ω₀ := funext fun t => e₁.2 t (by rw [hζα]; exact le_top)
    have f₂ : (Φ₂ (h₀ ω₀)).2 = β₀ ω₀ := funext fun t => e₂.2 t (by rw [hζβ]; exact le_top)
    rw [f₁, f₂]
    exact ⟨pα.1, pα.2.2.2.2, pβ.1, hord⟩
  -- regularity on the given space, read through the maps
  have hχ' := hχ
  have hπχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le hχ'.le
  have hb41 : sleLambda κ - π * chiC κ - θ₁ * chiC κ ≤ b := by linarith
  obtain ⟨hL₁, hR₁⟩ := Sec7.Lemma71G.prop74Data_remark41 hκ hκ4 le_rfl h12.le ha hb41
  obtain ⟨hL₂, hR₂⟩ := Sec7.Lemma71G.prop74Data_remark41 hκ hκ4 h12.le le_rfl ha hb41
  have r₁ := IsFlowLine.ae_isSeedProper hκ hκ4.le hbpc hL₁ hR₁ hη₁
  have r₂ := IsFlowLine.ae_isSeedProper hκ hκ4.le hbpc hL₂ hR₂ hη₂
  have m₁ := hΦ₁ P h hh η₁ ζ₁ hη₁
  have m₂ := hΦ₂ P h hh η₂ ζ₂ hη₂
  have hmaps : ∀ᵐ ω ∂P, (Φ₁ (h ω)).2 = η₁ ω ∧ (Φ₂ (h ω)).2 = η₂ ω := by
    filter_upwards [r₁, r₂, m₁, m₂] with ω a₁ a₂ e₁ e₂
    exact ⟨funext fun t => e₁.2 t (by rw [a₁.1]; exact le_top),
      funext fun t => e₂.2 t (by rw [a₂.1]; exact le_top)⟩
  have hreg : ∀ᵐ ω ∂P, Continuous (Φ₁ (h ω)).2 ∧ Tendsto (fun t => ‖(Φ₁ (h ω)).2 t‖) atTop atTop ∧
      Continuous (Φ₂ (h ω)).2 := by
    filter_upwards [r₁, r₂, hmaps] with ω a₁ a₂ e
    rw [e.1, e.2]
    exact ⟨a₁.2.1, a₁.2.2.2.2.2, a₂.2.1⟩
  have hord := ae_range_subset_closedLeftSide_of_map_eq hΦ₁m hΦ₂m hh.1 hh₀.1 hlaw href' hreg
  filter_upwards [hord, hmaps] with ω hω e _ _
  rw [e.1, e.2] at hω
  exact hω

end Assembly

/-! ### Conditional independence from determination -/

section CondIndep

open Sec7 (prop74Data)

/-- **Under the §4.2 reference, a flow line of the Figure 7.1 field is conditionally independent of every process
given the field** (the hypothesis of Proposition 5.1, Lemma 5.4 and Lemma 5.7 in the form of
`Prop51CondIndepStatement`): its word satisfies (4.4), so it is almost surely a Borel function of the field
(`Lemma75Bridge.exists_flowLineMap_of_admissible`), with infinite lifetime (Remark 4.1's regime), and
`CondDet.condIndep_iSup_of_ae_eq_comp` applies. -/
theorem IsFlowLine.condIndep_of_cond44 (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) {Ω' : Type u}
    {m₂ : MeasurableSpace Ω'}
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {a b θ : ℝ} (ha : sleLambda κ - π * chiC κ + θ * chiC κ ≤ a)
    (hb : sleLambda κ - θ * chiC κ ≤ b) [mΩ : MeasurableSpace Ω'] [StandardBorelSpace Ω'] {P : Measure Ω'}
    [IsProbabilityMeasure P] {h : Ω' → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h (prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ)) {η : Ω' → ℝ≥0 → ℂ}
    {ζ : Ω' → ℝ≥0∞} (hη : IsFlowLine κ (prop74Data a b) {0} 0 θ P h η ζ) (hηm : ∀ t, Measurable fun ω => η ω t)
    (hm₂ : m₂ ≤ mΩ) :
    CondIndep (MeasurableSpace.comap h inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (fun ω => η ω t) inferInstance) m₂ hh.1.comap_le P := by
  have hχ := Sec4.chiC_pos hκ hκ4
  have hπχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le hχ.le
  have hF := Theorem15.isOrderedForceWord_flowLine (prop74Data a b) {0} 0
  have hbpc := Sec7.isPiecewiseConstant_prop74Data a b
  have h44 := Sec7.Lemma71H.cond44_flowLine_prop74Data (θ := θ) hκ (a := a) (b := b) ha hb
  obtain ⟨Φ, hΦm, hΦ⟩ := Lemma75Bridge.exists_flowLineMap_of_admissible hκ hκ4.le
    (Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44) (href κ hκ hκ4 _ _ _ _ hF h44)
  have hb41 : sleLambda κ - π * chiC κ - θ * chiC κ ≤ b := by linarith
  obtain ⟨hL, hR⟩ := Sec7.Lemma71G.prop74Data_remark41 hκ hκ4 le_rfl le_rfl ha hb41
  have hreg := IsFlowLine.ae_isSeedProper hκ hκ4.le hbpc hL hR hη
  have hmap := hΦ P h hh η ζ hη
  refine CondDet.condIndep_iSup_of_ae_eq_comp hh.1 hηm
    (Φ := fun t f => (Φ f).2 t) (fun t => (measurable_pi_apply t).comp (measurable_snd.comp hΦm)) (fun t => ?_) hm₂
  filter_upwards [hreg, hmap] with ω h1 h2
  exact (h2.2 t (by rw [h1.1]; exact le_top)).symm

end CondIndep

/-! ### The half-plane case is the Figure 5.1 case in Lemma 4.5's chart `Q` -/

section ChartQ

open Sec7 (prop74Data)
open Sec4 (stripQHData)

/-- **The data of Figure 7.1 are Figure 5.1 data read in the chart `Q`** (`z₀ ↦ ∞`, Lemma 4.5): for `q = e^{πx₀}` and
`y ∉ {−1/q, 0, 1}` (the images of the strip ends and of the seed), the `Q`-transported data of the strip data
`−a | b` (lower) and `−(a + πχ) | b + πχ` (upper, jump at `z₀`) are `prop74Data a b`. So for the half-plane case of
Proposition 5.5 the upper data are `a′ = a + πχ`, `b′ = b + πχ` and no change of the upper data (the specification's
appeal to Proposition 3.4) is needed; see `prop55_convenient_of_eq52` for the bounds. -/
theorem stripQHData_prop74Data {κ a b x₀ y : ℝ} (hy₁ : y ≠ -(1 / Real.exp (π * x₀))) (hy₀ : y ≠ 0)
    (hy₂ : y ≠ 1) :
    stripQHData κ (Real.exp (π * x₀)) (fig51Lower a b) (fig51Upper x₀ (a + π * chiC κ) (b + π * chiC κ)) y =
      prop74Data a b y := by
  set q := Real.exp (π * x₀) with hq_def
  have hq : 0 < q := Real.exp_pos _
  have hπ := Real.pi_pos
  rcases lt_or_gt_of_ne hy₁ with hlt | hgt
  · -- upper line, left of `z₀`
    rw [Sec4.stripQHData_of_lt hlt]
    have hpos := Sec4.stripQ_upper_left_pos hq hlt
    have hy1' : y - 1 < 0 := by linarith [Sec4.neg_one_div_neg hq]
    have hexp : Real.exp (π * (Real.log ((q * y + 1) / (y - 1)) / π)) < Real.exp (π * x₀) := by
      rw [mul_div_cancel₀ _ hπ.ne', Real.exp_log hpos, ← hq_def, div_lt_iff_of_neg hy1']
      linarith
    have hx : Real.log ((q * y + 1) / (y - 1)) / π < x₀ := Sec4.exp_lt_exp_mul_pi_iff.1 hexp
    have hy0 : y < 0 := hlt.trans (Sec4.neg_one_div_neg hq)
    simp only [fig51Upper, hx, ↓reduceIte, prop74Data, hy0]
    ring
  · rcases lt_or_gt_of_ne hy₂ with hlt1 | hgt1
    · -- lower line
      rw [Sec4.stripQHData_of_mem hgt hlt1]
      have hqy : 0 < 1 + q * y := by linarith [(Sec4.neg_one_lt_mul_iff hq).1 hgt]
      have hd : 0 < 1 - y := by linarith
      rcases lt_or_gt_of_ne hy₀ with hneg | hposy
      · have hlt1' : (1 + q * y) / (1 - y) < 1 := by
          rw [div_lt_one hd]; linarith [mul_neg_of_pos_of_neg hq hneg]
        have hx0 : Real.log ((1 + q * y) / (1 - y)) / π < 0 :=
          div_neg_of_neg_of_pos (Real.log_neg (div_pos hqy hd) hlt1') hπ
        simp only [fig51Lower, hx0, ↓reduceIte, prop74Data, hneg]
      · have hgt1' : 1 < (1 + q * y) / (1 - y) := by
          rw [one_lt_div hd]; linarith [mul_pos hq hposy]
        have hx0 : 0 < Real.log ((1 + q * y) / (1 - y)) / π := div_pos (Real.log_pos hgt1') hπ
        simp only [fig51Lower, not_lt.2 hx0.le, ↓reduceIte, prop74Data, not_lt.2 hposy.le]
    · -- upper line, right of `z₀`
      rw [Sec4.stripQHData_of_gt hq hgt1]
      have hpos := Sec4.stripQ_upper_right_pos hq hgt1
      have hy1' : 0 < y - 1 := by linarith
      have hexp : Real.exp (π * x₀) < Real.exp (π * (Real.log ((q * y + 1) / (y - 1)) / π)) := by
        rw [mul_div_cancel₀ _ hπ.ne', Real.exp_log hpos, ← hq_def, lt_div_iff₀ hy1']
        linarith
      have hx : x₀ < Real.log ((q * y + 1) / (y - 1)) / π := Sec4.exp_lt_exp_mul_pi_iff.1 hexp
      have hy0 : ¬ y < 0 := not_lt.2 (by linarith)
      simp only [fig51Upper, not_lt.2 hx.le, ↓reduceIte, prop74Data, hy0]
      ring

/-- **Under (5.2), the upper data `a′ = a + πχ`, `b′ = b + πχ` are the convenient upper data of the proof of
Proposition 5.5** (`a′ ≥ λ′ + (θ₁ + π/2)χ`, `b′ ≥ λ′ + (3π/2 − θ₁)χ`, `λ′ = λ(16/κ) = λ − πχ/2`), and the lower
bounds `(λ − b)/χ ≤ θ₁ < θ₂ ≤ (a + πχ − λ)/χ` of `prop55_of_prop51CondIndep` hold. -/
theorem prop55_convenient_of_eq52 {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {a b θ₁ θ₂ : ℝ}
    (hb : sleLambda κ - θ₁ * chiC κ ≤ b) (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a) (h12 : θ₁ < θ₂) :
    (sleLambda κ - b) / chiC κ ≤ θ₁ ∧ θ₂ ≤ (a + π * chiC κ - sleLambda κ) / chiC κ ∧
      sleLambda (16 / κ) + (θ₁ + π / 2) * chiC κ ≤ a + π * chiC κ ∧
      sleLambda (16 / κ) + (3 * π / 2 - θ₁) * chiC κ ≤ b + π * chiC κ := by
  have hχ := Sec4.chiC_pos hκ hκ4
  have hlam := Sec4.sleLambda_sixteen_div_eq_sub hκ
  have h12χ : θ₁ * chiC κ < θ₂ * chiC κ := mul_lt_mul_of_pos_right h12 hχ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hχ]; linarith
  · rw [le_div_iff₀ hχ]; linarith
  · rw [hlam]; nlinarith
  · rw [hlam]; nlinarith

end ChartQ

end Prop55Half

end Sec5

end InteractingSLE
