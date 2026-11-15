/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71Four
import InteractingSLE.Spec.Sec7.Lemma72BMain
import InteractingSLE.Spec.Sec7.Lemma613
import InteractingSLE.Spec.Sec7.Prop74ProofWord
import InteractingSLE.Spec.Sec7.StripSysField

/-!
# Proposition 7.4's pocket: the angle shift from the four-curve space to two three-curve spaces

Packet PROVE-PROP74B, item (c) (`planning/handoffs/PROVE-PROP74.md`, "How to discharge it"). Specification §7.1 setup
(p. 221: "`η_{θ_i}` is the flow line of `h + θ_iχ`") and p. 243 ("Applying the same component-pair construction
simultaneously to finitely many middle flow lines").

On the four-curve space (`Lemma71Four.IsFourCurveSpace`: outer flow lines `β = η_{α₂}`, `α = η_{α₁}` and middle flow
lines `γᵢ = η_{θᵢ}` of a GFF `h` with the data `(A, B)` of Figure 7.1), the middle curve `γᵢ` is the zero-angle flow
line of the shifted field `h + θᵢχ` (`Exist.flowField 0 (θᵢχ) h`), whose data are `(A − θᵢχ, B + θᵢχ)`, and the outer
curves are its flow lines with the angles `α₂ − θᵢ > 0` and `α₁ − θᵢ < 0`. So `(h + θᵢχ, β, α, γᵢ)` is a three-curve
space (`Lemma72B.IsThreeCurveSpace`), the object of Lemma 7.1's one-middle-curve construction.

## Main results

* `flowField_zero_apply`, `isTranslateAddConst_zero_iff`, `flowField_zero_flowField_zero`: the constant shift `h + c`;
* `isBoundedHarmonicExtension_shift`, `isGFFWithBoundaryData_shift`, `centredField_shift`: the shift moves the data
  `(A, B)` to `(A − c, B + c)` and keeps the centred field;
* **`isFlowLine_shift_iff`**: the angle-`θ` flow line of `h` is the angle-`(θ − θ₀)` flow line of `h + θ₀χ`;
* `IsFlowLine.isGFFWithBoundaryData_zero`: the field of an angle-`0` flow line with data `prop74Data a b` is a GFF with
  these data;
* **`isThreeCurveSpace_shift`**, `isThreeCurveSpace_one`, `isThreeCurveSpace_two`: the two three-curve spaces of the
  four-curve space (Lemma 6.13's exclusion (MD1) from `Lemma613.lemma613ContactStatement_of_prop55`).

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Real
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec7.Prop74B

open Sec5.Prop55Half

/-! ### The constant shift of a field -/

/-- `Exist.flowField 0 c h` is `h + c`. -/
theorem flowField_zero_apply (c : ℝ) (h : DistOn upperHalfPlaneOpens) (φ : TestOn upperHalfPlaneOpens) :
    Exist.flowField 0 c h φ = h φ + c * ∫ w, φ w := by
  rw [Exist.flowField_apply]
  congr 2
  ext z
  rw [Exist.pushTest_shiftChart_apply, Complex.ofReal_zero, sub_zero]

/-- The frozen `IsTranslateAddConst` with translation `0`: `h' = h + c`. -/
theorem isTranslateAddConst_zero_iff {c : ℝ} {h h' : DistOn upperHalfPlaneOpens} :
    IsTranslateAddConst 0 c h h' ↔ ∀ φ : TestOn upperHalfPlaneOpens, h' φ = h φ + c * ∫ w, φ w := by
  constructor
  · intro ht φ
    exact ht φ φ fun z => by rw [Complex.ofReal_zero, add_zero]
  · intro ht φ φ' hφ
    have e : φ' = φ := by
      ext z
      rw [hφ z, Complex.ofReal_zero, add_zero]
    rw [e]
    exact ht φ

theorem flowField_zero_flowField_zero (c₁ c₂ : ℝ) (h : DistOn upperHalfPlaneOpens) :
    Exist.flowField 0 c₂ (Exist.flowField 0 c₁ h) = Exist.flowField 0 (c₁ + c₂) h := by
  ext φ
  rw [flowField_zero_apply, flowField_zero_apply, flowField_zero_apply]
  ring

theorem flowField_zero_zero (h : DistOn upperHalfPlaneOpens) : Exist.flowField 0 0 h = h := by
  ext φ
  rw [flowField_zero_apply, zero_mul, add_zero]

/-! ### Shifted data, harmonic extension, GFF and centred field -/

theorem prop74Data_shift (A B c y : ℝ) : prop74Data (A - c) (B + c) y = prop74Data A B y + c := by
  simp only [prop74Data]
  split_ifs <;> ring

/-- The bounded harmonic extension of the shifted data is the shifted extension. -/
theorem isBoundedHarmonicExtension_shift {A B : ℝ} {S : Set ℝ} {u₀ : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (prop74Data A B) S u₀) (c : ℝ) :
    IsBoundedHarmonicExtension (prop74Data (A - c) (B + c)) S (fun z => u₀ z + c) := by
  obtain ⟨hharm, ⟨C, hC⟩, hlim⟩ := hu
  refine ⟨fun z hz => (hharm z hz).add (InnerProductSpace.harmonicAt_const _), ⟨C + |c|, fun z hz => ?_⟩,
    fun x hx => ?_⟩
  · exact (abs_add_le _ _).trans (by linarith [hC z hz])
  · rw [prop74Data_shift]
    exact (hlim x hx).add_const c

/-- **The shifted field `h + c` of a GFF with the data `(A, B)` is a GFF with the data `(A − c, B + c)`.** -/
theorem isGFFWithBoundaryData_shift {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {A B : ℝ} {S : Set ℝ}
    (hh : IsGFFWithBoundaryData P h (prop74Data A B) S) (c : ℝ) :
    IsGFFWithBoundaryData P (fun ω => Exist.flowField 0 c (h ω)) (prop74Data (A - c) (B + c)) S := by
  refine ⟨(Exist.measurable_flowField 0 c).comp hh.1, fun u hu => ?_⟩
  have hu' : IsBoundedHarmonicExtension (prop74Data A B) S (fun z => u z - c) := by
    have h1 := isBoundedHarmonicExtension_shift hu (-c)
    have e1 : A - c - -c = A := by ring
    have e2 : B + c + -c = B := by ring
    rw [e1, e2] at h1
    simpa only [← sub_eq_add_neg] using h1
  have hmi : ∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun w => (fun z => u z - c) (w + ((0 : ℝ) : ℂ)) * φ w) := fun φ =>
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn (S := H)
      (((hu.1.continuousOn).comp (continuousOn_id.add continuousOn_const)
        fun z hz => Exist.add_real_mem_H hz 0).sub continuousOn_const) φ φ.tsupport_subset
  have hX := Exist.isZBGFFProcess_flowField (hh.2 _ hu') 0 c hmi
  have e : ∀ w : ℂ, (fun z => u z - c) (w + ((0 : ℝ) : ℂ)) + c = u w := fun w => by
    simp only [Complex.ofReal_zero, add_zero, sub_add_cancel]
  simp only [e] at hX
  exact hX

/-- The centred field is unchanged by the shift of the field and of its harmonic extension. -/
theorem centredField_shift {Ω : Type*} (h : Ω → DistOn upperHalfPlaneOpens) {u₀ : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u₀ H) (c : ℝ) :
    WholeField.centredField (fun ω => Exist.flowField 0 c (h ω)) (fun z => u₀ z + c) =
      WholeField.centredField h u₀ := by
  funext ω
  ext φ
  have hc₀ : ContinuousOn u₀ H := hu.continuousOn
  have hc₁ : ContinuousOn (fun z => u₀ z + c) H := hc₀.add continuousOn_const
  change Exist.flowField 0 c (h ω) φ -
      SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (fun z => u₀ z + c) φ =
    h ω φ - SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ φ
  rw [SupercriticalConformalCovariance.GM24.smoothDist_apply hc₁,
    SupercriticalConformalCovariance.GM24.smoothDist_apply hc₀, flowField_zero_apply]
  have hi : Integrable (fun x => φ x * u₀ x) := SupercriticalConformalCovariance.GM24.integrable_test_mul hc₀ φ
  have hφi : Integrable (fun x => φ x) := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have e : (fun x => φ x * (u₀ x + c)) = fun x => φ x * u₀ x + c * φ x := by
    funext x
    ring
  rw [e, integral_add hi (hφi.const_mul c), integral_const_mul]
  ring

/-! ### The angle shift of a flow line -/

/-- **The angle shift** (§7.1: "`η_{θ_i}` is the flow line of `h + θ_iχ`"): the angle-`θ` flow line of `h` with the
data `(A, B)` is the angle-`(θ − θ₀)` flow line of `h + θ₀χ`, whose data are `(A − θ₀χ, B + θ₀χ)`. -/
theorem isFlowLine_shift_iff {κ A B θ θ₀ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} :
    IsFlowLine κ (prop74Data A B) {0} 0 θ P h η ζ ↔
      IsFlowLine κ (prop74Data (A - θ₀ * chiC κ) (B + θ₀ * chiC κ)) {0} 0 (θ - θ₀) P
        (fun ω => Exist.flowField 0 (θ₀ * chiC κ) (h ω)) η ζ := by
  rw [isFlowLine_prop74Data_iff, isFlowLine_prop74Data_iff]
  have eA : A - θ₀ * chiC κ - (θ - θ₀) * chiC κ = A - θ * chiC κ := by ring
  have eB : B + θ₀ * chiC κ + (θ - θ₀) * chiC κ = B + θ * chiC κ := by ring
  rw [eA, eB]
  constructor
  · rintro ⟨h', 𝓕, W, VL, VR, B', htr, hc, htrace⟩
    refine ⟨h', 𝓕, W, VL, VR, B', fun ω => isTranslateAddConst_zero_iff.2 fun φ => ?_, hc, htrace⟩
    rw [isTranslateAddConst_zero_iff.1 (htr ω) φ, flowField_zero_apply]
    ring
  · rintro ⟨h', 𝓕, W, VL, VR, B', htr, hc, htrace⟩
    refine ⟨h', 𝓕, W, VL, VR, B', fun ω => isTranslateAddConst_zero_iff.2 fun φ => ?_, hc, htrace⟩
    rw [isTranslateAddConst_zero_iff.1 (htr ω) φ, flowField_zero_apply]
    ring

/-- **The field of an angle-`0` flow line from `0` with the data `prop74Data a b` is a GFF with these data** (the
field clause of the frozen `IsOptionalHullCoupling`, through `StripSysField.isGFFWithBoundaryData_of_flowLineGFF`). -/
theorem IsFlowLine.isGFFWithBoundaryData_zero {κ a b : ℝ} (hκ : 0 < κ) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLine κ (prop74Data a b) {0} 0 0 P X η ζ) :
    IsGFFWithBoundaryData P X (prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ) := by
  obtain ⟨h', 𝓕, W, VL, VR, B, htr, hc, _⟩ := hfl
  have e : h' = X := funext fun ω => by
    have h1 := htr ω
    rw [zero_mul] at h1
    exact Sec5.Markov.eq_of_isTranslateAddConst_zero h1
  have hG := StripSysField.isGFFWithBoundaryData_of_flowLineGFF hκ (isPiecewiseConstant_prop74Data a b)
    (P := P) (h := h') ⟨hc.2.1, hc.2.2.1⟩
  rwa [e] at hG

/-! ### The three-curve spaces of the four-curve space -/

/-- A simple proper curve from `0` misses every nonzero real point. -/
theorem IsSeedProper.ne_ofReal {γ : ℝ≥0 → ℂ} (hγ : IsSeedProper γ) (t : ℝ≥0) {x : ℝ} (hx : x ≠ 0) :
    γ t ≠ x := by
  rcases eq_zero_or_pos t with ht | ht
  · rw [ht, hγ.2.2.1]
    exact fun h => hx (Complex.ofReal_eq_zero.1 h.symm)
  · intro h
    have him : 0 < (γ t).im := hγ.2.2.2.1 t ht
    rw [h, Complex.ofReal_im] at him
    exact lt_irrefl _ him

/-- **The three-curve space of one middle curve of a four-curve configuration** (packet item (c)). Let `β`, `γ`, `α`
be the flow lines of `h` with the angles `α₂ > θ > α₁` (data `(A, B)` with (5.2) for the outer pair), with Lemma 6.2's
hypotheses for the centred field, almost surely complete simple proper curves from `0` in the order `β ≤ γ ≤ α`. Then
`(h + θχ, β, α, γ)` is a three-curve space with the angles `α₁ − θ < 0 < α₂ − θ` and the data `(A − θχ, B + θχ)`.
The exclusion of (MD1) is `Lemma613.lemma613ContactStatement_of_prop55`, applied to the pairs `(α₁, θ)` and
`(θ, α₂)` of the original field. -/
theorem isThreeCurveSpace_shift (href : Lemma71H.Cond44ReferenceStatement.{u})
    (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) {κ α₁ θ α₂ A B : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (h1 : α₁ < θ) (h2 : θ < α₂) (hA : sleLambda κ - π * chiC κ + α₂ * chiC κ ≤ A)
    (hB : sleLambda κ - α₁ * chiC κ ≤ B) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β γ α : Ω → ℝ≥0 → ℂ}
    {ζβ ζγ ζα : Ω → ℝ≥0∞}
    (hh : IsGFFWithBoundaryData P h (prop74Data A B) ((({0} : Finset ℝ)) : Set ℝ))
    (hu₀ : IsBoundedHarmonicExtension (prop74Data A B) ((({0} : Finset ℝ)) : Set ℝ) u₀)
    (hz : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (hβf : IsFlowLine κ (prop74Data A B) {0} 0 α₂ P h β ζβ)
    (hγf : IsFlowLine κ (prop74Data A B) {0} 0 θ P h γ ζγ)
    (hαf : IsFlowLine κ (prop74Data A B) {0} 0 α₁ P h α ζα)
    (hβ : Lemma71G.IsLemma62Curve β (WholeField.centredField h u₀) P)
    (hγ : Lemma71G.IsLemma62Curve γ (WholeField.centredField h u₀) P)
    (hα : Lemma71G.IsLemma62Curve α (WholeField.centredField h u₀) P)
    (hae : ∀ᵐ ω ∂P, ζβ ω = ⊤ ∧ ζγ ω = ⊤ ∧ ζα ω = ⊤ ∧ IsSeedProper (β ω) ∧ IsSeedProper (γ ω) ∧
      IsSeedProper (α ω) ∧ range (β ω) ⊆ closedLeftSide (γ ω) ∧ range (γ ω) ⊆ closedLeftSide (α ω) ∧
      range (β ω) ⊆ closedLeftSide (α ω)) :
    Lemma72B.IsThreeCurveSpace κ (α₁ - θ) (α₂ - θ) (A - θ * chiC κ) (B + θ * chiC κ) P
      (fun ω => Exist.flowField 0 (θ * chiC κ) (h ω)) (fun z => u₀ z + θ * chiC κ) β α γ ζβ ζα ζγ := by
  have hχ := Sec4.chiC_pos hκ hκ4
  have hMD := Lemma613.lemma613ContactStatement_of_prop55 href h55
  have hθA : sleLambda κ - π * chiC κ + θ * chiC κ ≤ A := by nlinarith
  have hθB : sleLambda κ - θ * chiC κ ≤ B := by nlinarith
  have n1 := hMD κ hκ hκ4 A B α₁ θ h1 hB hθA P h hh α γ ζα ζγ hαf hγf
  have n2 := hMD κ hκ hκ4 A B θ α₂ h2 hθB hA P h hh γ β ζγ ζβ hγf hβf
  have hcf := centredField_shift h hu₀.1 (θ * chiC κ)
  have hγ0 := (isFlowLine_shift_iff (θ₀ := θ)).1 hγf
  rw [sub_self] at hγ0
  refine ⟨isGFFWithBoundaryData_shift hh _, isBoundedHarmonicExtension_shift hu₀ _, hcf ▸ hz,
    (isFlowLine_shift_iff (θ₀ := θ)).1 hβf,
    (isFlowLine_shift_iff (θ₀ := θ)).1 hαf, hγ0, hcf ▸ hβ, hcf ▸ hα, hcf ▸ hγ, ?_⟩
  filter_upwards [hae, n1, n2] with ω hω hn1 hn2
  obtain ⟨zβ, zγ, zα, pβ, pγ, pα, oβγ, oγα, oβα⟩ := hω
  refine ⟨zβ, zα, zγ, fun i t x hx => ?_, oβγ, oγα, oβα, pβ, pα, pγ,
    Lemma71I.isOrderedArcs_of_closedLeftSide pβ pα pγ oγα oβγ, (hn1 zα zγ).2, (hn2 zγ zβ).1⟩
  fin_cases i
  · exact IsSeedProper.ne_ofReal pβ t hx
  · exact IsSeedProper.ne_ofReal pα t hx
  · exact IsSeedProper.ne_ofReal pγ t hx

section Four

variable {κ α₁ θ₁ θ₂ α₂ A B : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β γ₂ γ₁ α : Ω → ℝ≥0 → ℂ} {ζβ ζ₂ ζ₁ ζα : Ω → ℝ≥0∞}

/-- **The three-curve space of the first middle curve** `γ₁ = η_{θ₁}` of a four-curve space: `(h + θ₁χ, β, α, γ₁)`. -/
theorem isThreeCurveSpace_one (href : Lemma71H.Cond44ReferenceStatement.{u})
    (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) (h1 : α₁ < θ₁) (h12 : θ₁ < θ₂)
    (h2 : θ₂ < α₂) (hA : sleLambda κ - π * chiC κ + α₂ * chiC κ ≤ A) (hB : sleLambda κ - α₁ * chiC κ ≤ B)
    (hS : Lemma71Four.IsFourCurveSpace κ α₁ θ₁ θ₂ α₂ A B P h u₀ β γ₂ γ₁ α ζβ ζ₂ ζ₁ ζα) :
    Lemma72B.IsThreeCurveSpace κ (α₁ - θ₁) (α₂ - θ₁) (A - θ₁ * chiC κ) (B + θ₁ * chiC κ) P
      (fun ω => Exist.flowField 0 (θ₁ * chiC κ) (h ω)) (fun z => u₀ z + θ₁ * chiC κ) β α γ₁ ζβ ζα ζ₁ := by
  obtain ⟨hh, hu₀, hz, hβf, _, hγf, hαf, hβ, _, hγ, hα, hae⟩ := hS
  refine isThreeCurveSpace_shift href h55 hκ hκ4 h1 (h12.trans h2) hA hB hh hu₀ hz hβf hγf hαf hβ hγ hα ?_
  filter_upwards [hae] with ω hω
  obtain ⟨zβ, -, z₁, zα, pβ, -, p₁, pα, -, oβ1, oβα, -, -, o1α⟩ := hω
  exact ⟨zβ, z₁, zα, pβ, p₁, pα, oβ1, o1α, oβα⟩

/-- **The three-curve space of the second middle curve** `γ₂ = η_{θ₂}` of a four-curve space: `(h + θ₂χ, β, α, γ₂)`. -/
theorem isThreeCurveSpace_two (href : Lemma71H.Cond44ReferenceStatement.{u})
    (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) (h1 : α₁ < θ₁) (h12 : θ₁ < θ₂)
    (h2 : θ₂ < α₂) (hA : sleLambda κ - π * chiC κ + α₂ * chiC κ ≤ A) (hB : sleLambda κ - α₁ * chiC κ ≤ B)
    (hS : Lemma71Four.IsFourCurveSpace κ α₁ θ₁ θ₂ α₂ A B P h u₀ β γ₂ γ₁ α ζβ ζ₂ ζ₁ ζα) :
    Lemma72B.IsThreeCurveSpace κ (α₁ - θ₂) (α₂ - θ₂) (A - θ₂ * chiC κ) (B + θ₂ * chiC κ) P
      (fun ω => Exist.flowField 0 (θ₂ * chiC κ) (h ω)) (fun z => u₀ z + θ₂ * chiC κ) β α γ₂ ζβ ζα ζ₂ := by
  obtain ⟨hh, hu₀, hz, hβf, hγf, _, hαf, hβ, hγ, _, hα, hae⟩ := hS
  refine isThreeCurveSpace_shift href h55 hκ hκ4 (h1.trans h12) h2 hA hB hh hu₀ hz hβf hγf hαf hβ hγ hα ?_
  filter_upwards [hae] with ω hω
  obtain ⟨zβ, z₂, -, zα, pβ, p₂, -, pα, oβ2, -, oβα, -, o2α, -⟩ := hω
  exact ⟨zβ, z₂, zα, pβ, p₂, pα, oβ2, o2α, oβα⟩

/-- The (5.2) bounds of the shifted three-curve space: the bounds of the outer pair are unchanged by the shift. -/
theorem shift_bounds (θ : ℝ) (hA : sleLambda κ - π * chiC κ + α₂ * chiC κ ≤ A)
    (hB : sleLambda κ - α₁ * chiC κ ≤ B) :
    sleLambda κ - π * chiC κ + (α₂ - θ) * chiC κ ≤ A - θ * chiC κ ∧
      sleLambda κ - (α₁ - θ) * chiC κ ≤ B + θ * chiC κ := by
  constructor <;> nlinarith

end Four

end InteractingSLE.Sec7.Prop74B
