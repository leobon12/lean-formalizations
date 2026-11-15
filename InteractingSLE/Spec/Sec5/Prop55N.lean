/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Cond44Ref
import InteractingSLE.Spec.Sec5.Prop55Half
import InteractingSLE.Spec.Sec7.Lemma71GSpace
import InteractingSLE.Spec.Sec7.Lemma72BMain
import InteractingSLE.Spec.Sec7.Lemma613

/-!
# Proposition 5.5 in `ℍ` from Propositions 4.11 and 5.1 in the chart `Q`

Packet PROVE-SEC5-N. Specification §5, proof of Proposition 5.5 (`source/spec/p097-144.md` L834–L838, p. 140):
"Proposition 4.11 implies that `η_{θ₁}` is the left boundary of the counterflow line `η′_{θ₁}` of
`h + (θ₁ − π/2)χ` … Since `η_{θ₂}` is the flow line of `h + (θ₁ − π/2)χ` with angle `θ₂ − θ₁ + π/2 > π/2`,
Proposition 5.1 implies that `η_{θ₂}` is to the left of `η′_{θ₁}`. The result then follows since Proposition 4.11
implies that `η_{θ₁}` is contained in the left boundary of `η′_{θ₁}`."

As for Theorem 1.2 under (4.4) (`Cond44Ref.lean`), the argument is run in Lemma 4.5's chart `Q`, where the field of
Figure 7.1 (`Sec7.prop74Data a b`) is the strip field of the proof (PROVE-SEC5-K,
`Prop55Half.stripQHData_prop74Data`), so Proposition 3.4 is not needed, and the counterflow line of `h + (θ₁ − π/2)χ` is the frozen centred counterflow from
`∞`. The three curves are realized on one space by gluing (`WangWu.glueMeasure`): both flow lines are realized on one
GFF (they are determined by the field, `Cond44Ref.hasFieldDeterminedHistories_of_prop411Q`), and a sample of the
counterflow is glued at `h + (θ₁ − π/2)χ`.

* **Named input `Prop51QStatement`**: Proposition 5.1 in Proposition 5.5's configuration, on the glued space: no point
  of the counterflow line of `h + (θ₁ − π/2)χ` at an alive positive rational time is on the left of the flow line
  `η_{θ₂}`.
* **`prop55HalfExistsStatement_of_prop411Q_of_prop51Q`**: `Prop55Half.Prop55HalfExistsStatement` from
  `Cond44Ref.Prop411QStatement` and `Prop51QStatement`.
* **`prop55HalfPlaneStatement_of_prop411Q_of_prop51Q`**, **`exists_isThreeCurveSpace_of_prop411Q_of_prop51Q`**: the
  half-plane Proposition 5.5 and Lemma 7.1's three-curve space (Lemma 6.13's contact exclusion is proved from these,
  PROVE-LEMMA71J) from the two named inputs alone.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.Cond44Ref

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique

/-! ### The named input: Proposition 5.1 in Proposition 5.5's configuration -/

/-- **Named input: Proposition 5.1 for the configuration of Proposition 5.5, in the chart `Q`, on the glued space**
(specification §5, Proposition 5.1, pp. 128–135, as applied in the proof of Proposition 5.5, p. 140). Let
`0 < κ < 4`, `θ₁ < θ₂`, and let the data `−a | b` of Figure 7.1 satisfy (5.2): `b ≥ λ − θ₁χ`,
`a ≥ λ − πχ + θ₂χ`. Let `h` be a GFF with these data on `Ω` and `η` its flow line of angle `θ₂`; let `(h₂, W₂, ζ₂)`
be a centred counterflow coupling whose field has the law of `h + (θ₁ − π/2)χ`, and `k` a regular conditional law of
its killed history given its field. Almost surely on the glued space `P ⊗ k(h + (θ₁ − π/2)χ)` (the flow line and the
counterflow line of `h + (θ₁ − π/2)χ`, conditionally independent given `h`; `η` is the flow line of
`h + (θ₁ − π/2)χ` of angle `θ₂ − θ₁ + π/2 > π/2`), no point of the counterflow line at an alive positive rational
time lies on the left side of `η` ("`η_θ` passes to the left of `η′`"). -/
def Prop51QStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ a b θ₁ θ₂ : ℝ, θ₁ < θ₂ →
    sleLambda κ - θ₁ * chiC κ ≤ b → sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a →
    ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
      (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ)),
      IsFlowLine κ (Sec7.prop74Data a b) {0} 0 θ₂ P h η ζ →
      ∀ {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
        IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂ →
        P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂ →
        ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
          P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k →
          ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
              ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))),
            ∀ s : ℚ, cfPts p.2 s ∉ leftSideOf (range (η p.1))

/-! ### Flow lines as proper arcs -/

/-- The range of a proper arc read on `ℝ≥0`. -/
theorem arcRange_toNNReal (η : ℝ≥0 → ℂ) : arcRange (fun s : ℝ => η s.toNNReal) = range η := by
  ext z
  constructor
  · rintro ⟨s, -, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, mem_Ici.2 t.2, by simp⟩

/-- On an infinite lifetime, the seed line is the continuous generating trace. -/
theorem seedLine_eq_of_isGeneratingTrace {Ω : Type*} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {ω : Ω} (hζ : ζ ω = ⊤)
    (hwc : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω}) (hw0 : W 0 ω = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (fun t => W t ω) (ζ ω) η) : seedLine ζ W ω = fun s : ℝ => η s.toNNReal := by
  have hk : (fun t => killedProc ζ W t ω) = fun t => W t ω := funext (killedProc_of_eq_top hζ)
  funext s
  simp only [seedLine, hk]
  rw [hζ] at hη hwc
  exact LP.traceAt_eq_of_isGeneratingTrace hη hwc hw0 ENNReal.coe_lt_top

/-- **A flow line from `0` of an admissible word is almost surely a proper arc and its coupling's seed line.** -/
theorem ae_isProperArc_of_isFlowLine {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {b : ℝ → ℝ} {J : Finset ℝ} {θ : ℝ}
    (hadm : Sec4.HasAdmissiblePartialSums κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0))
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hfl : IsFlowLine κ b J 0 θ P h η ζ) :
    ∀ᵐ ω ∂P, IsProperArc (fun s : ℝ => η ω s.toNNReal) := by
  obtain ⟨h', 𝓕, W, VL, VR, B, -, hC, htr⟩ := hfl
  have hF := Theorem15.isOrderedForceWord_flowLine b J 0
  filter_upwards [ae_seedLine_of_admissible hκ hκ4 hF hadm hC.1, htr, hC.1.2.2.2.2] with ω hω ht hp
  obtain ⟨hζ, -, hγ⟩ := hω
  have e : (fun t => η ω t - ((0 : ℝ) : ℂ)) = η ω := by
    funext t
    simp
  rw [e] at ht
  rwa [seedLine_eq_of_isGeneratingTrace hζ hp.2.2.2.1 hp.1 ht] at hγ

/-- The strict left side in the chart `E` lies in the frozen left side. -/
theorem stripLeftSide_subset_leftSideOf (A : Set ℂ) : stripLeftSide A ⊆ leftSideOf A :=
  fun _ ⟨hz, x, hx, hxA, hxcl⟩ => ⟨hz, x, hx.2, hxA, hxcl⟩

/-- A property of the first coordinate that holds almost surely on a glued space holds almost surely. -/
theorem ae_of_ae_glue_fst {Ω α β : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → α} (κ : Kernel α β) [IsMarkovKernel κ]
    (hX : Measurable X) {Q : Ω → Prop} (h : ∀ᵐ p ∂(glueMeasure μ κ X hX), Q p.1) : ∀ᵐ ω ∂μ, Q ω := by
  have h' := Measure.ae_ae_of_ae_compProd (p := fun p : Ω × β => Q p.1) h
  filter_upwards [h'] with ω hω
  by_contra hQ
  have hnull : (κ.comap X hX ω) univ = 0 := by
    rw [ae_iff] at hω
    simp only [hQ, not_false_eq_true, ofPred_true] at hω
    exact hω
  simp at hnull

/-! ### Proposition 5.5 -/

/-- **`Prop55Half.Prop55HalfExistsStatement` from Propositions 4.11 and 5.1 in the chart `Q`.** -/
theorem prop55HalfExistsStatement_of_prop411Q_of_prop51Q (h411 : Prop411QStatement.{u})
    (h51 : Prop51QStatement.{u}) : Prop55Half.Prop55HalfExistsStatement.{u} := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 hb ha
  obtain ⟨Ω, mΩ, P, hP, h, hh⟩ := Sec7.Lemma71G.exists_isGFFWithBoundaryData_prop74Data.{u} hκ a b
  have hbpc := Sec7.isPiecewiseConstant_prop74Data a b
  have hχ := Sec4.chiC_pos hκ hκ4
  have hθχ : θ₁ * chiC κ ≤ θ₂ * chiC κ := mul_le_mul_of_nonneg_right h12.le hχ.le
  have hF := Theorem15.isOrderedForceWord_flowLine (Sec7.prop74Data a b) {0} 0
  -- (4.4) for both angles, hence both flow lines exist on `h` and are proper arcs
  have h44₁ := Sec7.Lemma71H.cond44_flowLine_prop74Data (θ := θ₁) hκ (a := a) (b := b) (by linarith) hb
  have h44₂ := Sec7.Lemma71H.cond44_flowLine_prop74Data (θ := θ₂) hκ (a := a) (b := b) ha (by linarith)
  have hadm₁ := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44₁
  have hadm₂ := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44₂
  obtain ⟨η₁, ζ₁, hη₁⟩ := Sec7.Lemma71H.exists_isFlowLine_of_det hκ hκ4.le hbpc hh hadm₁
    (hasFieldDeterminedHistories_of_prop411Q h411 hκ hκ4 hF h44₁)
  obtain ⟨η₂, ζ₂, hη₂⟩ := Sec7.Lemma71H.exists_isFlowLine_of_det hκ hκ4.le hbpc hh hadm₂
    (hasFieldDeterminedHistories_of_prop411Q h411 hκ hκ4 hF h44₂)
  have harc₁ := ae_isProperArc_of_isFlowLine hκ hκ4.le hadm₁ hη₁
  have harc₂ := ae_isProperArc_of_isFlowLine hκ hκ4.le hadm₂ hη₂
  refine ⟨Ω, mΩ, P, hP, h, η₁, η₂, ζ₁, ζ₂, hh, hη₁, hη₂, ?_⟩
  -- the coupling of `η₁`, with field `h + θ₁χ`
  obtain ⟨h₁, 𝓕, W, VL, VR, B, htr, hC, htrace⟩ := hη₁
  obtain rfl : h₁ = fun ω => Exist.flowField 0 (θ₁ * chiC κ) (h ω) :=
    funext fun ω => Lemma75Bridge.eq_flowField_of_isTranslateAddConst (htr ω)
  -- the counterflow of `h + (θ₁ − π/2)χ` and the glued space
  obtain ⟨Ω₂, mΩ₂, hSB, P₂, hP₂, h₂, W₂, ζ₂', hcf, hh₂, hlaw⟩ := exists_cfCoupling hκ hC
  have hX₂ := isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf
  set k := condDistrib (cfHistory W₂ ζ₂') h₂ P₂ with hkdef
  have hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂' ω)) = P₂.map h₂ ⊗ₘ k :=
    (compProd_map_condDistrib hh₂.aemeasurable (measurable_cfHistory hX₂).aemeasurable).symm
  have hXm : Measurable fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)) :=
    (measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)
  -- Proposition 4.11 for `η₁` and Proposition 5.1 for `η₂` on the same glued space
  have hg411 := h411 κ hκ hκ4 _ _ _ _ hF h44₁ P 𝓕 W VL VR B ζ₁ _ hC P₂ h₂ W₂ ζ₂' hcf hlaw k hk
  have hg51 := h51 κ hκ hκ4 a b θ₁ θ₂ h12 hb ha P h η₂ ζ₂ hh hη₂ P₂ h₂ W₂ ζ₂' hcf hlaw k hk
  have hreg : ∀ᵐ ω ∂P, IsProperArc (seedLine ζ₁ W ω) ∧ seedLine ζ₁ W ω = (fun s : ℝ => η₁ ω s.toNNReal) ∧
      IsProperArc (fun s : ℝ => η₂ ω s.toNNReal) := by
    filter_upwards [ae_seedLine_of_admissible hκ hκ4.le hF hadm₁ hC.1, htrace, hC.1.2.2.2.2, harc₂]
      with ω hω ht hp ha₂
    obtain ⟨hζ, -, hγ⟩ := hω
    have e : (fun t => η₁ ω t - ((0 : ℝ) : ℂ)) = η₁ ω := by
      funext t
      simp
    rw [e] at ht
    exact ⟨hγ, seedLine_eq_of_isGeneratingTrace hζ hp.2.2.2.1 hp.1 ht, ha₂⟩
  have hglue : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) hXm),
      LiesRightOf (range (η₁ p.1)) (range (η₂ p.1)) := by
    filter_upwards [hg411, hg51, ae_glue_fst (μ := P) k hXm hreg] with p hp1 hp2 hp3
    obtain ⟨hγ, hline, hγ₂⟩ := hp3
    -- `η₁` lies in the completed counterflow range
    have hsub : range (η₁ p.1) ⊆ cfRange p.2 := by
      rw [← arcRange_toNNReal, ← hline]
      exact arcRange_subset_closure_of_forall_rat hγ hp1.1
    -- the completed counterflow range avoids the left side of `η₂`
    have hdis : Disjoint (cfRange p.2) (leftSideOf (range (η₂ p.1))) := by
      rw [← arcRange_toNNReal]
      refine disjoint_closure_leftSideOf hγ₂ ?_
      rintro _ ⟨s, rfl⟩
      rw [arcRange_toNNReal]
      exact hp2 s
    exact ((hdis.mono_left hsub).mono_right (stripLeftSide_subset_leftSideOf _))
  exact ae_of_ae_glue_fst k hXm hglue

/-- **The half-plane Proposition 5.5 (`Sec7.Lemma71H.Prop55HalfPlaneStatement`) from Propositions 4.11 and 5.1 in
the chart `Q`.** -/
theorem prop55HalfPlaneStatement_of_prop411Q_of_prop51Q (h411 : Prop411QStatement.{u})
    (h51 : Prop51QStatement.{u}) : Sec7.Lemma71H.Prop55HalfPlaneStatement.{u} :=
  Prop55Half.prop55HalfPlaneStatement_of_exists (cond44ReferenceStatement_of_prop411Q h411)
    (prop55HalfExistsStatement_of_prop411Q_of_prop51Q h411 h51)

/-- **Lemma 7.1's three-curve space from Propositions 4.11 and 5.1 in the chart `Q`**: the inputs of
`Sec7.Lemma72B.exists_isThreeCurveSpace` (the §4.2 reference, the half-plane Proposition 5.5, and Lemma 6.13's
contact exclusion, which `Sec7.Lemma613.lemma613ContactStatement_of_prop55` proves from the first two). -/
theorem exists_isThreeCurveSpace_of_prop411Q_of_prop51Q (h411 : Prop411QStatement.{u})
    (h51 : Prop51QStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {θ₁ θ₂ a b : ℝ} (hθ₁ : θ₁ < 0)
    (hθ₂ : 0 < θ₂) (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a) (hb : sleLambda κ - θ₁ * chiC κ ≤ b) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) (β α γ : Ω → ℝ≥0 → ℂ) (ζβ ζα ζγ : Ω → ℝ≥0∞),
      Sec7.Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ :=
  Sec7.Lemma72B.exists_isThreeCurveSpace (cond44ReferenceStatement_of_prop411Q h411)
    (prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51)
    (Sec7.Lemma613.lemma613ContactStatement_of_prop55 (cond44ReferenceStatement_of_prop411Q h411)
      (prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51)) hκ hκ4 hθ₁ hθ₂ ha hb

end InteractingSLE.Sec5.Cond44Ref
