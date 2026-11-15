/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71HInputs
import InteractingSLE.Spec.Sec7.Lemma71BGeom
import InteractingSLE.Spec.Supplement.S9BTransfer
import InteractingSLE.Spec.Zhan.TransienceTrace

/-!
# Lemma 7.1's pocket: the planar facts on the three-curve space

Packet PROVE-LEMMA71I, part (α). Specification, proof of Lemma 7.1 (`source/spec/p193-240.md` L583–L598,
pp. 223–224): "All three curves are simple proper non-boundary-intersecting curves from zero to infinity, with the
established closed-side order of this subsection. … **Aux.** lemma 93 orders the common contacts of every pair. …
**Aux.** lemma 33 gives the Jordan pocket bounded by the two corresponding open outer arcs. These are exactly the
nonempty between-components. … Every nonempty pocket is in fact visited. Between its two endpoint-hit times, the middle
curve cannot lie entirely on the outer curves: the two closed contact-time sets are nowhere dense by the pairwise
argument in Lemma 6.13."

The deterministic chamber argument (Aux. 93, Aux. 33, the traversal, the boundary charts and the mapped segment) is
landed for three ordered simple proper arcs of `ℍ` (`WangWu.IsOrderedArcs`, PROVE-WW-B4; read off as
`Lemma71B.exists_mappedSegment_geom`). This file connects it to the three-curve space of
`Lemma71H.exists_threeCurveSpace_ordered`:

* **the order**: the frozen W0 order `range β ⊆ closedLeftSide γ` (closed left Jordan side, the curve closed along
  its lower vertical ray) gives `Disjoint (range β) (rightSideOf (range γ))`, the order of `WangWu.IsOrderedArcs`
  (`disjoint_rightSideOf_of_subset_closedLeftSide`, through the Jordan separation `Supp9B.disjoint_leftSide_rightSide`);
* **the curves as arcs**: `realPath η t = η t⁺` is a simple proper arc (`isProperArc_realPath`);
* **simplicity of the flow lines** in Remark 4.1's regime (`IsFlowLine.ae_injective_angle`; the injective trace of
  `Zhan.IsIntegratedSLEEvolution.ae_simple_trace` and uniqueness of generating traces);
* **(MD1)** (Lemma 6.13: the contact-time sets have empty interior) is probabilistic: it uses Proposition 3.8's
  common-component case, the single-curve side heights and the §2.3 branch normalization (pp. 216–217), i.e. the
  in-flight side-height work. It enters as the named input `Lemma613ContactStatement`, stated exactly as the
  exclusion of (MD1) for two flow lines of distinct angles of the Figure 7.1 field;
* **`ae_isOrderedArcs`** and **`ae_mappedSegment_geom`**: almost surely, on the three-curve space, the three curves are
  ordered simple proper arcs with nowhere-dense contact times, and for **every** component `C` between the outer
  curves there are a traversal clock and a boundary chart whose mapped segment is a continuous simple path in `ℍ̄` from
  `0` to `∞` with nowhere-dense real-boundary times (the hypotheses (a)–(f) of `Lemma71HTraverse` and their
  consequences, in the form `WangWu.IsOrderedArcs.lemma422` proves them).

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.Lemma71I

/-! ### The closed-side order as the order of `WangWu.IsOrderedArcs` -/

section Sides

variable {γ : ℝ≥0 → ℂ}

/-- A real point to the right of the seed and off the closed curve is on the right side (mirror of
`Supp9B.ofReal_mem_leftSide`). -/
theorem ofReal_mem_rightSide (hγ : ∀ t, 0 ≤ (γ t).im) (h0 : (γ 0).im = 0) {x : ℝ}
    (hx : (γ 0).re < x) (hxγ : (x : ℂ) ∉ seedRayClosure γ) : (x : ℂ) ∈ Supp9B.rightSide γ := by
  have hcl : (x : ℂ) ∈ closure (Supp9B.lowerRight (γ 0).re) := by
    have ht : Tendsto (fun s : ℝ => (x : ℂ) - (s : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
      have : Continuous (fun s : ℝ => (x : ℂ) - (s : ℂ) * Complex.I) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    constructor <;> simp [hx, show (0 : ℝ) < s from hs]
  have hpc : IsPreconnected (insert (x : ℂ) (Supp9B.lowerRight (γ 0).re)) :=
    (Supp9B.convex_lowerRight _).isPreconnected.subset_closure (subset_insert _ _)
      (insert_subset hcl subset_closure)
  exact hpc.subset_connectedComponentIn (mem_insert_of_mem _ (Supp9B.right_ref_mem_lowerRight h0))
    (insert_subset hxγ (Supp9B.lowerRight_subset_compl hγ)) (mem_insert _ _)

/-- **The frozen right side of a proper curve from `0` is its Jordan right side**: a point of `ℍ ∖ γ` whose
complementary component reaches the positive real axis off `γ` lies in the component of `γ(0) + 1 − i` in the
complement of the curve closed along its lower vertical ray. -/
theorem rightSideOf_range_subset_rightSide (hγ : Supp9B.IsProperCurve γ) (h0 : γ 0 = 0) :
    rightSideOf (range γ) ⊆ Supp9B.rightSide γ := by
  rintro z ⟨⟨hzH, hzγ⟩, x, hx0, hxγ, hxcl⟩
  have h0' : (γ 0).im = 0 := by rw [h0]; simp
  set S := seedRayClosure γ with hSdef
  have hSc : IsClosed S := Supp9B.isClosed_seedRayClosure hγ
  have hray : ∀ p : ℂ, 0 < p.im → p ∉ range γ → p ∉ S := by
    rintro p hp hpγ (hpS | ⟨-, hpim⟩)
    · exact hpγ hpS
    · rw [h0'] at hpim
      linarith
  have hxS : (x : ℂ) ∉ S := by
    rintro (hxS | ⟨hxre, -⟩)
    · exact hxγ hxS
    · rw [h0] at hxre
      simp only [Complex.ofReal_re, Complex.zero_re] at hxre
      linarith
  have hxR : (x : ℂ) ∈ Supp9B.rightSide γ :=
    ofReal_mem_rightSide hγ.2.2.1 h0' (by rw [h0]; simpa using hx0) hxS
  have hRo : IsOpen (Supp9B.rightSide γ) := hSc.isOpen_compl.connectedComponentIn
  obtain ⟨w, hwR, hwC⟩ := mem_closure_iff.1 hxcl _ hRo hxR
  have hsub : H \ range γ ⊆ Sᶜ := fun p hp => hray p hp.1 hp.2
  have hpre : connectedComponentIn (H \ range γ) z ⊆ connectedComponentIn Sᶜ z :=
    isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn ⟨hzH, hzγ⟩) ((connectedComponentIn_subset _ _).trans hsub)
  have hw : w ∈ connectedComponentIn Sᶜ z := hpre hwC
  have hzS : z ∈ Sᶜ := hray z hzH hzγ
  show z ∈ connectedComponentIn Sᶜ (γ 0 + 1 - Complex.I)
  rw [connectedComponentIn_eq hwR, ← connectedComponentIn_eq hw]
  exact mem_connectedComponentIn hzS

/-- **The W0 closed-side order gives the order of `WangWu.IsOrderedArcs`**: if `β` lies in the closed left side of
the proper curve `γ` from `0`, then `β` avoids the frozen right side of `γ`. -/
theorem disjoint_rightSideOf_of_subset_closedLeftSide (hγ : Supp9B.IsProperCurve γ) (h0 : γ 0 = 0)
    {β : ℝ≥0 → ℂ} (hβ : range β ⊆ closedLeftSide γ) : Disjoint (range β) (rightSideOf (range γ)) := by
  have h0' : (γ 0).im = 0 := by rw [h0]; simp
  rw [Set.disjoint_left]
  intro z hzβ hzR
  have hR := rightSideOf_range_subset_rightSide hγ h0 hzR
  rcases (hβ hzβ : z ∈ Supp9B.leftSide γ ∪ seedRayClosure γ) with hL | hS
  · exact Set.disjoint_left.1 (Supp9B.disjoint_leftSide_rightSide hγ h0') hL hR
  · exact connectedComponentIn_subset _ _ hR hS

end Sides

/-! ### `ℝ≥0`-indexed curves as simple proper arcs -/

/-- The `ℝ`-indexed path `t ↦ η(t⁺)` of an `ℝ≥0`-indexed curve. -/
def realPath (η : ℝ≥0 → ℂ) (t : ℝ) : ℂ := η t.toNNReal

theorem realPath_coe (η : ℝ≥0 → ℂ) (t : ℝ≥0) : realPath η t = η t := by
  simp [realPath]

theorem arcRange_realPath (η : ℝ≥0 → ℂ) : WangWu.arcRange (realPath η) = range η := by
  ext z
  constructor
  · rintro ⟨t, -, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, t.2, realPath_coe η t⟩

/-- **A continuous injective curve from `0`, in `ℍ` at positive times and tending to `∞`, is a simple proper arc.** -/
theorem isProperArc_realPath {η : ℝ≥0 → ℂ} (hc : Continuous η) (hi : Injective η) (h0 : η 0 = 0)
    (hH : ∀ t, 0 < t → η t ∈ H) (hinf : Tendsto (fun t => ‖η t‖) atTop atTop) :
    WangWu.IsProperArc (realPath η) where
  cont := (hc.comp continuous_real_toNNReal).continuousOn
  inj := fun s hs t ht hst => by
    have h := hi hst
    rw [← Real.coe_toNNReal s hs, ← Real.coe_toNNReal t ht, h]
  zero := by simp [realPath, h0]
  mem_H := fun t ht => hH _ (Real.toNNReal_pos.2 ht)
  tendsto := hinf.comp tendsto_real_toNNReal_atTop

/-- The pathwise hypotheses of a curve of the three-curve configuration. -/
def IsSimpleProper (η : ℝ≥0 → ℂ) : Prop :=
  Continuous η ∧ Injective η ∧ η 0 = 0 ∧ (∀ t, 0 < t → η t ∈ H) ∧ Tendsto (fun t => ‖η t‖) atTop atTop

theorem IsSimpleProper.isProperArc {η : ℝ≥0 → ℂ} (h : IsSimpleProper η) : WangWu.IsProperArc (realPath η) :=
  isProperArc_realPath h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

theorem IsSimpleProper.isProperCurve {η : ℝ≥0 → ℂ} (h : IsSimpleProper η) : Supp9B.IsProperCurve η := by
  refine ⟨h.1, h.2.1, fun t => ?_, h.2.2.2.2⟩
  rcases eq_zero_or_pos t with ht | ht
  · rw [ht, h.2.2.1]; simp
  · exact le_of_lt (h.2.2.2.1 t ht)

/-- **Three ordered curves** (Lemma 7.1's setup: `η_{θ₁}` (= `α`) right of `η` (= `γ`) right of `η_{θ₂}` (= `β`),
in the W0 closed-side form of `Lemma71H.exists_threeCurveSpace_ordered`) **are ordered simple proper arcs** in the
sense of `WangWu.IsOrderedArcs` (right wall `α`, middle `γ`, left wall `β`). -/
theorem isOrderedArcs_of_closedLeftSide {β α γ : ℝ≥0 → ℂ} (hβ : IsSimpleProper β) (hα : IsSimpleProper α)
    (hγ : IsSimpleProper γ) (hγα : range γ ⊆ closedLeftSide α) (hβγ : range β ⊆ closedLeftSide γ) :
    WangWu.IsOrderedArcs (realPath α) (realPath γ) (realPath β) where
  right := hα.isProperArc
  middle := hγ.isProperArc
  left := hβ.isProperArc
  right_middle := by
    rw [arcRange_realPath, arcRange_realPath]
    exact disjoint_rightSideOf_of_subset_closedLeftSide hα.isProperCurve hα.2.2.1 hγα
  middle_left := by
    rw [arcRange_realPath, arcRange_realPath]
    exact disjoint_rightSideOf_of_subset_closedLeftSide hγ.isProperCurve hγ.2.2.1 hβγ

/-- No rational parameter interval of `γ` is contained in `range α` (the exclusion of (MD1), Lemma 6.13). -/
def NoCommonArc (γ α : ℝ≥0 → ℂ) : Prop :=
  ∀ a b : ℚ, 0 < a → a < b → ∃ t : ℝ≥0, (a : ℝ) ≤ t ∧ (t : ℝ) ≤ b ∧ γ t ∉ range α

/-- **(MD1) excluded ⇒ the contact times have empty interior** (Lemma 6.13's rational-interval reduction,
`Sec6.interior_eq_empty_of_forall_rat`). -/
theorem interior_contact_eq_empty {γ α : ℝ≥0 → ℂ} (h : NoCommonArc γ α) :
    interior {t ∈ Ici (0 : ℝ) | realPath γ t ∈ WangWu.arcRange (realPath α)} = ∅ := by
  set X := {t ∈ Ici (0 : ℝ) | realPath γ t ∈ WangWu.arcRange (realPath α)} with hX
  have hsub : interior X ⊆ interior (X ∩ Ioi 0) := by
    refine interior_maximal (fun t ht => ⟨interior_subset ht, ?_⟩) isOpen_interior
    have h1 : interior X ⊆ interior (Ici (0 : ℝ)) := interior_mono fun s hs => hs.1
    rw [interior_Ici] at h1
    exact h1 ht
  have h2 : interior (X ∩ Ioi 0) = ∅ := by
    refine Sec6.interior_eq_empty_of_forall_rat inter_subset_right fun a b ha hab hcon => ?_
    obtain ⟨t, hat, htb, htα⟩ := h a b ha hab
    have ht := (hcon ⟨hat, htb⟩).1.2
    rw [arcRange_realPath, realPath_coe] at ht
    exact htα ht
  rw [h2] at hsub
  exact subset_empty_iff.1 hsub

/-! ### Simplicity of the flow lines in Remark 4.1's regime -/

section Simple

variable {k : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **An angle-`θ` flow line from `0` in Remark 4.1's regime is almost surely a simple proper curve** (Remark 2.3 for
`κ ≤ 4`; the injective trace of `Zhan.IsIntegratedSLEEvolution.ae_simple_trace` is the flow line by uniqueness of
generating traces, `IsGeneratingTrace.eq_of_le`; transience by `Lemma71G.IsFlowLine.ae_tendsto_angle`). -/
theorem IsFlowLine.ae_isSimpleProper_angle (hk : 0 < k) (hk4 : k ≤ 4) (hb : IsPiecewiseConstantBoundaryData b J)
    {θ : ℝ} (hL : ∀ x : ℝ, x < 0 → x ∉ J → b x + θ * chiC k ≤ -sleLambda k + π * chiC k)
    (hR : ∀ x : ℝ, 0 < x → x ∉ J → sleLambda k - π * chiC k ≤ b x + θ * chiC k)
    (hfl : IsFlowLine k b J 0 θ P h η ζ) : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsSimpleProper (η ω) := by
  obtain ⟨𝓕, W, VL, VR, B, hev, htr⟩ := Lemma71G.IsFlowLine.exists_evolution_angle hfl
  have hword := Theorem15.isOrderedForceWord_flowLine b J 0
  have hadm := Lemma71G.hasAdmissiblePartialSums_flowLine_angle hk hb θ hL hR
  filter_upwards [Zhan.IsIntegratedSLEEvolution.ae_simple_trace hk hk4 hword hadm hev, htr, hev.2.2.2.2,
    Lemma71G.IsFlowLine.ae_tendsto_angle hk hk4 hb hL hR hfl] with ω h1 h2 h3 h4
  obtain ⟨hζ, -, η', hη', hinj, hH, -⟩ := h1
  rw [hζ] at h2 h3
  have heq : η ω = η' := funext fun t => h2.eq_of_le hη' h3.2.2.2.1 h3.1 le_top
  have hc : Continuous η' := by
    have := hη'.2.1
    simp only [le_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  rw [heq] at h4 ⊢
  exact ⟨hζ, hc, hinj, hη'.1, hH, h4.2.2⟩

end Simple

/-! ### (MD1): the named input of Lemma 6.13 -/

/-- **Named input: Lemma 6.13's exclusion of (MD1)** (specification pp. 216–217: "If it had nonempty interior with
positive probability, some fixed rational `0 < a < b < ∞` would satisfy `P[η_{θ₁}([a, b]) ⊆ η_{θ₂}] > 0` (MD1)",
excluded by the common-component case of Proposition 3.8 (MD2), the single-curve side heights `λ − θᵢχ` and the
§2.3 normalization of the branches). For `0 < κ < 4`, the data of Figure 7.1 and angles `θ₁ < θ₂` with
Proposition 5.5's bounds (5.2), two flow lines from `0` of the same GFF almost surely share no nondegenerate
parameter arc, in either parametrization. -/
def Lemma613ContactStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ a b θ₁ θ₂ : ℝ, θ₁ < θ₂ →
    sleLambda κ - θ₁ * chiC κ ≤ b → sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h (prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ) →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ (prop74Data a b) {0} 0 θ₁ P h η₁ ζ₁ → IsFlowLine κ (prop74Data a b) {0} 0 θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ζ₁ ω = ⊤ → ζ₂ ω = ⊤ → NoCommonArc (η₁ ω) (η₂ ω) ∧ NoCommonArc (η₂ ω) (η₁ ω)

/-! ### The planar facts almost surely -/

section Space

variable {κ : ℝ} {θ₁ θ₂ a b : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {β α γ : Ω → ℝ≥0 → ℂ} {ζβ ζα ζγ : Ω → ℝ≥0∞}

/-- **The planar hypotheses of the chamber argument hold almost surely on the three-curve space.** For the flow lines
`β = η_{θ₂}`, `α = η_{θ₁}`, `γ = η_0` of the Figure 7.1 field (Lemma 7.1's setup, `θ₁ < 0 < θ₂`, bounds (5.2)) with
the a.s. closed-side order of `Lemma71H.exists_threeCurveSpace_ordered`: almost surely the three curves are simple
proper curves, `(α, γ, β)` are ordered simple proper arcs (`WangWu.IsOrderedArcs`), and the middle curve has no common
arc with either outer curve. Named input: (MD1) excluded (`Lemma613ContactStatement`). -/
theorem ae_isOrderedArcs (hMD : Lemma613ContactStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : θ₁ < 0)
    (hθ₂ : 0 < θ₂) (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a)
    (hb : sleLambda κ - θ₁ * chiC κ ≤ b)
    (hh : IsGFFWithBoundaryData P h (prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ))
    (hβf : IsFlowLine κ (prop74Data a b) {0} 0 θ₂ P h β ζβ) (hαf : IsFlowLine κ (prop74Data a b) {0} 0 θ₁ P h α ζα)
    (hγf : IsFlowLine κ (prop74Data a b) {0} 0 0 P h γ ζγ)
    (hord : ∀ᵐ ω ∂P, range (β ω) ⊆ closedLeftSide (γ ω) ∧ range (γ ω) ⊆ closedLeftSide (α ω)) :
    ∀ᵐ ω ∂P, IsSimpleProper (β ω) ∧ IsSimpleProper (α ω) ∧ IsSimpleProper (γ ω) ∧
      WangWu.IsOrderedArcs (realPath (α ω)) (realPath (γ ω)) (realPath (β ω)) ∧
      NoCommonArc (γ ω) (α ω) ∧ NoCommonArc (γ ω) (β ω) := by
  have hχ := Sec4.chiC_pos hκ hκ4
  have h1 : 0 < θ₂ * chiC κ := mul_pos hθ₂ hχ
  have h2 : θ₁ * chiC κ < 0 := mul_neg_of_neg_of_pos hθ₁ hχ
  have hπ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le hχ.le
  have hb41 : sleLambda κ - π * chiC κ - θ₁ * chiC κ ≤ b := by linarith
  have hpc := isPiecewiseConstant_prop74Data a b
  have hsimple : ∀ θ, θ₁ ≤ θ → θ ≤ θ₂ → ∀ {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞},
      IsFlowLine κ (prop74Data a b) {0} 0 θ P h η ζ → ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsSimpleProper (η ω) := by
    intro θ hθ1 hθ2 η ζ hfl
    obtain ⟨hL, hR⟩ := Lemma71G.prop74Data_remark41 hκ hκ4 hθ1 hθ2 ha hb41
    exact IsFlowLine.ae_isSimpleProper_angle hκ hκ4.le hpc hL hR hfl
  have hγα := hMD κ hκ hκ4 a b θ₁ 0 hθ₁ hb (by linarith) P h hh α γ ζα ζγ hαf hγf
  have hγβ := hMD κ hκ hκ4 a b 0 θ₂ hθ₂ (by linarith) ha P h hh γ β ζγ ζβ hγf hβf
  filter_upwards [hsimple θ₂ (hθ₁.trans hθ₂).le le_rfl hβf, hsimple θ₁ le_rfl (hθ₁.trans hθ₂).le hαf,
    hsimple 0 hθ₁.le hθ₂.le hγf, hord, hγα, hγβ] with ω hβω hαω hγω hordω hγαω hγβω
  refine ⟨hβω.2, hαω.2, hγω.2, isOrderedArcs_of_closedLeftSide hβω.2 hαω.2 hγω.2 hordω.2 hordω.1,
    (hγαω hαω.1 hγω.1).2, (hγβω hγω.1 hβω.1).1⟩

/-- **The pocket geometry almost surely, for every pocket** (proof of Lemma 7.1, pp. 223–224, with Remark 6.14):
under the hypotheses of `ae_isOrderedArcs`, almost surely, for every component `C` between the outer curves `α`
(right) and `β` (left), there are a traversal clock `κ'` of `C` by the middle curve and a boundary chart `Ψ` of `C`
(`Ψ(C) ⊆ ℍ`) whose mapped segment `u ↦ Ψ(γ(κ' u))` is a continuous simple path in `ℍ̄` from `0` to `∞` with
nowhere-dense real-boundary times (`Lemma71B.exists_mappedSegment_geom`; the full chamber statement, for every
boundary chart, is `WangWu.IsOrderedArcs.lemma422` applied to the a.s. hypotheses of `ae_isOrderedArcs`). -/
theorem ae_mappedSegment_geom (hMD : Lemma613ContactStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : θ₁ < 0)
    (hθ₂ : 0 < θ₂) (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a)
    (hb : sleLambda κ - θ₁ * chiC κ ≤ b)
    (hh : IsGFFWithBoundaryData P h (prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ))
    (hβf : IsFlowLine κ (prop74Data a b) {0} 0 θ₂ P h β ζβ) (hαf : IsFlowLine κ (prop74Data a b) {0} 0 θ₁ P h α ζα)
    (hγf : IsFlowLine κ (prop74Data a b) {0} 0 0 P h γ ζγ)
    (hord : ∀ᵐ ω ∂P, range (β ω) ⊆ closedLeftSide (γ ω) ∧ range (γ ω) ⊆ closedLeftSide (α ω)) :
    ∀ᵐ ω ∂P, ∀ C ∈ betweenComponents (range (α ω)) (range (β ω)),
      ∃ (κ' : ℝ → ℝ) (Ψ : ℂ → ℂ), ContinuousOn κ' (Ici 0) ∧ StrictMonoOn κ' (Ici 0) ∧
        (∀ u, 0 ≤ u → realPath (γ ω) (κ' u) ∈ closure C) ∧
        (∀ t, 0 ≤ t → realPath (γ ω) t ∈ C → ∃ u, 0 ≤ u ∧ κ' u = t) ∧ MapsTo Ψ C H ∧
        ContinuousOn (fun u => Ψ (realPath (γ ω) (κ' u))) (Ici 0) ∧
        InjOn (fun u => Ψ (realPath (γ ω) (κ' u))) (Ici 0) ∧
        MapsTo (fun u => Ψ (realPath (γ ω) (κ' u))) (Ici 0) Hbar ∧ Ψ (realPath (γ ω) (κ' 0)) = 0 ∧
        Tendsto (fun u => ‖Ψ (realPath (γ ω) (κ' u))‖) atTop atTop ∧
        interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (Ψ (realPath (γ ω) (κ' u))).im = 0} = ∅ := by
  filter_upwards [ae_isOrderedArcs hMD hκ hκ4 hθ₁ hθ₂ ha hb hh hβf hαf hγf hord] with ω hω C hC
  obtain ⟨-, -, -, hord', hcα, hcβ⟩ := hω
  rw [← arcRange_realPath (α ω), ← arcRange_realPath (β ω)] at hC
  exact Lemma71B.exists_mappedSegment_geom hord' (interior_contact_eq_empty hcα) (interior_contact_eq_empty hcβ) hC

/-- **The ordered three-curve space with the planar facts** (Lemma 7.1's setup and the deterministic part of its proof,
pp. 221–224): `Lemma71H.exists_threeCurveSpace_ordered` together with, almost surely, simple proper curves, the
ordered-arc structure of `(α, γ, β)` and no common arc of the middle curve with either outer curve, so that
`WangWu.IsOrderedArcs.lemma422` applies to every component between the outer curves. Named inputs: those of
`exists_threeCurveSpace_ordered` and (MD1) excluded. Conditional helper. -/
theorem exists_threeCurveSpace_planar (href : Lemma71H.Cond44ReferenceStatement.{u})
    (hA56 : Restart.RetainedRangeEntranceStatement.{u}) (h55 : Lemma71H.Prop55HalfPlaneStatement.{u})
    (hMD : Lemma613ContactStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {θ₁ θ₂ a b : ℝ} (hθ₁ : θ₁ < 0)
    (hθ₂ : 0 < θ₂) (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a) (hb : sleLambda κ - θ₁ * chiC κ ≤ b) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) (β α γ : Ω → ℝ≥0 → ℂ) (ζβ ζα ζγ : Ω → ℝ≥0∞),
      IsGFFWithBoundaryData P h (prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ) ∧
      IsBoundedHarmonicExtension (prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ) u₀ ∧
      LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P ∧
      IsFlowLine κ (prop74Data a b) {0} 0 θ₂ P h β ζβ ∧ IsFlowLine κ (prop74Data a b) {0} 0 θ₁ P h α ζα ∧
      IsFlowLine κ (prop74Data a b) {0} 0 0 P h γ ζγ ∧
      Lemma71G.IsLemma62Curve β (WholeField.centredField h u₀) P ∧
      Lemma71G.IsLemma62Curve α (WholeField.centredField h u₀) P ∧
      Lemma71G.IsLemma62Curve γ (WholeField.centredField h u₀) P ∧
      ∀ᵐ ω ∂P, ζβ ω = ⊤ ∧ ζα ω = ⊤ ∧ ζγ ω = ⊤ ∧
        (∀ i (t : ℝ≥0) (x : ℝ), x ≠ 0 → Sec6.Three.threeCurves β α γ i ω t ≠ x) ∧
        range (β ω) ⊆ closedLeftSide (γ ω) ∧ range (γ ω) ⊆ closedLeftSide (α ω) ∧
        range (β ω) ⊆ closedLeftSide (α ω) ∧
        IsSimpleProper (β ω) ∧ IsSimpleProper (α ω) ∧ IsSimpleProper (γ ω) ∧
        WangWu.IsOrderedArcs (realPath (α ω)) (realPath (γ ω)) (realPath (β ω)) ∧
        NoCommonArc (γ ω) (α ω) ∧ NoCommonArc (γ ω) (β ω) := by
  obtain ⟨Ω, mΩ, P, hP, h, u₀, β, α, γ, ζβ, ζα, ζγ, hh, hu₀, hz, hβf, hαf, hγf, hβ, hα, hγ, hae⟩ :=
    Lemma71H.exists_threeCurveSpace_ordered href hA56 h55 hκ hκ4 hθ₁ hθ₂ ha hb
  refine ⟨Ω, mΩ, P, hP, h, u₀, β, α, γ, ζβ, ζα, ζγ, hh, hu₀, hz, hβf, hαf, hγf, hβ, hα, hγ, ?_⟩
  have hord : ∀ᵐ ω ∂P, range (β ω) ⊆ closedLeftSide (γ ω) ∧ range (γ ω) ⊆ closedLeftSide (α ω) :=
    hae.mono fun ω hω => ⟨hω.2.2.2.2.1, hω.2.2.2.2.2.1⟩
  filter_upwards [hae, ae_isOrderedArcs hMD hκ hκ4 hθ₁ hθ₂ ha hb hh hβf hαf hγf hord] with ω h1 h2
  exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1, h1.2.2.2.2.2.2, h2⟩

end Space

end InteractingSLE.Sec7.Lemma71I
