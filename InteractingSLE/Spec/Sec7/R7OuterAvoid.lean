/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7OuterOrder
import InteractingSLE.Spec.Sec5.Cond44Ref
import InteractingSLE.Spec.Sec5.Prop55N
import InteractingSLE.Spec.Sec5.GlueCond

/-!
# Theorem R.7, part (a): the counterflow avoids the exterior side `E_L` of the certified left frontier

Packet PROVE-R7-OUTER. Supplement §5.1 (`source/spec/p433-480.md` L962–L964, p. 471): "The available non-boundary
inputs are the complete simple extremal flow lines `β_R, β_L` of angles `−π/2, +π/2`, the global side confinement of
`η` […] Write `E_R, E_L` for the open exterior Jordan sides of `β_R, β_L`. Then `η` avoids `E_R ∪ E_L` throughout
its lifetime."

In the Lean frame (`Sec7.StripSys`): the field `h` on `ℍ` with data `b`, its centred counterflow `η′` from `∞` to `0`
(frozen `IsCenteredCounterflowDriver κ P h W′ ζ′`, curve `R ∘ trace(W′)`, `R(z) = −1/z`), and `β_L` its flow line of
angle `π/2` from `0`. The counterflow's left boundary is `β_L` — this is Proposition 4.11 (`Sec5.Cond44Ref`,
named input `Prop411QStatement`, R48-safe): the counterflow of `g = h₀ − (π/2)χ` never enters the left side of the
angle-`0` flow line of `h₀`, i.e. of the angle-`π/2` flow line of `g`. That input is stated on the **glued space**
(the flow line and a counterflow sample conditionally independent given the field). This file transfers it to an
**arbitrary** centred counterflow coupling of `h` on the same space as the flow line, e.g. the strip system's:

* `arcEnum`, `closure_range_arcEnum`: `arcRange γ ∪ {Im ≤ 0}` as the closure of a countable family;
* `LeftQ`, **`leftQ_iff`**, **`measurableSet_leftQ`**: a countable (rational polygonal reachability,
  `Theorem15D5.Reach`) description of `z ∈ leftSideOf (arcRange γ)` for proper arcs, jointly measurable in the arc
  (product σ-algebra) and the point;
* **`ae_of_glue`**: a measurable event of `(D, Y)` holding on the glued space holds for `(D, Y)` itself when `D` is
  almost surely a Borel function of the field and the kernel is the conditional law of `Y` given the field — here
  `D` is the flow line (field-determined, `exists_flowLineMap_of_heights`) and `Y` the counterflow's history;
* **`ae_cfPts_notMem_leftSideOf`**: almost surely no counterflow point at a rational time is in `E_L`;
* `ae_disjoint_cfRange_leftSideOf`: the completed counterflow range misses `E_L`;
* **`ae_negInv_trace_notMem_leftSideOf`**: every continuous generating trace `γ′` of `W′` (infinite lifetime) has
  `R(γ′(t)) ∉ E_L` at **every** time (continuity and openness of `E_L`). No trace existence is assumed or used.

R48: the inputs are `Prop411QStatement` (an input of Theorem 1.2's chain) and lemmas proved without Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC isOpen_H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Sec7.R7Outer

open Sec5.Cond44Ref (cfPts cfHistory cfRange cfField)
open Theorem15D5 (Reach ratPt)
open WangWu (IsProperArc arcRange glueMeasure negInv)
open Sec5.Prop55Half (IsSeedProper)
open StripHeights44 (IsHeightBounded44)

/-! ### A countable description of the left side of a proper arc -/

/-- A countable family whose closure is `arcRange γ ∪ {Im ≤ 0}` (for a proper arc `γ`): the values of `γ` at
nonnegative rational times and the rational points of the closed lower half-plane. -/
def arcEnum (γ : ℝ → ℂ) : ℚ ⊕ (ℚ × ℚ) → ℂ
  | Sum.inl q => γ (max (q : ℝ) 0)
  | Sum.inr p => if (p.2 : ℝ) ≤ 0 then ratPt p else 0

theorem closure_range_arcEnum {γ : ℝ → ℂ} (hγ : IsProperArc γ) :
    closure (range (arcEnum γ)) = arcRange γ ∪ {z : ℂ | z.im ≤ 0} := by
  have hcl : IsClosed (arcRange γ ∪ {z : ℂ | z.im ≤ 0}) :=
    hγ.isClosed_arcRange.union (isClosed_le Complex.continuous_im continuous_const)
  refine Subset.antisymm (closure_minimal ?_ hcl) (union_subset ?_ ?_)
  · rintro _ ⟨(q | p), rfl⟩
    · exact Or.inl ⟨_, mem_Ici.2 (le_max_right _ _), rfl⟩
    · right
      simp only [arcEnum, mem_ofPred_eq]
      split_ifs with hp
      · simpa [ratPt] using hp
      · simp
  · refine Sec5.Cond44Ref.arcRange_subset_closure_of_forall_rat hγ fun t ht => subset_closure ⟨Sum.inl t, ?_⟩
    simp only [arcEnum, max_eq_left (show (0 : ℝ) ≤ t by exact_mod_cast ht.le)]
  · intro z hz
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨q₁, hq₁⟩ := exists_rat_btwn (show z.re - ε / 2 < z.re + ε / 2 by linarith)
    obtain ⟨q₂, hq₂⟩ := exists_rat_btwn (show z.im - ε / 2 < z.im by linarith)
    have hq₂0 : (q₂ : ℝ) ≤ 0 := le_trans hq₂.2.le hz
    refine ⟨arcEnum γ (Sum.inr (q₁, q₂)), ⟨_, rfl⟩, ?_⟩
    simp only [arcEnum, hq₂0, ↓reduceIte]
    rw [Complex.dist_eq]
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
    simp only [ratPt, Complex.sub_re, Complex.sub_im]
    have h1 : |z.re - q₁| < ε / 2 := abs_sub_lt_iff.2 ⟨by linarith [hq₁.1], by linarith [hq₁.2]⟩
    have h2 : |z.im - q₂| < ε / 2 := abs_sub_lt_iff.2 ⟨by linarith [hq₂.1], by linarith [hq₂.2]⟩
    linarith

theorem compl_closure_range_arcEnum {γ : ℝ → ℂ} (hγ : IsProperArc γ) :
    (closure (range (arcEnum γ)))ᶜ = H \ arcRange γ := by
  rw [closure_range_arcEnum hγ]
  ext z
  simp only [mem_compl_iff, mem_union, mem_ofPred_eq, not_or, not_le, Set.mem_sdiff]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- **The left side of an arc by rational data**: `z` is reached by a rational polygonal path in
`ℍ ∖ arcRange γ` from a rational point of a rational half-disc at a negative real point that misses the arc. -/
def LeftQ (γ : ℝ → ℂ) (z : ℂ) : Prop :=
  ∃ (x r : ℚ) (w : ℚ × ℚ) (k : ℕ), x < 0 ∧ 0 < r ∧
    (∀ q : ℚ, γ (max (q : ℝ) 0) ∉ Sec5.Cond44Ref.halfDisc x r) ∧
    ratPt w ∈ Sec5.Cond44Ref.halfDisc x r ∧ Reach (closure (range (arcEnum γ)))ᶜ (ratPt w) k z

/-- **`LeftQ` is the left side** of a proper arc. -/
theorem leftQ_iff {γ : ℝ → ℂ} (hγ : IsProperArc γ) {z : ℂ} : LeftQ γ z ↔ z ∈ leftSideOf (arcRange γ) := by
  have hdis : Disjoint (arcRange γ) (leftSideOf (arcRange γ)) := disjoint_left.2 fun _ hz hL => hL.1.2 hz
  rw [Sec5.Cond44Ref.mem_leftSideOf_iff_leftReach hγ subset_rfl hdis]
  have hU : IsOpen (H \ arcRange γ) := isOpen_H.sdiff hγ.isClosed_arcRange
  have hdisc : ∀ x r : ℚ, (∀ q : ℚ, γ (max (q : ℝ) 0) ∉ Sec5.Cond44Ref.halfDisc x r) ↔
      Disjoint (Sec5.Cond44Ref.halfDisc x r) (arcRange γ) := by
    intro x r
    constructor
    · intro hq
      rw [disjoint_comm, Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
      intro hne
      obtain ⟨q, hq0, hqU⟩ := (Sec5.Cond44Ref.exists_rat_mem_iff hγ (Sec5.Cond44Ref.isOpen_halfDisc x r)).2 hne
      exact hq q (by rwa [max_eq_left hq0])
    · intro hd q hq
      exact disjoint_left.1 hd hq ⟨_, mem_Ici.2 (le_max_right _ _), rfl⟩
  constructor
  · rintro ⟨x, r, w, k, hx, hr, hq, hw, hR⟩
    have hz := hR.mem
    rw [compl_closure_range_arcEnum hγ] at hR hz
    exact ⟨hz.1, hz.2, x, r, w, hx, hr, (hdisc x r).1 hq, hw, hR.mem_connectedComponentIn⟩
  · rintro ⟨-, -, x, r, w, hx, hr, hd, hw, hc⟩
    obtain ⟨k, hk⟩ := (Theorem15D5.mem_connectedComponentIn_iff_exists_reach hU).1 hc
    refine ⟨x, r, w, k, hx, hr, (hdisc x r).2 hd, hw, ?_⟩
    rwa [compl_closure_range_arcEnum hγ]

/-- **`LeftQ` is measurable** in a measurable arc (product σ-algebra on `ℝ → ℂ`) and a measurable point. -/
theorem measurableSet_leftQ {X : Type*} [MeasurableSpace X] {γ : X → ℝ → ℂ} (hγ : ∀ s, Measurable fun x => γ x s)
    {z : X → ℂ} (hz : Measurable z) : MeasurableSet {x | LeftQ (γ x) (z x)} := by
  have hf : ∀ i, Measurable fun x => arcEnum (γ x) i := by
    rintro (q | p)
    · exact hγ _
    · exact measurable_const
  refine measurableSet_setOfPred.2 (Measurable.exists fun x₀ => Measurable.exists fun r => Measurable.exists
    fun w => Measurable.exists fun k => ?_)
  refine measurable_const.and (measurable_const.and ((Measurable.forall fun q => ?_).and
    (measurable_const.and (measurableSet_setOfPred.1 (Theorem15D5.measurableSet_reach hf measurable_const k hz)))))
  exact (measurableSet_setOfPred.1 (hγ _ (Sec5.Cond44Ref.isOpen_halfDisc x₀ r).measurableSet)).not


/-! ### From the glued space to the given coupling -/

/-- **Transfer from the glued space.** Let `k` be a conditional law of `Y` given `X` (`P.map (X, Y) = P.map X ⊗ₘ k`)
and `D` almost surely a Borel function `G` of `X`. A measurable event of `(D, sample)` holding almost surely on the
glued space `P ⊗ k(X)` holds almost surely for `(D, Y)` itself. -/
theorem ae_of_glue {Ω α β E : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace E] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → α} (hX : Measurable X) {Y : Ω → β}
    (hY : Measurable Y) (k : Kernel α β) [IsMarkovKernel k] (hk : P.map (fun ω => (X ω, Y ω)) = P.map X ⊗ₘ k)
    {G : α → E} (hG : Measurable G) {D : Ω → E} (hD : ∀ᵐ ω ∂P, D ω = G (X ω)) {S : Set (E × β)}
    (hS : MeasurableSet S) (hglue : ∀ᵐ p ∂(glueMeasure P k X hX), (D p.1, p.2) ∈ S) :
    ∀ᵐ ω ∂P, (D ω, Y ω) ∈ S := by
  have hD' := WangWu.ae_glue_fst (μ := P) k hX hD
  have hS' : MeasurableSet {q : α × β | (G q.1, q.2) ∈ S} := ((hG.comp measurable_fst).prodMk measurable_snd) hS
  have hF : Measurable fun p : Ω × β => (X p.1, p.2) := (hX.comp measurable_fst).prodMk measurable_snd
  have hmap : (glueMeasure P k X hX).map (fun p => (X p.1, p.2)) = P.map (fun ω => (X ω, Y ω)) := by
    rw [hk]
    refine Measure.ext_prod fun {s t} hs ht => ?_
    rw [Measure.map_apply hF (hs.prod ht)]
    have h1 : (fun p : Ω × β => (X p.1, p.2)) ⁻¹' (s ×ˢ t) = (X ⁻¹' s) ×ˢ t := by ext; simp
    rw [h1, WangWu.glueMeasure_apply_prod k hX (hX hs) ht, Measure.compProd_apply_prod hs ht,
      setLIntegral_map hs (k.measurable_coe ht) hX]
  have h0 : ∀ᵐ q ∂((glueMeasure P k X hX).map fun p => (X p.1, p.2)), (G q.1, q.2) ∈ S := by
    refine (ae_map_iff hF.aemeasurable hS').2 ?_
    filter_upwards [hglue, hD'] with p hp hDp
    rw [hDp] at hp
    exact hp
  rw [hmap] at h0
  have h1 := (ae_map_iff (hX.prodMk hY).aemeasurable hS').1 h0
  filter_upwards [h1, hD] with ω h1 hDω
  rw [hDω]
  exact h1

/-! ### The counterflow avoids the left side of `β_L` -/

/-- The counterflow field of the angle-`π/2` flow line's coupling field is the field itself:
`(h + (π/2)χ) − (π/2)χ = h`. -/
theorem cfField_flowField_half (κ : ℝ) (f : DistOn upperHalfPlaneOpens) :
    cfField κ (Exist.flowField 0 (π / 2 * chiC κ) f) = f := by
  ext φ
  simp only [cfField, Exist.flowField_apply, Sec5.GlueCond.pushTest_shiftChart_zero]
  ring

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}

/-- **The counterflow avoids `E_L` at rational times** (supplement §5.1: "`η` avoids `E_R ∪ E_L` throughout its
lifetime", left half; Proposition 4.11, R48-safe). On any probability space carrying a GFF `h` with data `b` whose
angle-`π/2` flow-line word satisfies (4.4), a centred counterflow `W′` of `h` and the angle-`π/2` flow line `β_L` of
`h`: almost surely `β_L` is seed-proper and no counterflow point at a rational time lies in `leftSideOf β_L`. -/
theorem ae_cfPts_notMem_leftSideOf (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b J) (hθ : IsHeightBounded44 κ b J (π / 2)) {Ω : Type u}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b J) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') {β : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hβ : IsFlowLine κ b J 0 (π / 2) P h β ζ) :
    ∀ᵐ ω ∂P, IsSeedProper (β ω) ∧ ∀ s : ℚ, cfPts (cfHistory W' ζ' ω) s ∉ leftSideOf (range (β ω)) := by
  have hreg := IsFlowLine.ae_regular_of_heights hκ hκ4 hb hθ hβ
  obtain ⟨Φ, hΦm, hΦ⟩ :=
    exists_flowLineMap_of_heights (Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411) hκ hκ4 hb hθ
  have hΦβ := hΦ P h hh β ζ hβ
  obtain ⟨h', 𝓕, W, VL, VR, B, htr, hC, hgen⟩ := hβ
  have hF := Theorem15.isOrderedForceWord_flowLine b J 0
  have h44 := cond44_of_heights hκ hb hθ
  have hadm := hasAdmissiblePartialSums_of_heights hκ hκ4 hb hθ
  have hXe : (fun ω => cfField κ (h' ω)) = h := funext fun ω => by
    rw [Lemma75Bridge.eq_flowField_of_isTranslateAddConst (htr ω)]
    exact cfField_flowField_half κ (h ω)
  have hXm : Measurable fun ω => cfField κ (h' ω) := (Sec5.Cond44Ref.measurable_cfField κ).comp hC.2.1
  have hYm := Sec5.Cond44Ref.measurable_cfHistory
    (Sec5.Cond44Ref.isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf)
  set k := condDistrib (cfHistory W' ζ') h P with hkdef
  have hk : P.map (fun ω => (h ω, cfHistory W' ζ' ω)) = P.map h ⊗ₘ k :=
    (compProd_map_condDistrib hh.1.aemeasurable hYm.aemeasurable).symm
  have hlaw : P.map (fun ω => cfField κ (h' ω)) = P.map h := by rw [hXe]
  have hglue := h411 κ hκ hκ4 _ _ _ _ hF h44 P 𝓕 W VL VR B ζ h' hC P h W' ζ' hcf hlaw k hk
  have hk' : P.map (fun ω => ((fun ω => cfField κ (h' ω)) ω, cfHistory W' ζ' ω)) =
      P.map (fun ω => cfField κ (h' ω)) ⊗ₘ k := by
    have e2 : (fun ω => (cfField κ (h' ω), cfHistory W' ζ' ω)) = fun ω => (h ω, cfHistory W' ζ' ω) :=
      funext fun ω => by rw [show cfField κ (h' ω) = h ω from congrFun hXe ω]
    rw [e2, hXe]
    exact hk
  set G : DistOn upperHalfPlaneOpens → ℝ → ℂ := fun f s => (Φ f).2 s.toNNReal with hGdef
  have hGm : Measurable G :=
    measurable_pi_iff.2 fun s => (measurable_pi_apply _).comp (measurable_snd.comp hΦm)
  have hline := Sec5.Cond44Ref.ae_seedLine_of_admissible hκ hκ4.le hF hadm hC.1
  have hDG : ∀ᵐ ω ∂P, WangWu.seedLine ζ W ω = G (cfField κ (h' ω)) ∧ IsProperArc (WangWu.seedLine ζ W ω) ∧
      arcRange (WangWu.seedLine ζ W ω) = range (β ω) := by
    filter_upwards [hline, hgen, hΦβ, hC.1.2.2.2.2] with ω hl hg hΦω hpath
    obtain ⟨hζ, -, hpa⟩ := hl
    obtain ⟨hw0, -, -, hcw, -⟩ := hpath
    have hg' : IsGeneratingTrace (fun t => W t ω) (ζ ω) (β ω) := by
      have e : (fun t => β ω t - ((0 : ℝ) : ℂ)) = β ω := funext fun t => by simp
      rw [← e]
      exact hg
    have hsl : WangWu.seedLine ζ W ω = fun s : ℝ => β ω s.toNNReal := by
      funext s
      simp only [WangWu.seedLine]
      have hk : (fun t => InteractingSLE.killedProc ζ W t ω) = fun t => W t ω :=
        funext (InteractingSLE.killedProc_of_eq_top hζ)
      rw [hk]
      exact LP.traceAt_eq_of_isGeneratingTrace hg' hcw hw0 (by rw [hζ]; exact ENNReal.coe_lt_top)
    refine ⟨?_, hpa, ?_⟩
    · rw [hsl, show cfField κ (h' ω) = h ω from congrFun hXe ω]
      funext s
      simp only [hGdef]
      exact (hΦω.2 _ (by rw [hζ]; exact le_top)).symm
    · rw [hsl]
      exact Sec5.Cond44Ref.arcRange_toNNReal (β ω)
  set S : Set ((ℝ → ℂ) × LawUnique.HistorySpace 0 0) := {q | ∀ s : ℚ, ¬ LeftQ q.1 (cfPts q.2 s)}
    with hSdef
  have hS : MeasurableSet S := by
    rw [hSdef, ofPred_forall]
    exact MeasurableSet.iInter fun s => (measurableSet_leftQ (γ := fun q : (ℝ → ℂ) × _ => q.1)
      (fun t => (measurable_pi_apply t).comp measurable_fst)
      ((Sec5.Cond44Ref.measurable_cfPts s).comp measurable_snd)).compl
  have hglueS : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h' ω)) hXm),
      (WangWu.seedLine ζ W p.1, p.2) ∈ S := by
    filter_upwards [hglue, WangWu.ae_glue_fst (μ := P) k hXm hDG] with p hp hq s hL
    exact hp.2 s ((leftQ_iff hq.2.1).1 hL)
  have htrans := ae_of_glue hXm hYm k hk' hGm (hDG.mono fun ω hω => hω.1) hS hglueS
  filter_upwards [htrans, hDG, hreg] with ω hS' hD hr
  refine ⟨hr.2, fun s hmem => hS' s ((leftQ_iff hD.2.1).2 ?_)⟩
  rw [hD.2.2]
  exact hmem

/-- A seed-proper curve, read on `ℝ`, is a proper arc with the same range. -/
theorem IsSeedProper.isProperArc {γ : ℝ≥0 → ℂ} (hγ : IsSeedProper γ) :
    IsProperArc (Lemma71I.realPath γ) ∧ arcRange (Lemma71I.realPath γ) = range γ :=
  ⟨(IsSeedProper.isSimpleProper hγ).isProperArc, Lemma71I.arcRange_realPath γ⟩

/-- `leftSideOf` of a seed-proper curve is open. -/
theorem isOpen_leftSideOf_range {γ : ℝ≥0 → ℂ} (hγ : IsSeedProper γ) : IsOpen (leftSideOf (range γ)) := by
  have h := Sec5.Cond44Ref.isOpen_leftSideOf_arcRange (IsSeedProper.isProperArc hγ).1
  rwa [(IsSeedProper.isProperArc hγ).2] at h

/-- **The completed counterflow range misses `E_L`.** -/
theorem ae_disjoint_cfRange_leftSideOf (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b J) (hθ : IsHeightBounded44 κ b J (π / 2)) {Ω : Type u}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b J) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') {β : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hβ : IsFlowLine κ b J 0 (π / 2) P h β ζ) :
    ∀ᵐ ω ∂P, Disjoint (cfRange (cfHistory W' ζ' ω)) (leftSideOf (range (β ω))) := by
  filter_upwards [ae_cfPts_notMem_leftSideOf h411 hκ hκ4 hb hθ hh hcf hβ] with ω hω
  have hA := IsSeedProper.isProperArc hω.1
  have h := Sec5.Cond44Ref.disjoint_closure_leftSideOf hA.1 (S := range (cfPts (cfHistory W' ζ' ω)))
    (by rintro _ ⟨s, rfl⟩; rw [hA.2]; exact hω.2 s)
  rwa [hA.2] at h

/-- The counterflow point at a positive rational time is the image under `R(z) = −1/z` of the driver's trace, when
the lifetime is infinite and the driver continuous. -/
theorem cfPts_cfHistory_eq {Ω : Type*} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {ω : Ω} (hζ : ζ' ω = ⊤)
    (hc : Continuous fun t => W' t ω) (h0 : W' 0 ω = 0) {η' : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (fun t => W' t ω) ⊤ η') {q : ℚ} (hq : 0 < q) :
    cfPts (cfHistory W' ζ' ω) q = negInv (η' (q : ℝ).toNNReal) := by
  have hlt : (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (cfHistory W' ζ' ω).1 := by
    change _ < ζ' ω
    rw [hζ]
    exact ENNReal.coe_lt_top
  simp only [cfPts, hq, hlt, and_self, ↓reduceIte, WangWu.revLine]
  rw [cfHistory, WangWu.histLine_killedHistory hζ hc]
  congr 1
  simp only [WangWu.seedLine]
  have hk : (fun t => InteractingSLE.killedProc ζ' W' t ω) = fun t => W' t ω :=
    funext (InteractingSLE.killedProc_of_eq_top hζ)
  rw [hk]
  exact LP.traceAt_eq_of_isGeneratingTrace hη hc.continuousOn h0 ENNReal.coe_lt_top

/-- **Every trace of the counterflow avoids `E_L` at every time** (supplement §5.1: "`η` avoids `E_R ∪ E_L`
throughout its lifetime", left half). Almost surely, on infinite lifetime, for every continuous generating trace `γ′`
of the counterflow driver `W′` (chart `R`), the physical counterflow `R(γ′(t)) = −1/γ′(t)` is never on the left side of
`β_L`. Trace existence is neither assumed nor used (the statement is vacuous without a trace). -/
theorem ae_negInv_trace_notMem_leftSideOf (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (hκ : 0 < κ)
    (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J) (hθ : IsHeightBounded44 κ b J (π / 2)) {Ω : Type u}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b J) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') {β : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hβ : IsFlowLine κ b J 0 (π / 2) P h β ζ) :
    ∀ᵐ ω ∂P, ζ' ω = ⊤ → ∀ η' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ η' →
      ∀ t : ℝ≥0, negInv (η' t) ∉ leftSideOf (range (β ω)) := by
  have hpathW : ∀ᵐ ω ∂P, W' 0 ω = 0 ∧ ContinuousOn (fun t => W' t ω) {t | (t : ℝ≥0∞) < ζ' ω} := by
    obtain ⟨b', J', g, -, -, hd⟩ := hcf
    obtain ⟨g', 𝓕', VL', VR', B', -, hC'⟩ := hd
    filter_upwards [hC'.1.2.2.2.2] with ω hp
    exact ⟨hp.1, hp.2.2.2.1⟩
  filter_upwards [ae_cfPts_notMem_leftSideOf h411 hκ hκ4 hb hθ hh hcf hβ, hpathW] with ω hω hpω hζ η' hη t hmem
  have hc : Continuous fun t => W' t ω := by
    have := hpω.2
    rw [hζ] at this
    exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
  have hηc : Continuous η' := continuousOn_univ.1 (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hL := isOpen_leftSideOf_range hω.1
  by_cases hne : η' t = 0
  · rw [hne] at hmem
    simp only [negInv, inv_zero, neg_zero] at hmem
    exact Sec5.Cond44Ref.not_zero_mem_H hmem.1.1
  have ht0 : 0 < t := by
    refine pos_of_ne_zero fun ht => hne ?_
    rw [ht]
    exact hη.1
  have hcont : ContinuousAt (fun u : ℝ≥0 => negInv (η' u)) t :=
    (WangWu.continuousAt_negInv hne).comp hηc.continuousAt
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hcont.preimage_mem_nhds (hL.mem_nhds hmem))
  have ht0' : (0 : ℝ) < t := by exact_mod_cast ht0
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt (show (t : ℝ) - ε < t by linarith) ht0')
  have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (le_max_right _ _) hq1
  have hqε : (t : ℝ) - ε < q := lt_of_le_of_lt (le_max_left _ _) hq1
  have hu : ((q : ℝ).toNNReal : ℝ≥0) ∈ Metric.ball t ε := by
    rw [Metric.mem_ball, NNReal.dist_eq, Real.coe_toNNReal _ hq0.le, abs_sub_lt_iff]
    constructor <;> linarith
  have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
  have hin := hball hu
  simp only [mem_preimage] at hin
  rw [← cfPts_cfHistory_eq hζ hc hpω.1 hη hq0'] at hin
  exact hω.2 q hin

end InteractingSLE.Sec7.R7Outer
