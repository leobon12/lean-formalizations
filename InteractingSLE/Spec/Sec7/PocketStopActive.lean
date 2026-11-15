/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketUnionPtInput

/-!
# The marked union law at the ambient time `T(q)`: the canonical set `K_q = ℍ ∖ activeDom`

Packet PROVE-STRIPSYS33. Specification §7.4: Aux. lemma 124 (`source/spec/p385-432.md` L171–L196, pp. 393–394:
"Assume the marked optional union law for `A ∪ R_t` … Then `B ∪ R_T` has the corresponding full marked local-set law"),
Aux. lemma 125's proof (pp. 396–397: "the relative active domain at `S` is exactly the target component of
`C ∖ R_{T(S)}`"), and Aux. lemmas 35–36 (`source/spec/p145-192.md` L908–L940: "Assume the marked stopping-time
local-set law, retaining these curve labels, the stopped counterflow history, and the canonical revealed germs").

PROVE-STRIPSYS32 reduced the pocket inputs to `PocketUnionPt.PocketStopLaw` (the marked union law of a set `K_q` at the
ambient time `T(q)`) and `PocketUnionPt.PocketStopMeanAt` (the central pocket mean on `C ∩ (ℍ ∖ F_q)`). Here `K_q` is
chosen canonically as the complement of the relative active domain,

  `K_q = ℍ ∖ activeDom = (ℍ ∖ C) ∪ (F_q ∩ ℍ)` on the live event `A ∩ {q < ζ}`, `K_q = ℍ` off it,

so that `ℍ ∖ K_q` is the active domain itself (the domain of the relative chart `c.loewner w q`, used for the mean in
`PocketStopMean.lean`). On the live event `K_q` is Aux. lemma 124's set `B ∪ R_{T(q)}` (`B = ℍ ∖ C` the exterior of the
pocket) read inside `ℍ`. Everything in `PocketStopLaw` except the marked local-set law itself is proved here:

* the pathwise clauses (frontier of the pocket and hull inside `K_q`, `K_q ∩ C ⊆ F_q`) and the regularity
  (`K_q ⊆ ℍ`, `ℍ ∖ K_q` open) from the ambient-domain identity of PROVE-STRIPSYS32 (`activeDom = C ∩ (ℍ ∖ F_q)`);
* the hitting measurability and the history-marked locality of `K_q` from those of **any** random set `E` that equals
  `B ∪ R_{T(q)}` on the live event (`PocketStopUnionLaw`, the named field-level input: Aux. lemma 124's/35's marked
  union law at the stop `T(q)`, with the relative history as marks). Off the live event `K_q = ℍ`, whose avoidance
  events of nonempty open sets are empty, so only the live part of `E` matters.

## Main results

* `activeCompl`, `liveExt`, `activeCompl_eq_liveExt`;
* `activeCompl_props`, `activeCompl_regular`;
* `measurable_liveExt`, `isHistoryAvoidanceLocal_liveExt`;
* `PocketStopUnionLaw` (named input), **`pocketStopLaw_activeCompl`**.

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStop

open PocketTraversal PocketAdapt Lemma71C LocalSets WholeField PocketCoupling PocketUnionPt

section Active

variable {Ω : Type*}

/-- **The canonical marked set at relative capacity time `q`**: the complement in `ℍ` of the relative active domain
(`ℍ` off the live event, where the active domain is empty). -/
def activeCompl (A : Set Ω) (γ : Ω → ℝ → ℂ) (c : Ω → Chart) (q : ℝ≥0) (ω : Ω) : Set ℂ :=
  H \ activeDom A γ c q ω

open Classical in
/-- **Aux. lemma 124's set `B ∪ R_{T(q)}` on the live event**, read inside `ℍ` (`B = ℍ ∖ C` the exterior of the pocket,
`F` the counterflow hull at `T(q)`), and `ℍ` off the live event. -/
def liveExt (A : Set Ω) (γ : Ω → ℝ → ℂ) (C F : Ω → Set ℂ) (q : ℝ≥0) (ω : Ω) : Set ℂ :=
  if ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω) then extHullSet (C ω) (F ω) else H

theorem liveExt_of_live {A : Set Ω} {γ : Ω → ℝ → ℂ} {C F : Ω → Set ℂ} {q : ℝ≥0} {ω : Ω}
    (hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)) : liveExt A γ C F q ω = extHullSet (C ω) (F ω) := by
  simp only [liveExt, hl, and_self, ↓reduceIte]

theorem liveExt_of_not_live {A : Set Ω} {γ : Ω → ℝ → ℂ} {C F : Ω → Set ℂ} {q : ℝ≥0} {ω : Ω}
    (hl : ¬ (ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω))) : liveExt A γ C F q ω = H := by
  simp only [liveExt, hl, ↓reduceIte]

/-- On the live event the canonical set is `B ∪ R_{T(q)}` inside `ℍ`; off it, both are `ℍ`. -/
theorem activeCompl_eq_liveExt {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart} {q : ℝ≥0} {C F : Ω → Set ℂ}
    (hact : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → activeDom A γ c q ω = C ω ∩ (H \ F ω)) :
    activeCompl A γ c q = liveExt A γ C F q := by
  funext ω
  by_cases hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)
  · rw [liveExt_of_live hl, activeCompl, hact ω hl.1 hl.2]
    ext z
    simp only [Set.mem_sdiff, mem_inter_iff, extHullSet, mem_union, mem_compl_iff]
    tauto
  · rw [liveExt_of_not_live hl, activeCompl, activeDom_eq_empty hl, sdiff_empty]

/-- **The pathwise clauses of the marked union law** for the canonical set, on the live event: it contains the
frontier of the open pocket in `ℍ` and the hull in `ℍ`, and meets the pocket only inside the hull. -/
theorem activeCompl_props {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart} {q : ℝ≥0} {C F : Ω → Set ℂ} {ω : Ω}
    (hact : activeDom A γ c q ω = C ω ∩ (H \ F ω))
    (hCo : IsOpen (C ω)) :
    frontier (C ω) ∩ H ⊆ activeCompl A γ c q ω ∧ F ω ∩ H ⊆ activeCompl A γ c q ω ∧
      activeCompl A γ c q ω ∩ C ω ⊆ F ω := by
  simp only [activeCompl, hact]
  refine ⟨fun z hz => ⟨hz.2, fun hzD => ?_⟩, fun z hz => ⟨hz.2, fun hzD => hzD.2.2 hz.1⟩,
    fun z hz => ?_⟩
  · rw [hCo.frontier_eq] at hz
    exact hz.1.2 hzD.1
  · by_contra hzF
    exact hz.1.2 ⟨hz.2, hz.1.1, hzF⟩

/-- **Regularity of the canonical set**: it lies in `ℍ`, and its complement in `ℍ` is open (the pocket is open and the
hull is relatively closed on the live event; the complement is empty off it). -/
theorem activeCompl_regular {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart} {q : ℝ≥0} {C F : Ω → Set ℂ}
    (hact : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → activeDom A γ c q ω = C ω ∩ (H \ F ω))
    (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hFo : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ F ω)) (ω : Ω) :
    activeCompl A γ c q ω ⊆ H ∧ IsOpen (H \ activeCompl A γ c q ω) := by
  refine ⟨sdiff_subset, ?_⟩
  have e : H \ activeCompl A γ c q ω = activeDom A γ c q ω := by
    rw [activeCompl, sdiff_sdiff_cancel_left]
    by_cases hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)
    · rw [hact ω hl.1 hl.2]
      exact inter_subset_right.trans sdiff_subset
    · rw [activeDom_eq_empty hl]
      exact empty_subset _
  rw [e]
  by_cases hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)
  · rw [hact ω hl.1 hl.2]
    exact (hCo ω hl.1).inter (hFo ω hl.1 hl.2)
  · rw [activeDom_eq_empty hl]
    exact isOpen_empty

end Active

/-! ### Measurability and locality from any set equal to `B ∪ R_{T(q)}` on the live event -/

section Law

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **Hitting measurability on the live event**: if `E` is hitting-measurable and equals `B ∪ R_{T(q)}` on the live
event `L ∈ mΩ`, the live set `liveExt` is hitting-measurable. -/
theorem measurable_liveExt {A : Set Ω} {γ : Ω → ℝ → ℂ} {C F : Ω → Set ℂ} {q : ℝ≥0}
    (hL : MeasurableSet {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)}) {E : Ω → Set ℂ}
    (hE : Measurable[mΩ, hittingSigma] E)
    (hEq : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → E ω = extHullSet (C ω) (F ω)) :
    Measurable[mΩ, hittingSigma] (liveExt A γ C F q) := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  classical
  have e : liveExt A γ C F q = {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)}.piecewise E fun _ => H := by
    funext ω
    by_cases hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)
    · rw [liveExt_of_live hl, piecewise_eq_of_mem _ _ _ (show ω ∈ {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)} from hl),
        hEq ω hl.1 hl.2]
    · rw [liveExt_of_not_live hl, piecewise_eq_of_notMem _ _ _
        (show ω ∉ {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)} from hl)]
  rw [e]
  exact hE.piecewise hL measurable_const

/-- **History-marked locality on the live event**: if `E` satisfies the history-marked avoidance criterion for the
marks `ℋ`, the live event is an `ℋ`-event, and `E = B ∪ R_{T(q)}` on it, then the live set satisfies the criterion for
`ℋ`. For a nonempty open `U ⊆ ℍ` the avoidance event of the live set is the avoidance event of `E` on the live event
(off it the live set is `ℍ ⊇ U`); for `U = ∅` both avoidance events are everything. -/
theorem isHistoryAvoidanceLocal_liveExt {A : Set Ω} {γ : Ω → ℝ → ℂ} {C F : Ω → Set ℂ} {q : ℝ≥0}
    (hL : MeasurableSet[ℋ] {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)}) {E : Ω → Set ℂ}
    {h : Ω → DistOn upperHalfPlaneOpens} (hloc : IsHistoryAvoidanceLocal ℋ E h P)
    (hEq : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → E ω = extHullSet (C ω) (F ω)) :
    IsHistoryAvoidanceLocal ℋ (liveExt A γ C F q) h P := by
  intro U G hUH hG hd F₀ hF₀
  rcases (U : Set ℂ).eq_empty_or_nonempty with hU | hU
  · obtain ⟨g, hg, hge⟩ := hloc U G hUH hG hd F₀ hF₀
    refine ⟨g, hg, ?_⟩
    have e : {ω | Disjoint (liveExt A γ C F q ω) U} ∩ F₀ = {ω | Disjoint (E ω) U} ∩ F₀ := by
      simp only [hU, disjoint_empty, ofPred_true]
    rw [e]
    exact hge
  · obtain ⟨g, hg, hge⟩ := hloc U G hUH hG hd (F₀ ∩ {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)}) (hF₀.inter hL)
    refine ⟨g, hg, ?_⟩
    have e : {ω | Disjoint (liveExt A γ C F q ω) U} ∩ F₀ =
        {ω | Disjoint (E ω) U} ∩ (F₀ ∩ {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)}) := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq]
      by_cases hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)
      · rw [liveExt_of_live hl, hEq ω hl.1 hl.2]
        tauto
      · rw [liveExt_of_not_live hl]
        refine ⟨fun h' => absurd h'.1 ?_, fun h' => absurd h'.2.2 hl⟩
        obtain ⟨z, hz⟩ := hU
        exact Set.not_disjoint_iff.2 ⟨z, hUH hz, hz⟩
    rw [e]
    exact hge

end Law

/-! ### The marked union law at `T(q)` from the named input -/

section UnionLaw

variable {Ω : Type*}

/-- **The marked union law of `B ∪ R_{T(q)}` at the ambient stop** (named field-level input; Aux. lemma 124's
hypothesis "the marked optional union law for `A ∪ R_t`" and its conclusion for `B ∪ R_T`, Aux. lemma 35's "marked
stopping-time local-set law, retaining these curve labels, the stopped counterflow history", Lemma 6.2 at the stop
`T(q)` of the counterflow enlarged by the walls): some hitting-measurable random set `E`, satisfying the history-marked
avoidance criterion (Aux. lemma 18) for the relative history `𝓦 ∨ σ(A ∩ prefix events up to q)`, equals
`ℍ ∩ ((ℍ ∖ C) ∪ F)` on the live event `A ∩ {q < ζ}`. -/
def PocketStopUnionLaw (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (γ : Ω → ℝ → ℂ) (C F : Ω → Set ℂ) (h₀ : Ω → DistOn upperHalfPlaneOpens) (q : ℝ≥0) : Prop :=
  ∃ E : Ω → Set ℂ, Measurable[mΩ, hittingSigma] E ∧ IsHistoryAvoidanceLocal (locPrefixSigma 𝓦 A γ q) E h₀ P ∧
    ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → E ω = extHullSet (C ω) (F ω)

end UnionLaw

section Stop

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **`PocketStopLaw` for the canonical set `ℍ ∖ activeDom`** from the marked union law of `B ∪ R_{T(q)}`
(`PocketStopUnionLaw`), the ambient-domain identity `activeDom = C ∩ (ℍ ∖ F)` on the live event (PROVE-STRIPSYS32's
`activeDom_eq_inter`), the openness of the pocket and the relative closedness of the hull. -/
theorem pocketStopLaw_activeCompl {A : Set Ω} {γ : Ω → ℝ → ℂ} {q : ℝ≥0} (hpre : locPrefixSigma 𝓦 A γ q ≤ mΩ)
    {c : Ω → Chart} {C F : Ω → Set ℂ}
    (hact : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → activeDom A γ c q ω = C ω ∩ (H \ F ω))
    (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hFo : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ F ω))
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hU : PocketStopUnionLaw 𝓦 P A γ C F h₀ q) :
    PocketStopLaw 𝓦 P A γ C F h₀ (activeCompl A γ c q) q := by
  obtain ⟨E, hEm, hEloc, hEq⟩ := hU
  have hL := measurableSet_live (𝓦 := 𝓦) A γ q
  refine ⟨?_, Eventually.of_forall fun ω => activeCompl_regular hact hCo hFo ω, ?_, fun ω hω hq =>
    activeCompl_props (hact ω hω hq) (hCo ω hω)⟩
  · rw [activeCompl_eq_liveExt hact]
    exact measurable_liveExt (hpre _ hL) hEm hEq
  · rw [activeCompl_eq_liveExt hact]
    exact isHistoryAvoidanceLocal_liveExt hL hEloc hEq

end Stop

end InteractingSLE.Sec7.PocketStop
