/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCBLocal

/-!
# W5's local frames from the localized local completion (late cuts)

Packet PROVE-RLC-C. Source: Theorem W5's proof (`source/spec/p529-576.md` L140–L180, pp. 534–536), paragraph
"Incoming active rational cuts": "Choose the cuts sufficiently late that their fresh incoming arcs and short available
outgoing portions at `p` lie in a prescribed small physical neighborhood of `p`", and "The interior and real local
frames": "If `p ∈ ℍ`, choose its physical neighborhood disjoint from the original real line. […] Suppose `p` is real.
[…] Shrink the physical neighborhood to one on which the original height is one constant `C`, and which avoids both
original seeds."

`Supp9D.localCompletionAtContact_of_retained` / `Supp9D.w5LocalFrameStatement_of_inputs` (PROVE-W5-REST) consume the
unlocalized `Supp9D.RetainedLocalCompletionStatement`, which quantifies over all fresh arcs from the cuts (PROVE-RLC-B's
finding: that form is stronger than what W5's proof provides). Here the consumer is re-proved from the localized
statement `RLC.RetainedLocalCompletionLocStatement` (PROVE-RLC-B, `RLCBLocal.lean`): the cut window `δ` of
`Supp9D.exists_incomingCuts'` is chosen by continuity of both paths at the contact, so that `RLC.IsLocalContact` holds
at the selected dyadic cuts (`exists_localWindow`).

Main results: `localCompletionAtContact_of_retainedLoc`, `w5LocalFrameStatement_of_loc`, `w5Statement_of_loc`, and
`w5Statement_of_realLoc_param` (Theorem W5 from the named inputs of PROVE-RLC-A/B and the localized real-contact case
`RLC.RetainedLocalCompletionRealLocStatement`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Supp7 Supp9 Supp9D Sec2.Assembly

/-! ### The late-cut window -/

/-- A time in the window `(a − δ, a]` is within `δ` of `a`. -/
theorem dist_lt_of_tsub_lt {a δ x : ℝ≥0} (h : a - δ < x) (hx : x ≤ a) : dist x a < (δ : ℝ) := by
  rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hx))]
  by_contra hc
  push Not at hc
  have hle : x + δ ≤ a := by
    rw [← NNReal.coe_le_coe]
    push_cast
    linarith
  exact absurd (le_tsub_of_add_le_right hle) (not_le.2 h)

/-- Off a finite set, a real point has a punctured neighborhood free of that set. -/
theorem exists_pos_forall_notMem_finset (J : Finset ℝ) (x : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : ℝ, |y - x| < ε → y ≠ x → y ∉ J := by
  have hO : IsOpen ((J.erase x : Set ℝ)ᶜ) := (J.erase x).finite_toSet.isClosed.isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO x (by simp)
  refine ⟨ε, hε, fun y hy hyx hyJ => hball ?_ (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hyx, hyJ⟩))⟩
  rw [mem_ball, Real.dist_eq]
  exact hy

/-- **W5's late-cut window** (p. 535: "Choose the cuts sufficiently late that their fresh incoming arcs […] lie in a
prescribed small physical neighborhood of `p`"): at a contact `p = α(a) = β(τ)` where both paths are continuous and
which is neither seed, there is `δ > 0` such that every pair of cuts in `(a − δ, a) × (τ − δ, τ)` localizes the
contact (`IsLocalContact`). -/
theorem exists_localWindow (J : Finset ℝ) {α β : ℝ≥0 → ℂ} {a τ : ℝ≥0} (hαa : ContinuousAt α a)
    (hβτ : ContinuousAt β τ) (hp : α a = β τ) (hα0 : α 0 ≠ α a) (hβ0 : β 0 ≠ α a) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ r s : ℝ≥0, a - δ < r → τ - δ < s → IsLocalContact J α r a β s τ := by
  obtain ⟨ε, hε, hJ⟩ := exists_pos_forall_notMem_finset J (α a).re
  have h1 : 0 < ‖α 0 - α a‖ := norm_pos_iff.2 (sub_ne_zero.2 hα0)
  have h2 : 0 < ‖β 0 - α a‖ := norm_pos_iff.2 (sub_ne_zero.2 hβ0)
  obtain ⟨ρ, hρ, hρε, hρ1, hρ2, hρH⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ε ∧ ρ ≤ ‖α 0 - α a‖ ∧ ρ ≤ ‖β 0 - α a‖ ∧
      (α a ∈ H → ρ ≤ (α a).im) := by
    by_cases hpH : α a ∈ H
    · refine ⟨min (min ε ‖α 0 - α a‖) (min ‖β 0 - α a‖ (α a).im), ?_, ?_, ?_, ?_, fun _ => ?_⟩
      · exact lt_min (lt_min hε h1) (lt_min h2 hpH)
      · exact (min_le_left _ _).trans (min_le_left _ _)
      · exact (min_le_left _ _).trans (min_le_right _ _)
      · exact (min_le_right _ _).trans (min_le_left _ _)
      · exact (min_le_right _ _).trans (min_le_right _ _)
    · exact ⟨min ε (min ‖α 0 - α a‖ ‖β 0 - α a‖), lt_min hε (lt_min h1 h2), min_le_left _ _,
        (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _),
        fun h => absurd h hpH⟩
  obtain ⟨δ₁, hδ₁, hα⟩ := Metric.continuousAt_iff.1 hαa ρ hρ
  obtain ⟨δ₂, hδ₂, hβ⟩ := Metric.continuousAt_iff.1 hβτ ρ hρ
  refine ⟨(min δ₁ δ₂).toNNReal, Real.toNNReal_pos.2 (lt_min hδ₁ hδ₂), fun r s hr hs => ?_⟩
  have hδ : (((min δ₁ δ₂).toNNReal : ℝ≥0) : ℝ) = min δ₁ δ₂ := Real.coe_toNNReal _ (lt_min hδ₁ hδ₂).le
  refine ⟨ρ, hρ, fun x hrx hxa => ?_, fun y hsy hyτ => ?_, hρH, fun y hy hyx => hJ y (hy.trans_le hρε) hyx,
    hρ1, hρ2⟩
  · have hd := dist_lt_of_tsub_lt (hr.trans hrx) hxa
    rw [hδ] at hd
    exact mem_ball.2 (hα (hd.trans_le (min_le_left _ _)))
  · have hd := dist_lt_of_tsub_lt (hs.trans hsy) hyτ
    rw [hδ] at hd
    rw [hp]
    exact mem_ball.2 (hβ (hd.trans_le (min_le_right _ _)))

/-! ### The consumer with late cuts -/

/-- **W5's local frames, pathwise, with late cuts** (pp. 534–536): `Supp9D.localCompletionAtContact_of_retained` with
the local comparison needed only at localized contacts (`IsLocalContact`). The cuts are chosen by
`Supp9D.exists_incomingCuts'` inside the window of `exists_localWindow`. -/
theorem localCompletionAtContact_of_retainedLoc (J : Finset ℝ) {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}
    (hF : PathFacts α ζ₁ β ζ₂)
    (hW0b : ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ → (c : ℝ≥0∞) < ζ₂ → HasOrderedProperCompletions α a β c →
      ¬ HasCommonOpenSubarc α a β c)
    (hloc : ∀ u ∈ dyadSet, ∀ r ∈ dyadSet, Supp7.IsOrdinaryRetainedPair α ζ₁ u β ζ₂ r →
      ∀ a τ : ℝ≥0, u < a → (a : ℝ≥0∞) < ζ₁ → r < τ → (τ : ℝ≥0∞) < ζ₂ → α a = β τ →
        (∀ x : ℝ≥0, u < x → x ≤ a → α x ∉ α '' Icc 0 u ∪ β '' Icc 0 r) →
        (∀ y : ℝ≥0, r < y → y ≤ τ → β y ∉ α '' Icc 0 u ∪ β '' Icc 0 r) →
        IsLocalContact J α u a β r τ →
        ∃ a₂ b₂ : ℝ≥0, a < a₂ ∧ (a₂ : ℝ≥0∞) < ζ₁ ∧ τ < b₂ ∧ (b₂ : ℝ≥0∞) < ζ₂ ∧
          HasOrderedProperCompletions α a₂ β b₂) :
    LocalCompletionAtContact α ζ₁ β ζ₂ := by
  intro a τ ha hτ hτ0 hp hE
  have hle₁ : ∀ x : ℝ≥0, x ≤ a → (x : ℝ≥0∞) ≤ ζ₁ := fun x hx => (ENNReal.coe_le_coe.2 hx).trans ha.le
  have hle₂ : ∀ y : ℝ≥0, y ≤ τ → (y : ℝ≥0∞) ≤ ζ₂ := fun y hy => (ENNReal.coe_le_coe.2 hy).trans hτ.le
  have h₁ : 0 < ζ₁ := lt_of_le_of_lt zero_le ha
  have h₂ : 0 < ζ₂ := lt_of_le_of_lt zero_le hτ
  have ha0 : 0 < a := by
    refine pos_iff_ne_zero.2 fun ha0 => ?_
    have := hF.eq_zero_of_eq_α0 h₁ h₂ (hle₂ τ le_rfl) (by rw [← hp, ha0])
    exact absurd this hτ0.ne'
  have hα0 : α 0 ≠ α a := fun he =>
    ha0.ne (hF.αi (hle₁ 0 zero_le) (hle₁ a le_rfl) he)
  have hβ0 : β 0 ≠ α a := fun he =>
    hτ0.ne (hF.βi (hle₂ 0 zero_le) (hle₂ τ le_rfl) (he.trans hp))
  obtain ⟨δ, hδ, hwin⟩ := exists_localWindow J (continuousAt_of_coe_lt hF.αc ha)
    (continuousAt_of_coe_lt hF.βc hτ) hp hα0 hβ0
  have hinc := Supp9.earlierContactsIncreasing_of_contactOrder Supp9B.orderedContactOrderStatement hF.α0 hF.β0
    hF.seed hE
  have harc : ∀ v < τ, ¬ HasCommonOpenSubarc α a β v := fun v hv =>
    hW0b a v ha (lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hv) (hle₂ τ le_rfl)) (hE v hv)
  obtain ⟨r, s, hrR, hsS, hδr, hra, hδs, hsτ, -, hd1, hd2, hrβ, hsα⟩ :=
    exists_incomingCuts' (hF.αc.mono fun x hx => hle₁ x hx.2) (hF.βc.mono fun y hy => hle₂ y hy.2)
      (hF.αi.mono fun x hx => hle₁ x hx.2) (hF.βi.mono fun y hy => hle₂ y hy.2) hinc hp ha0 hτ0 harc
      (dense_goodCuts hF.αc hF.αno) (dense_goodCuts hF.βc hF.βno) hδ
  have hrζ : (r : ℝ≥0∞) < ζ₁ := lt_trans (ENNReal.coe_lt_coe.2 hra) ha
  have hsζ : (s : ℝ≥0∞) < ζ₂ := lt_trans (ENNReal.coe_lt_coe.2 hsτ) hτ
  obtain ⟨hrD, hrH⟩ : r ∈ dyadSet ∧ α r ∈ QuantumZipper.H := hrR.resolve_right fun h => absurd h (not_le.2 hrζ)
  obtain ⟨hsD, hsH⟩ : s ∈ dyadSet ∧ β s ∈ QuantumZipper.H := hsS.resolve_right fun h => absurd h (not_le.2 hsζ)
  have hαfresh : ∀ x ∈ Icc r a, α x ∉ β '' Icc 0 s := by
    rintro x hx ⟨y, hy, hyx⟩
    rcases hx.1.lt_or_eq with hrx | hrx
    · exact Set.disjoint_left.1 hd1 ⟨x, ⟨hrx, hx.2⟩, rfl⟩ ⟨y, hy, hyx⟩
    · exact hrβ y (hy.2.trans hsτ.le) (hrx ▸ hyx.symm)
  have hβfresh : ∀ y ∈ Icc s τ, β y ∉ α '' Icc 0 r := by
    rintro y hy ⟨x, hx, hxy⟩
    rcases hy.1.lt_or_eq with hsy | hsy
    · exact Set.disjoint_left.1 hd2 ⟨y, ⟨hsy, hy.2⟩, rfl⟩ ⟨x, hx, hxy⟩
    · exact hsα x (hx.2.trans hra.le) (hsy ▸ hxy)
  have hord : Supp7.IsOrdinaryRetainedPair α ζ₁ r β ζ₂ s :=
    isOrdinaryRetainedPair_of_cuts hF.α0 hF.β0 hF.seed
      (Supp9.HasOrderedProperCompletions.mono (hE s hsτ) hra.le le_rfl)
      (hF.αc.mono fun x hx => hle₁ x hx.2) (hF.βc.mono fun y hy => hle₂ y hy.2)
      (fun x _ hxa => completion_left_of_le (hE 0 hτ0) hxa.le)
      (fun y _ hyτ => completion_right_of_le (hE y hyτ) le_rfl)
      (fun x hx => hF.αim x (hle₁ x hx)) (fun y hy => hF.βim y (hle₂ y hy)) hra le_rfl hsτ le_rfl hp hp
      hrH hsH hαfresh hβfresh hrζ hsζ
  refine hloc r hrD s hsD hord a τ hra ha hsτ hτ hp ?_ ?_ (hwin r s hδr hδs)
  · rintro x hrx hxa (⟨x', hx', hxx'⟩ | hxβ)
    · have := hF.αi (hle₁ x' (hx'.2.trans hra.le)) (hle₁ x hxa) hxx'
      exact absurd (this ▸ hx'.2) (not_le.2 hrx)
    · exact hαfresh x ⟨hrx.le, hxa⟩ hxβ
  · rintro y hsy hyτ (hyα | ⟨y', hy', hyy'⟩)
    · exact hβfresh y ⟨hsy.le, hyτ⟩ hyα
    · have := hF.βi (hle₂ y' (hy'.2.trans hsτ.le)) (hle₂ y hyτ) hyy'
      exact absurd (this ▸ hy'.2) (not_le.2 hsy)

/-- **W5's local frames** (`Supp9.W5LocalFrameStatement`) from Aux. lemma 25, W0a, W0b and the **localized** local
comparison at dyadic retained pairs (`RetainedLocalCompletionLocStatement`). -/
theorem w5LocalFrameStatement_of_loc (h25 : Theorem15.Aux25Statement.{u}) (hW0a : Supp9.W0aStatement.{u})
    (hW0b : Supp9.W0bStatement.{u}) (hL : RetainedLocalCompletionLocStatement.{u}) :
    Supp9.W5LocalFrameStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  have hLall : ∀ᵐ ω ∂P, ∀ p : (ℕ × ℕ) × (ℕ × ℕ),
      Supp7.IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) (dyad p.1.1 p.1.2) (η₂ ω) (ζ₂ ω) (dyad p.2.1 p.2.2) →
      ∀ a τ : ℝ≥0, dyad p.1.1 p.1.2 < a → (a : ℝ≥0∞) < ζ₁ ω → dyad p.2.1 p.2.2 < τ → (τ : ℝ≥0∞) < ζ₂ ω →
        η₁ ω a = η₂ ω τ →
        (∀ x : ℝ≥0, dyad p.1.1 p.1.2 < x → x ≤ a →
          η₁ ω x ∉ η₁ ω '' Icc 0 (dyad p.1.1 p.1.2) ∪ η₂ ω '' Icc 0 (dyad p.2.1 p.2.2)) →
        (∀ y : ℝ≥0, dyad p.2.1 p.2.2 < y → y ≤ τ →
          η₂ ω y ∉ η₁ ω '' Icc 0 (dyad p.1.1 p.1.2) ∪ η₂ ω '' Icc 0 (dyad p.2.1 p.2.2)) →
        IsLocalContact jumps (η₁ ω) (dyad p.1.1 p.1.2) a (η₂ ω) (dyad p.2.1 p.2.2) τ →
        ∃ a₂ b₂ : ℝ≥0, a < a₂ ∧ (a₂ : ℝ≥0∞) < ζ₁ ω ∧ τ < b₂ ∧ (b₂ : ℝ≥0∞) < ζ₂ ω ∧
          HasOrderedProperCompletions (η₁ ω) a₂ (η₂ ω) b₂ :=
    ae_all_iff.2 fun p => hL κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
      (dyad p.1.1 p.1.2) (dyad p.2.1 p.2.2)
  filter_upwards [ae_pathFacts h25 hW0a hκ hκ4 hb hx hθ hh hη₁ hη₂,
    hW0b κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂, hLall] with ω hF hb0 hl
  refine localCompletionAtContact_of_retainedLoc jumps hF hb0 ?_
  rintro u ⟨⟨n, k⟩, rfl⟩ r ⟨⟨n', k'⟩, rfl⟩
  exact hl ((n, k), (n', k'))

/-- **Theorem W5** (`Theorem15.W5Statement`) from Aux. lemma 25, W0a, W0b, Lemma 7.7, the joint G7 carrier, the
**localized** local comparison at dyadic retained pairs and the common-seed local comparison
(`Supp9D.w5Statement_of_inputs''` with `RetainedLocalCompletionLocStatement` in place of the unlocalized form). -/
theorem w5Statement_of_loc (h25 : Theorem15.Aux25Statement.{u}) (hW0a : Supp9.W0aStatement.{u})
    (hW0b : Supp9.W0bStatement.{u}) (h77 : Supp10.Lemma77Statement.{0}) (hJ : JointRetainedPairStatement.{u})
    (hL : RetainedLocalCompletionLocStatement.{u}) (hCS : Supp9.W5CommonSeedStatement.{u}) :
    Theorem15.W5Statement.{u} :=
  w5Statement_of_inputs' h25 hW0a hW0b h77 hJ hCS (w5LocalFrameStatement_of_loc h25 hW0a hW0b hL)

/-- **Theorem W5** from Aux. lemma 25, W0a, W0b, Lemma 7.7, the joint G7 carrier, the common-seed comparison, the
named inputs G2 (with G2b) and G3 of PROVE-RLC-A, Theorems 1.2 (param) and 1.3, PROVE-CONDDET's two-tip input, and the
**localized real-contact case** `RetainedLocalCompletionRealLocStatement`. -/
theorem w5Statement_of_realLoc_param (h25 : Theorem15.Aux25Statement.{u}) (hW0a : Supp9.W0aStatement.{u})
    (hW0b : Supp9.W0bStatement.{u}) (h77 : Supp10.Lemma77Statement.{0}) (hJ : JointRetainedPairStatement.{u})
    (hCS : Supp9.W5CommonSeedStatement.{u}) (hG2 : G2ReferenceStatement.{0})
    (hG3 : G3ChartComparisonStatement.{0}) (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : Restart.RetainedCanonCondDetStatement.{u})
    (hR : RetainedLocalCompletionRealLocStatement.{u}) : Theorem15.W5Statement.{u} :=
  w5Statement_of_loc h25 hW0a hW0b h77 hJ
    (retainedLocalCompletionLocStatement_of_param hG2 hG3 h12p h13 hD hR) hCS

end RLC

end InteractingSLE
