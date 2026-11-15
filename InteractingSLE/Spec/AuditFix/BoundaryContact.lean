/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.AuditFix.BoundaryContactInputs
import InteractingSLE.Frozen.Spec.IsFlowLine_crosses_of_lt

/-!
# Theorem 1.5's contact clauses at every contact, boundary contacts included (audit fix, contact scope)

Packet PROVE-AF-CONTACT (audit priority 1, audit §2.1, p. 5). The sealed frozen Theorem 1.5 clauses
(`IsFlowLine.merges`, `IsFlowLine.crosses_of_lt`, `IsFlowLine.stays_right_of_lt`) fire only on an *interior
available contact* (`IsInteriorAvailableContact`: `s < ζ₁`, `t < ζ₂`, `η₁ s = η₂ t ∈ ℍ`). The paper (Miller–Sheffield,
arXiv:1201.1496v2) states the interaction for every intersection: Theorem 1.5 (p. 30), (ii) "upon intersecting, the two
curves merge and never separate", (iii) "upon intersecting, crosses and then never crosses back"; its proof,
Proposition 7.12 (p. 141), takes the *first* intersection times `τ₁, τ₂`, which may be on `∂ℍ` (Lemma 7.8, p. 137: "The
claim regarding `C_K` is clear if `w₀ ∈ ∂H` by Proposition 6.5"; Figure 7.5, p. 139: "it could be that `w₀ ∈ ∂H`").

## Main results (each a `…Statement : Prop` with its `…_holds` proof)

* `MergesUponContactStatement` (Theorem 1.5 (ii), p. 30; Proposition 7.12, p. 141): for equal angles, at **every**
  contact `η₁ s = η₂ t` of the closed available paths (`s ≤ ζ₁`, `t ≤ ζ₂`) — interior or real, the common starting
  point when `x₁ = x₂`, and terminal contacts — the curves agree as ordered unparametrized curves after it
  (`AgreeAsCurvesAfter`). At a terminal contact (`s = ζ₁` or `t = ζ₂`) the frozen predicate holds with a one-point
  portion: the paper asserts nothing beyond the meeting there ("a terminal meeting supplies no post-meeting subarc").
* `CrossesUponAvailableContactStatement` (Theorem 1.5 (iii), p. 30; Proposition 7.12, p. 141): the frozen crossing
  conclusion (first contact `(s₀, t₀)` attained at one common point, `CrossesFromRightAt` there) for **every**
  available contact (`s < ζ₁`, `t < ζ₂`), real points included. Only the trigger is widened; the first contact may
  itself be real.
* `CrossesUponContactStatement` (terminal contacts as triggers): every contact of the closed available paths forces a
  first contact, and the crossing holds there whenever both continuations at it are nonempty
  (`s₀ < ζ₁`, `t₀ < ζ₂`). When one path ends at its first contact the paper asserts no crossing portion
  (Proposition 7.12 concerns `η_i|[τ_i, T_i]`, a single point when `τ_i = T_i`).
* `CriticalOrderedNoInteriorPointStatement`, `CriticalCrossingNoLaterInteriorPointStatement` (critical angles,
  what is proved): the frozen interior exclusions hold at every contact parameter up to and including the terminal
  ones. The paper's claim at *real* contact points is not proved here (see the hand-off
  `planning/handoffs/PROVE-AF-CONTACT.md`): the project's critical-angle route (7.12D through
  `Theorem15D5.G7GB7aFirstHitStatement`) excludes first hits in `ℍ` only, and Lemma G12 is available for fixed real
  points of one flow line (`Supp7.g12FlowStatement`), not for the random real junctions of the other path under the
  retained conditional law.

The strengthening lemmas `merging15Statement_of_mergesUponContact` and
`crossingFirstClause_of_crossesUponAvailableContact` check that the new statements imply the frozen ones.

## Proof

No new probabilistic input. The closed inputs (`AuditFix.ContactInputs`) are Lemma 7.7's first contact (W8, from any
contact of the closed available paths), Theorem 7.12C at every first contact with two nonempty continuations (the
restart carrier of Lemma 7.8, interior or real), Lemma 7.5 and Aux. lemma 25. The deterministic steps here: a first
contact precedes every contact; at a terminal contact `AgreeAsCurvesAfter` holds with one-point portions
(`agreeAsCurvesAfter_of_coe_eq_left`/`_right`); merging persists along the merged arc (`Sec7`, Corollary 7.12E's last
step); a finite terminal value is real (`Supp10.finiteEndpointRealStatement`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.AuditFix

open ContactInputs

/-! ### Terminal contacts and the persistence of merging -/

/-- **A contact at the end of the first available path**: if `η₁ s = η₂ t` with `s = ζ₁` (finite) and `t ≤ ζ₂`, the
two paths agree as curves after the contact, with the one-point portions `{s}` and `{t}` (`a = ζ₁`, `c = t`). -/
theorem agreeAsCurvesAfter_of_coe_eq_left {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {s t : ℝ≥0}
    (hs : (s : ℝ≥0∞) = ζ₁) (ht : (t : ℝ≥0∞) ≤ ζ₂) (hst : η₁ s = η₂ t) :
    AgreeAsCurvesAfter η₁ ζ₁ s η₂ ζ₂ t := by
  have h1 : ∀ x : {x : ℝ≥0 // s ≤ x ∧ (x : ℝ≥0∞) ≤ ζ₁}, x.1 = s := fun x =>
    le_antisymm (ENNReal.coe_le_coe.1 (x.2.2.trans_eq hs.symm)) x.2.1
  have h2 : ∀ y : {y : ℝ≥0 // t ≤ y ∧ (y : ℝ≥0∞) ≤ (t : ℝ≥0∞)}, y.1 = t := fun y =>
    le_antisymm (ENNReal.coe_le_coe.1 y.2.2) y.2.1
  refine ⟨ζ₁, t, hs.le, le_rfl, le_rfl, ht, Or.inl rfl,
    { toFun := fun _ => ⟨t, le_rfl, le_rfl⟩
      invFun := fun _ => ⟨s, le_rfl, hs.le⟩
      left_inv := fun x => Subtype.ext (h1 x).symm
      right_inv := fun y => Subtype.ext (h2 y).symm
      map_rel_iff' := fun {x y} =>
        ⟨fun _ => le_of_eq (Subtype.ext ((h1 x).trans (h1 y).symm)), fun _ => le_rfl⟩ }, fun x => ?_⟩
  show η₂ t = η₁ x.1
  rw [h1 x]
  exact hst.symm

/-- **A contact at the end of the second available path** (`t = ζ₂`, finite): the reflection of
`agreeAsCurvesAfter_of_coe_eq_left`. -/
theorem agreeAsCurvesAfter_of_coe_eq_right {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {s t : ℝ≥0}
    (hs : (s : ℝ≥0∞) ≤ ζ₁) (ht : (t : ℝ≥0∞) = ζ₂) (hst : η₁ s = η₂ t) :
    AgreeAsCurvesAfter η₁ ζ₁ s η₂ ζ₂ t :=
  Sec7.AgreeAsCurvesAfter.symm (agreeAsCurvesAfter_of_coe_eq_left ht hs hst.symm)

/-- **Merging at every contact of the closed available paths, from merging at the first contact.** For injective
available paths with first contact `(s₀, t₀)`, if they merge there whenever both continuations are nonempty, then they
merge at every contact `(s, t)`, `s ≤ ζ₁`, `t ≤ ζ₂`: on the branch with two nonempty continuations the contact lies on
the merged arc (`Sec7.agreeAsCurvesAfter_of_isFirstContact`); otherwise one path ends at `(s₀, t₀) ≤ (s, t)`, so the
contact is terminal for it. -/
theorem agreeAsCurvesAfter_of_firstContact {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {s₀ t₀ s t : ℝ≥0}
    (hi₁ : InjOn η₁ {s | (s : ℝ≥0∞) ≤ ζ₁}) (hi₂ : InjOn η₂ {t | (t : ℝ≥0∞) ≤ ζ₂})
    (h₀ : IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀)
    (hm : (s₀ : ℝ≥0∞) < ζ₁ → (t₀ : ℝ≥0∞) < ζ₂ → AgreeAsCurvesAfter η₁ ζ₁ s₀ η₂ ζ₂ t₀)
    (hs : (s : ℝ≥0∞) ≤ ζ₁) (ht : (t : ℝ≥0∞) ≤ ζ₂) (hst : η₁ s = η₂ t) :
    AgreeAsCurvesAfter η₁ ζ₁ s η₂ ζ₂ t := by
  have hle := h₀.2.2.2 s t hs ht hst
  by_cases hs₀ : (s₀ : ℝ≥0∞) < ζ₁
  · by_cases ht₀ : (t₀ : ℝ≥0∞) < ζ₂
    · exact Sec7.agreeAsCurvesAfter_of_isFirstContact hi₁ hi₂ h₀ (hm hs₀ ht₀)
        ⟨zero_le, hs, zero_le, ht, hst⟩
    · exact agreeAsCurvesAfter_of_coe_eq_right hs
        (le_antisymm ht ((not_lt.1 ht₀).trans (ENNReal.coe_le_coe.2 hle.2))) hst
  · exact agreeAsCurvesAfter_of_coe_eq_left
      (le_antisymm hs ((not_lt.1 hs₀).trans (ENNReal.coe_le_coe.2 hle.1))) ht hst

/-! ### Theorem 1.5 (ii): merging upon every contact -/

/-- **Theorem 1.5 (ii) at every contact** (paper p. 30: "If `θ₁ = θ₂`, then `η^{x₁}_{θ₁}` may intersect `η^{x₂}_{θ₂}`
and, upon intersecting, the two curves merge and never separate"; Proposition 7.12, p. 141, at the first intersection,
which may lie on `∂ℍ`). For `x₂ ≤ x₁` and a common angle `θ`: almost surely, at every contact `η₁ s = η₂ t` of the
closed available paths (`s ≤ ζ₁`, `t ≤ ζ₂`; the contact point interior or real) the two flow lines agree as ordered
unparametrized curves after it until the shorter available portion ends. The frozen `IsFlowLine.merges` is the
restriction to `s < ζ₁`, `t < ζ₂`, `η₁ s ∈ ℍ`. -/
def MergesUponContactStatement : Prop :=
  ∀ {κ : ℝ} (_hκ : 0 < κ) (_hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (_hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ : ℝ} (_hx : x₂ ≤ x₁)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (_hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (_hη₁ : IsFlowLine κ b jumps x₁ θ P h η₁ ζ₁) (_hη₂ : IsFlowLine κ b jumps x₂ θ P h η₂ ζ₂),
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → (t : ℝ≥0∞) ≤ ζ₂ ω → η₁ ω s = η₂ ω t →
      AgreeAsCurvesAfter (η₁ ω) (ζ₁ ω) s (η₂ ω) (ζ₂ ω) t

/-- **Theorem 1.5 (ii) at every contact, proved.** `x₂ < x₁`: W8 (Lemma 7.7) gives the first contact `(s₀, t₀)` of
the closed available paths; Theorem 7.12C (equal angles, the restart carrier at a first contact with two nonempty
continuations, interior or real) merges the paths there; `agreeAsCurvesAfter_of_firstContact` carries the merging to
`(s, t)`. `x₂ = x₁`: Lemma 7.5 makes the two flow lines one available path, and Aux. lemma 25 gives `s = t`. -/
theorem mergesUponContact_holds : MergesUponContactStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ hx Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  have hi₁ := Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁
  have hi₂ := Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂
  rcases hx.lt_or_eq with hlt | heq
  · filter_upwards [hi₁, hi₂,
      w8FirstContact κ hκ hκ4 b jumps hb x₁ x₂ θ θ hlt (lt_add_of_pos_right θ Real.pi_pos) P h hh
        η₁ η₂ ζ₁ ζ₂ hη₁ hη₂,
      thm712CMerging κ hκ hκ4 b jumps hb x₁ x₂ θ hlt P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂]
      with ω hi₁ω hi₂ω hfω hmω
    intro s t hs ht hst
    obtain ⟨s₀, t₀, h₀⟩ := hfω ⟨s, t, hs, ht, hst⟩
    exact agreeAsCurvesAfter_of_firstContact hi₁ω hi₂ω h₀ (hmω s₀ t₀ h₀) hs ht hst
  · have hη₁' : IsFlowLine κ b jumps x₂ θ P h η₁ ζ₁ := heq ▸ hη₁
    obtain ⟨Φ, -, hΦ⟩ := lemma75.{u} κ hκ hκ4 b jumps hb x₂ θ
    filter_upwards [hi₁, hΦ P h hh η₁ ζ₁ hη₁', hΦ P h hh η₂ ζ₂ hη₂] with ω hi₁ω h₁ω h₂ω
    intro s t hs ht hst
    have hζ : ζ₂ ω = ζ₁ ω := h₂ω.1.symm.trans h₁ω.1
    have heqOn : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ ζ₁ ω → η₂ ω r = η₁ ω r := fun r hr =>
      (h₂ω.2 r (by rw [hζ]; exact hr)).symm.trans (h₁ω.2 r hr)
    have ht' : (t : ℝ≥0∞) ≤ ζ₁ ω := by rw [← hζ]; exact ht
    have hts : t = s := hi₁ω ht' hs ((heqOn t ht').symm.trans hst.symm)
    subst hts
    rw [hζ]
    exact Theorem15.agreeAsCurvesAfter_self_of_eqOn heqOn ht'

/-- The new merging statement implies the frozen `IsFlowLine.merges` (an interior available contact is a contact of
the closed available paths). -/
theorem merging15Statement_of_mergesUponContact (hM : MergesUponContactStatement.{u}) :
    Wire.Merging15Statement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ hx Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  filter_upwards [hM hκ hκ4 b jumps hb hx hh hη₁ hη₂] with ω hω s t hst
  exact hω s t hst.1.le hst.2.1.le hst.2.2.1

/-! ### Theorem 1.5 (iii): crossing upon every available contact -/

/-- **Theorem 1.5 (iii), crossing, at every available contact** (paper p. 30: "if `θ₂ + π > θ₁ > θ₂`, then
`η^{x₁}_{θ₁}` may intersect `η^{x₂}_{θ₂}` and, upon intersecting, crosses and then never crosses back"; Proposition 7.12,
p. 141: "`η^{x₁}_{θ₁}|[0,T₁]` almost surely crosses `η^{x₂}_{θ₂}|[0,T₂]` upon intersecting", with `τᵢ` the first
intersection times, possibly on `∂ℍ`). For `x₂ < x₁` and `θ₂ < θ₁ < θ₂ + π`: almost surely, if the flow lines have an
available contact `η₁ s = η₂ t` (`s < ζ₁`, `t < ζ₂`, the point interior or real), then their first contact `(s₀, t₀)` is
attained at one common point and there the first curve crosses the second from right to left and never crosses back
(`CrossesFromRightAt`). This is the frozen first clause of `IsFlowLine.crosses_of_lt` with the trigger
`IsInteriorAvailableContact` replaced by an available contact; the conclusion is unchanged. -/
def CrossesUponAvailableContactStatement : Prop :=
  ∀ {κ : ℝ} (_hκ : 0 < κ) (_hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (_hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (_hx : x₂ < x₁) (_hθ : θ₂ < θ₁) (_hθπ : θ₁ < θ₂ + Real.pi)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (_hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (_hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (_hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂),
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, (s : ℝ≥0∞) < ζ₁ ω → (t : ℝ≥0∞) < ζ₂ ω → η₁ ω s = η₂ ω t →
      ∃ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ ∧
        CrossesFromRightAt (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀

/-- **Theorem 1.5 (iii), crossing, with terminal contacts as triggers** (paper p. 30 and Proposition 7.12, p. 141;
Proposition 7.12 asserts the crossing for `η_i|[τ_i, T_i]`, a single point when a path stops at the first
intersection). For `x₂ < x₁` and `θ₂ < θ₁ < θ₂ + π`: almost surely, every contact `η₁ s = η₂ t` of the closed
available paths (`s ≤ ζ₁`, `t ≤ ζ₂`, interior or real, terminal values included) forces a first contact `(s₀, t₀)`
attained at one common point, and the first curve crosses the second there (`CrossesFromRightAt`) whenever both
continuations at it are nonempty (`s₀ < ζ₁`, `t₀ < ζ₂`). -/
def CrossesUponContactStatement : Prop :=
  ∀ {κ : ℝ} (_hκ : 0 < κ) (_hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (_hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (_hx : x₂ < x₁) (_hθ : θ₂ < θ₁) (_hθπ : θ₁ < θ₂ + Real.pi)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (_hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (_hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (_hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂),
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → (t : ℝ≥0∞) ≤ ζ₂ ω → η₁ ω s = η₂ ω t →
      ∃ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ ∧
        ((s₀ : ℝ≥0∞) < ζ₁ ω → (t₀ : ℝ≥0∞) < ζ₂ ω →
          CrossesFromRightAt (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀)

/-- **Crossing with terminal triggers, proved**: W8 (Lemma 7.7) gives the first contact from any contact of the closed
available paths, and Theorem 7.12C (strict angles: the restart carrier and W5 in the first-contact chart, at every
first contact with two nonempty continuations, interior or real) gives the crossing there. -/
theorem crossesUponContact_holds : CrossesUponContactStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ hθπ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  filter_upwards [w8FirstContact κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθπ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂,
    thm712CCrossing κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ hθπ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂]
    with ω hfω hcω
  intro s t hs ht hst
  obtain ⟨s₀, t₀, h₀⟩ := hfω ⟨s, t, hs, ht, hst⟩
  exact ⟨s₀, t₀, h₀, hcω s₀ t₀ h₀⟩

/-- **Crossing upon every available contact, proved**: the first contact precedes the available contact
(`IsFirstContact`), so both of its continuations are nonempty. -/
theorem crossesUponAvailableContact_holds : CrossesUponAvailableContactStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ hθπ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  filter_upwards [crossesUponContact_holds hκ hκ4 b jumps hb hx hθ hθπ hh hη₁ hη₂] with ω hω
  intro s t hs ht hst
  obtain ⟨s₀, t₀, h₀, hc⟩ := hω s t hs.le ht.le hst
  have hle := h₀.2.2.2 s t hs.le ht.le hst
  exact ⟨s₀, t₀, h₀, hc ((ENNReal.coe_le_coe.2 hle.1).trans_lt hs)
    ((ENNReal.coe_le_coe.2 hle.2).trans_lt ht)⟩

/-- The new crossing statement implies the first clause of the frozen `IsFlowLine.crosses_of_lt` (an interior
available contact is an available contact). -/
theorem crossingFirstClause_of_crossesUponAvailableContact (hC : CrossesUponAvailableContactStatement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₂ < θ₁) (hθπ : θ₁ < θ₂ + Real.pi)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t →
      ∃ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ ∧
        CrossesFromRightAt (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀ := by
  filter_upwards [hC hκ hκ4 b jumps hb hx hθ hθπ hh hη₁ hη₂] with ω hω s t hst
  exact hω s t hst.1 hst.2.1 hst.2.2.1

/-! ### Critical angles: what is proved -/

/-- **Theorem 1.5 (i), critical angles, at every contact parameter: no common point in `ℍ`** (paper p. 30: "otherwise
the paths almost surely do not intersect (except possibly at their starting point)"). For `x₂ ≤ x₁`, `θ₁ < θ₂` and
`θ₂ − θ₁ ≥ πκ/(4 − κ)`: almost surely every contact `η₁ s = η₂ t` of the closed available paths (`s ≤ ζ₁`, `t ≤ ζ₂`,
terminal values included) is a real point. This is the proved scope; the paper's exclusion of real contact points
(other than a starting point) is not proved here. -/
def CriticalOrderedNoInteriorPointStatement : Prop :=
  ∀ {κ : ℝ} (_hκ : 0 < κ) (_hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (_hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (_hx : x₂ ≤ x₁) (_hθ : θ₁ < θ₂)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (_hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (_hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (_hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (_hcrit : Real.pi * κ / (4 - κ) ≤ θ₂ - θ₁),
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → (t : ℝ≥0∞) ≤ ζ₂ ω → η₁ ω s = η₂ ω t →
      η₁ ω s ∉ QuantumZipper.H

/-- **No common point in `ℍ` at critical angles, proved**: a finite terminal value is real
(`Supp10.finiteEndpointRealStatement`), so a contact in `ℍ` is available for both paths, and the sealed frozen
`IsFlowLine.stays_right_of_lt` excludes it. -/
theorem criticalOrderedNoInteriorPoint_holds : CriticalOrderedNoInteriorPointStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ hcrit
  filter_upwards [(IsFlowLine.stays_right_of_lt hκ hκ4 b jumps hb hx hθ hh hη₁ hη₂).2 hcrit,
    Supp10.finiteEndpointRealStatement κ hκ hκ4 b jumps hb x₁ θ₁ P h hh η₁ ζ₁ hη₁,
    Supp10.finiteEndpointRealStatement κ hκ hκ4 b jumps hb x₂ θ₂ P h hh η₂ ζ₂ hη₂]
    with ω hω hE₁ hE₂
  intro s t hs ht hst hH
  have hH₂ : η₂ ω t ∈ QuantumZipper.H := hst ▸ hH
  exact hω s t ⟨lt_of_le_of_ne hs fun he => hE₁ s he hH, lt_of_le_of_ne ht fun he => hE₂ t he hH₂, hst, hH⟩

/-- **Theorem 1.5 (iii), critical angles, at every contact parameter: no later common point in `ℍ`** (paper p. 30:
"otherwise the paths almost surely do not subsequently intersect"). For `x₂ < x₁`, `θ₂ < θ₁ < θ₂ + π` and
`θ₁ − θ₂ ≥ πκ/(4 − κ)`: almost surely every contact `η₁ s = η₂ t` in `ℍ` of the closed available paths (`s ≤ ζ₁`,
`t ≤ ζ₂`) is the first contact. In particular, when the first contact is a real point there is no contact in `ℍ` at
all. The paper's exclusion of later *real* contact points is not proved here. -/
def CriticalCrossingNoLaterInteriorPointStatement : Prop :=
  ∀ {κ : ℝ} (_hκ : 0 < κ) (_hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (_hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (_hx : x₂ < x₁) (_hθ : θ₂ < θ₁) (_hθπ : θ₁ < θ₂ + Real.pi)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (_hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (_hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (_hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (_hcrit : Real.pi * κ / (4 - κ) ≤ θ₁ - θ₂),
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → (t : ℝ≥0∞) ≤ ζ₂ ω → η₁ ω s = η₂ ω t →
      η₁ ω s ∈ QuantumZipper.H → IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t

/-- **No later common point in `ℍ` at critical angles, proved**: a finite terminal value is real, so a contact in `ℍ`
is available for both paths, and the sealed frozen `IsFlowLine.crosses_of_lt` makes it the first contact. -/
theorem criticalCrossingNoLaterInteriorPoint_holds : CriticalCrossingNoLaterInteriorPointStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ hθπ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ hcrit
  filter_upwards [(IsFlowLine.crosses_of_lt hκ hκ4 b jumps hb hx hθ hθπ hh hη₁ hη₂).2 hcrit,
    Supp10.finiteEndpointRealStatement κ hκ hκ4 b jumps hb x₁ θ₁ P h hh η₁ ζ₁ hη₁,
    Supp10.finiteEndpointRealStatement κ hκ hκ4 b jumps hb x₂ θ₂ P h hh η₂ ζ₂ hη₂]
    with ω hω hE₁ hE₂
  intro s t hs ht hst hH
  have hH₂ : η₂ ω t ∈ QuantumZipper.H := hst ▸ hH
  exact hω s t ⟨lt_of_le_of_ne hs fun he => hE₁ s he hH, lt_of_le_of_ne ht fun he => hE₂ t he hH₂, hst, hH⟩

end InteractingSLE.AuditFix
