/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.AuditFix.StrongCrossArc
import InteractingSLE.Spec.Theorem15D5Crossing
import InteractingSLE.Spec.Supplement.S10B712D
import InteractingSLE.Spec.Supplement.S9Propagation
import InteractingSLE.Spec.Restart.Carrier

/-!
# Audit fix (crossing): no common open outgoing arc at the first contact

Packet PROVE-AF-CROSS (external audit of 2026-11-15, §2.2, pp. 6–7). Specification p. 542, proof of Theorem 7.12C:
"W0b, applied in this conditional chart, excludes a common actual open outgoing arc with unequal angles." This file
carries that sentence out on the route of the frozen crossing clause (`Theorem15D5.chartOrderAfterCrossingStatement_of_restartLim`):

* **W0b at each datum** under the restart kernel. The conditional continuations `γ₂` (angle `θ₂`) and `γ₁` (angle
  `θ₁ > θ₂`) are flow lines from the common seed `0` of one GFF with the chart datum, so W5 orders all their strict
  prefixes (lower angle first) and W0b, applied to these ordered prefixes, excludes an open subarc of `γ₂` in a prefix
  of `γ₁`. The other orientation follows because ordered prefixes are continuous and injective
  (`Supp10.exists_firstArc_of_secondArc`). Conclusion: `NoArcStrict` (`noArcStrict_of_ordered`).
* **Integrating back.** On the dyadic prefixes, the no-common-arc event is measurable (`NoArcEvent`,
  `measurableSet_noArcEvent`, by the countable description `Cross.DyadCommonArc`), and it has full `K c`-measure for
  almost every datum, so it holds for the restart variable almost surely (`Restart.ae_mem_of_compProd_eq`).
* **Through the chart and the clocks** (`hasCommonOpenSubarc_chart_of_physical`). The chart images are the limits of
  the active chart `φ` along the active domain `D` at the physical points (`IsChartContinuationLim`), and the physical
  outgoing points lie in `closure D` (Lemma 7.7's confinement). Equal physical points therefore have equal chart
  images, and the increasing capacity clocks map open parameter intervals onto open intervals. So a common open
  subarc of the physical outgoing prefixes gives one of the chart prefixes, which the integrated event excludes.

Main result: `noCommonOutgoingArcStatement_of_inputs`, the conditional helper `NoCommonOutgoingArcStatement` from
Lemma 7.7, the restart carrier with the active prime end, W5 and W0b on the canonical space. It holds at **every**
first contact with two nonempty continuations, interior or real.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace AuditFix

namespace Cross

open Sec2.Assembly Supp9 Theorem15D5 Restart

/-! ### The no-common-arc event on the canonical space -/

/-- No common open subarc between strict prefixes of `γ₂` (on `[0, U₂)`) and `γ₁` (on `[0, U₁)`), in both
orientations (the lower-angle path `γ₂` first, as in W0b). -/
def NoArcStrict (γ₁ γ₂ : ℝ≥0 → ℂ) (U₁ U₂ : ℝ≥0∞) : Prop :=
  ∀ a c : ℝ≥0, (a : ℝ≥0∞) < U₂ → (c : ℝ≥0∞) < U₁ →
    ¬ HasCommonOpenSubarc γ₂ a γ₁ c ∧ ¬ HasCommonOpenSubarc γ₁ c γ₂ a

/-- The no-common-arc event of the restart coordinates, at the dyadic strict prefixes and through the countable
description `DyadCommonArc`. -/
def NoArcEvent {S : Type*} (γ₁ γ₂ : S → ℝ≥0 → ℂ) (U₁ U₂ : S → ℝ≥0∞) : Set S :=
  {s | ∀ n k n' k' : ℕ, (dyad n k : ℝ≥0∞) < U₂ s → (dyad n' k' : ℝ≥0∞) < U₁ s →
    ¬ DyadCommonArc (γ₂ s) (γ₁ s) (dyad n k) (dyad n' k') ∧
      ¬ DyadCommonArc (γ₁ s) (γ₂ s) (dyad n' k') (dyad n k)}

/-- The dyadic description of a common subarc is a measurable property of measurable coordinates. -/
theorem measurable_dyadCommonArc {S : Type*} [MeasurableSpace S] {f g : S → ℝ≥0 → ℂ}
    (hf : ∀ t, Measurable fun s => f s t) (hg : ∀ t, Measurable fun s => g s t) (a c : ℝ≥0) :
    Measurable fun s => DyadCommonArc (f s) (g s) a c := by
  unfold DyadCommonArc
  refine Measurable.exists fun i => Measurable.exists fun j => Measurable.exists fun i' =>
    Measurable.exists fun j' => Measurable.and measurable_const (Measurable.and measurable_const ?_)
  refine Measurable.forall fun p => Measurable.forall fun q => Measurable.imp measurable_const
    (Measurable.imp measurable_const (Measurable.forall fun m => Measurable.exists fun p' =>
      Measurable.exists fun q' => Measurable.and measurable_const ?_))
  exact measurableSet_setOfPred.1 (measurableSet_lt ((hf _).dist (hg _)) measurable_const)

/-- **The no-common-arc event is measurable.** -/
theorem measurableSet_noArcEvent {S : Type*} [MeasurableSpace S] {γ₁ γ₂ : S → ℝ≥0 → ℂ}
    {U₁ U₂ : S → ℝ≥0∞} (hU₁ : Measurable U₁) (hU₂ : Measurable U₂)
    (hγ₁ : ∀ t, Measurable fun s => γ₁ s t) (hγ₂ : ∀ t, Measurable fun s => γ₂ s t) :
    MeasurableSet (NoArcEvent γ₁ γ₂ U₁ U₂) := by
  unfold NoArcEvent
  refine measurableSet_setOfPred.2 (Measurable.forall fun n => Measurable.forall fun k =>
    Measurable.forall fun n' => Measurable.forall fun k' => Measurable.imp ?_ (Measurable.imp ?_
      (Measurable.and (measurable_dyadCommonArc hγ₂ hγ₁ _ _).not
        (measurable_dyadCommonArc hγ₁ hγ₂ _ _).not)))
  · exact measurableSet_setOfPred.1 (measurableSet_lt measurable_const hU₂)
  · exact measurableSet_setOfPred.1 (measurableSet_lt measurable_const hU₁)

/-- Paths continuous on their available intervals, without common open subarcs of strict prefixes, lie in the
no-common-arc event. -/
theorem mem_noArcEvent_of_noArcStrict {S : Type*} {γ₁ γ₂ : S → ℝ≥0 → ℂ} {U₁ U₂ : S → ℝ≥0∞} {s : S}
    (hc₁ : ContinuousOn (γ₁ s) {u | (u : ℝ≥0∞) ≤ U₁ s})
    (hc₂ : ContinuousOn (γ₂ s) {u | (u : ℝ≥0∞) ≤ U₂ s})
    (h : NoArcStrict (γ₁ s) (γ₂ s) (U₁ s) (U₂ s)) : s ∈ NoArcEvent γ₁ γ₂ U₁ U₂ := by
  intro n k n' k' hd hd'
  have hcon₂ : ContinuousOn (γ₂ s) (Icc 0 (dyad n k)) :=
    hc₂.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans hd.le
  have hcon₁ : ContinuousOn (γ₁ s) (Icc 0 (dyad n' k')) :=
    hc₁.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans hd'.le
  exact ⟨fun hD => (h _ _ hd hd').1 ((hasCommonOpenSubarc_iff_dyadCommonArc hcon₂ hcon₁).2 hD),
    fun hD => (h _ _ hd hd').2 ((hasCommonOpenSubarc_iff_dyadCommonArc hcon₁ hcon₂).2 hD)⟩

/-- On the no-common-arc event, no strict prefixes (dyadic or not) have a common open subarc. -/
theorem noArcStrict_of_mem_noArcEvent {S : Type*} {γ₁ γ₂ : S → ℝ≥0 → ℂ} {U₁ U₂ : S → ℝ≥0∞} {s : S}
    (hc₁ : ContinuousOn (γ₁ s) {u | (u : ℝ≥0∞) ≤ U₁ s})
    (hc₂ : ContinuousOn (γ₂ s) {u | (u : ℝ≥0∞) ≤ U₂ s})
    (hs : s ∈ NoArcEvent γ₁ γ₂ U₁ U₂) : NoArcStrict (γ₁ s) (γ₂ s) (U₁ s) (U₂ s) := by
  intro a c ha hc
  obtain ⟨n, k, hak, hd⟩ := exists_dyad_btwn ha
  obtain ⟨n', k', hck, hd'⟩ := exists_dyad_btwn hc
  have hcon₂ : ContinuousOn (γ₂ s) (Icc 0 (dyad n k)) :=
    hc₂.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans hd.le
  have hcon₁ : ContinuousOn (γ₁ s) (Icc 0 (dyad n' k')) :=
    hc₁.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans hd'.le
  obtain ⟨h1, h2⟩ := hs n k n' k' hd hd'
  exact ⟨fun hH => h1 ((hasCommonOpenSubarc_iff_dyadCommonArc hcon₂ hcon₁).1
      (hasCommonOpenSubarc_mono hH hak.le hck.le)),
    fun hH => h2 ((hasCommonOpenSubarc_iff_dyadCommonArc hcon₁ hcon₂).1
      (hasCommonOpenSubarc_mono hH hck.le hak.le))⟩

/-- **W0b on ordered prefixes, both orientations.** If every pair of strict prefixes has ordered proper completions
(W5, lower-angle path `γ₂` first) and W0b excludes a common open subarc of each such ordered pair, then no strict
prefixes have a common open subarc in either orientation: ordered prefixes are continuous and injective, so an open
subarc of `γ₁` in `γ₂([0, a])` gives one of `γ₂` in `γ₁([0, c])` (`Supp10.exists_firstArc_of_secondArc`). -/
theorem noArcStrict_of_ordered {γ₁ γ₂ : ℝ≥0 → ℂ} {U₁ U₂ : ℝ≥0∞}
    (hord : ∀ a c : ℝ≥0, (a : ℝ≥0∞) < U₂ → (c : ℝ≥0∞) < U₁ → HasOrderedProperCompletions γ₂ a γ₁ c)
    (hW0b : ∀ a c : ℝ≥0, (a : ℝ≥0∞) < U₂ → (c : ℝ≥0∞) < U₁ → HasOrderedProperCompletions γ₂ a γ₁ c →
      ¬ HasCommonOpenSubarc γ₂ a γ₁ c) : NoArcStrict γ₁ γ₂ U₁ U₂ := by
  intro a c ha hc
  have ho := hord a c ha hc
  have h1 := hW0b a c ha hc ho
  refine ⟨h1, ?_⟩
  rintro ⟨y₁, y₂, hy, hy₂, hsub⟩
  exact h1 (Supp10.exists_firstArc_of_secondArc (Supp9.HasOrderedProperCompletions.continuousOn_left ho)
    (Supp9.HasOrderedProperCompletions.injOn_left ho) (Supp9.HasOrderedProperCompletions.continuousOn_right ho)
    (Supp9.HasOrderedProperCompletions.injOn_right ho) hy hy₂ hsub)

/-! ### Through the chart and the capacity clocks -/

/-- **A common open arc of the physical outgoing prefixes is a common open arc of the chart prefixes.** The paths
`α`, `β` continue from `a₀`, `b₀` with available lifetimes `A`, `B`; their chart paths `Γα`, `Γβ` are read through
strictly increasing capacity clocks `cα`, `cβ` mapping `[0, Uα]`, `[0, Uβ]` onto `[a₀, A]`, `[b₀, B]`, as limits of
the chart `φ` along `D` at the physical points; the outgoing points of `α` lie in `closure D`. If an open arc
`α((a₀ + x₁, a₀ + x₂))`, `x₂ ≤ u`, lies in `β([b₀, b₀ + v])`, then the open chart arc `Γα((g x₁, g x₂))` lies in
`Γβ([0, g' v])` (`g`, `g'` the inverse clocks): an equal physical point has equal limits of `φ` along `D`. -/
theorem hasCommonOpenSubarc_chart_of_physical {α β : ℝ≥0 → ℂ} {A B : ℝ≥0∞} {a₀ b₀ : ℝ≥0} {D : Set ℂ}
    {φ : ℂ → ℂ} {Γα Γβ : ℝ≥0 → ℂ} {Uα Uβ : ℝ≥0∞} {cα cβ : ℝ≥0 → ℝ≥0}
    (hmα : StrictMonoOn cα {u | (u : ℝ≥0∞) ≤ Uα})
    (himα : cα '' {u | (u : ℝ≥0∞) ≤ Uα} = {s | a₀ ≤ s ∧ (s : ℝ≥0∞) ≤ A})
    (hmβ : StrictMonoOn cβ {u | (u : ℝ≥0∞) ≤ Uβ})
    (himβ : cβ '' {u | (u : ℝ≥0∞) ≤ Uβ} = {s | b₀ ≤ s ∧ (s : ℝ≥0∞) ≤ B})
    (hlα : ∀ u : ℝ≥0, (u : ℝ≥0∞) < Uα → Tendsto φ (𝓝[D] (α (cα u))) (𝓝 (Γα u)))
    (hlβ : ∀ u : ℝ≥0, (u : ℝ≥0∞) < Uβ → Tendsto φ (𝓝[D] (β (cβ u))) (𝓝 (Γβ u)))
    (hclα : ∀ s : ℝ≥0, a₀ ≤ s → (s : ℝ≥0∞) ≤ A → α s ∈ closure D)
    {u v : ℝ≥0} (hu : ((a₀ + u : ℝ≥0) : ℝ≥0∞) < A) (hv : ((b₀ + v : ℝ≥0) : ℝ≥0∞) < B)
    (h : HasCommonOpenSubarc (fun r => α (a₀ + r)) u (fun r => β (b₀ + r)) v) :
    HasCommonOpenSubarc Γα (invClock cα Uα a₀ u) Γβ (invClock cβ Uβ b₀ v) := by
  obtain ⟨x₁, x₂, h12, h2u, hsub⟩ := h
  have hmonoα : ∀ t t' : ℝ≥0, t ≤ t' → ((a₀ + t' : ℝ≥0) : ℝ≥0∞) ≤ A →
      invClock cα Uα a₀ t ≤ invClock cα Uα a₀ t' := fun t t' htt' ht' =>
    htt'.lt_or_eq.elim (fun hlt => (invClock_lt_invClock hmα himα ht' hlt).le)
      fun heq => (congrArg (invClock cα Uα a₀) heq).le
  have hmonoβ : ∀ t t' : ℝ≥0, t ≤ t' → ((b₀ + t' : ℝ≥0) : ℝ≥0∞) ≤ B →
      invClock cβ Uβ b₀ t ≤ invClock cβ Uβ b₀ t' := fun t t' htt' ht' =>
    htt'.lt_or_eq.elim (fun hlt => (invClock_lt_invClock hmβ himβ ht' hlt).le)
      fun heq => (congrArg (invClock cβ Uβ b₀) heq).le
  have hle : ∀ t : ℝ≥0, t ≤ u → ((a₀ + t : ℝ≥0) : ℝ≥0∞) ≤ A := fun t ht =>
    (ENNReal.coe_le_coe.2 (add_le_add le_rfl ht)).trans hu.le
  refine ⟨invClock cα Uα a₀ x₁, invClock cα Uα a₀ x₂,
    invClock_lt_invClock hmα himα (hle x₂ h2u) h12, hmonoα x₂ u h2u hu.le, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨t, htx₂, rfl⟩ := invClock_surj hmα himα (hle x₂ h2u) hw.2.le
  have ht₁ : x₁ < t := by
    by_contra hle'
    exact absurd hw.1 (not_lt.2 (hmonoα t x₁ (not_lt.1 hle') (hle x₁ (h12.le.trans h2u))))
  have ht₂ : t < x₂ := by
    refine lt_of_le_of_ne htx₂ fun heq => ?_
    rw [heq] at hw
    exact lt_irrefl _ hw.2
  obtain ⟨y, hy, hyt⟩ := hsub (mem_image_of_mem (fun r => α (a₀ + r)) ⟨ht₁, ht₂⟩)
  have hyt' : β (b₀ + y) = α (a₀ + t) := hyt
  have htA : ((a₀ + t : ℝ≥0) : ℝ≥0∞) < A :=
    (ENNReal.coe_le_coe.2 (add_le_add le_rfl (htx₂.trans h2u))).trans_lt hu
  have hyB : ((b₀ + y : ℝ≥0) : ℝ≥0∞) < B :=
    (ENNReal.coe_le_coe.2 (add_le_add le_rfl hy.2)).trans_lt hv
  have h1 := hlα _ (invClock_lt himα hmα htA)
  have h2 := hlβ _ (invClock_lt himβ hmβ hyB)
  rw [(invClock_spec himα htA.le).2] at h1
  rw [(invClock_spec himβ hyB.le).2, hyt'] at h2
  have := mem_closure_iff_nhdsWithin_neBot.1 (hclα (a₀ + t) le_self_add htA.le)
  exact ⟨invClock cβ Uβ b₀ y, ⟨zero_le, hmonoβ y v hy.2 hv.le⟩, tendsto_nhds_unique h2 h1⟩

/-! ### No common open outgoing arc at the first contact -/

/-- **No common open outgoing subarc at the first contact** (the conditional helper's conclusion; Theorem 7.12C,
specification p. 542: "They have no common nontrivial open outgoing arc"). In the setting of the frozen Theorem 1.5
(iii) (`x₂ < x₁`, `θ₂ < θ₁ < θ₂ + π`): almost surely, at every first contact `(s₀, t₀)` with two nonempty continuations,
for every pair of strict finite outgoing prefixes `η₁([s₀, s₀ + u])`, `η₂([t₀, t₀ + v])`, neither contains an open
subarc of the other. -/
def NoCommonOutgoingArcStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₂ < θ₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ∀ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ →
        (s₀ : ℝ≥0∞) < ζ₁ ω → (t₀ : ℝ≥0∞) < ζ₂ ω →
        ∀ u v : ℝ≥0, ((s₀ + u : ℝ≥0) : ℝ≥0∞) < ζ₁ ω → ((t₀ + v : ℝ≥0) : ℝ≥0∞) < ζ₂ ω →
          ¬ HasCommonOpenSubarc (fun r => η₁ ω (s₀ + r)) u (fun r => η₂ ω (t₀ + r)) v ∧
            ¬ HasCommonOpenSubarc (fun r => η₂ ω (t₀ + r)) v (fun r => η₁ ω (s₀ + r)) u

/-- **W0b in the first-contact chart** (specification p. 542; a conditional helper): `NoCommonOutgoingArcStatement`
from Lemma 7.7 (confinement of the outgoing paths to the closed active domain), the restart carrier with the active
prime end, and W5 and W0b on the canonical space (universe `0`). -/
theorem noCommonOutgoingArcStatement_of_inputs (h77 : Supp10.Lemma77Statement.{u})
    (hR : FirstContactRestartLimStatement.{u}) (hW5₀ : Theorem15.W5Statement.{0})
    (hW0b₀ : W0bStatement.{0}) : NoCommonOutgoingArcStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ hθπ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  obtain ⟨S, mS, H, γ₁, γ₂, U₁, U₂, M, β, X, K, hco, hM, hβ, hX, hK, hlaw, hpair, hpath⟩ :=
    hR κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθπ P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  obtain ⟨-, hU₁, hU₂, hγ₁, hγ₂, hc₁, hc₂⟩ := hco
  -- W5 and W0b at each datum, for the common-seed conditional pair (lower angle `θ₂` first)
  have hKE : ∀ᵐ c ∂(P.restrict M).map β, ∀ᵐ s ∂(K c), s ∈ NoArcEvent γ₁ γ₂ U₁ U₂ := by
    filter_upwards [hpair] with c hc
    obtain ⟨hgff, hf₁, hf₂⟩ := hc
    filter_upwards [hW5₀ κ hκ hκ4 c.fn c.jumps c.isPiecewiseConstantBoundaryData 0 0 θ₂ θ₁ le_rfl hθ
        (K c) H hgff γ₂ γ₁ U₂ U₁ hf₂ hf₁,
      hW0b₀ κ hκ hκ4 c.fn c.jumps c.isPiecewiseConstantBoundaryData 0 0 θ₂ θ₁ le_rfl hθ
        (K c) H hgff γ₂ γ₁ U₂ U₁ hf₂ hf₁] with s hs5 hs0
    exact mem_noArcEvent_of_noArcStrict (hc₁ s) (hc₂ s) (noArcStrict_of_ordered hs5 hs0)
  -- the measurable event integrates back
  have hae := ae_mem_of_compProd_eq hM hβ hX hlaw (measurableSet_noArcEvent hU₁ hU₂ hγ₁ hγ₂) hKE
  filter_upwards [hae, hpath, h77 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθπ P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂]
    with ω hωE hωp h7
  intro s₀ t₀ h₀ hs₀ ht₀ u v hu hv
  obtain ⟨hMω, hC⟩ := hωp s₀ t₀ h₀ hs₀ ht₀
  obtain ⟨φ, -, -, c₁, c₂, -, -, -, -, -, -, -, hm₁, him₁, hm₂, him₂, -, -, hl₁, hl₂⟩ := hC
  -- Lemma 7.7: the outgoing paths stay in the closed active domain
  obtain ⟨s₀', t₀', h₀', hconf₁, hconf₂⟩ := h7 ⟨s₀, t₀, h₀.1, h₀.2.1, h₀.2.2.1⟩
  obtain ⟨rfl, rfl⟩ := Sec7.IsFirstContact.unique h₀' h₀
  have hNA := noArcStrict_of_mem_noArcEvent (hc₁ (X ω)) (hc₂ (X ω)) (hωE hMω)
  have hu' := invClock_lt him₁ hm₁ hu
  have hv' := invClock_lt him₂ hm₂ hv
  exact ⟨fun hH => (hNA _ _ hv' hu').2
      (hasCommonOpenSubarc_chart_of_physical hm₁ him₁ hm₂ him₂ hl₁ hl₂ hconf₁ hu hv hH),
    fun hH => (hNA _ _ hv' hu').1
      (hasCommonOpenSubarc_chart_of_physical hm₂ him₂ hm₁ him₁ hl₂ hl₁ hconf₂ hv hu hH)⟩

end Cross

end AuditFix

end InteractingSLE
