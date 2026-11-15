/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51TgtSep

/-!
# Theorem 1.2's Proposition 5.1 from Part A and (E1) for target-component excursions

Packet PROVE-PROP51-TGT (ruling R71; Astra's follow-up 4, Part (1), §1.7 L332–L501). PROVE-AUX61-R23 found that (E1)
holds — and is proved by Astra — only for fresh excursions restarted in the **original right-target component** of
`ℍ ∖ (R(K_s) ∪ η([0, t]))` (`Aux61Kernel.FwdNoEastCrosscutTgtQOn`), while PROVE-PROP51H-TOPO2's winding-number proof of
`Prop51G.FwdNoWrapQStatement` consumed (E1) for every post-contact excursion. This file proves the no-wrap step with
(E1) for target-component excursions only, and re-derives Theorem 1.2's two Proposition 5.1 inputs from it.

## The no-wrap step (`fwdNoWrapTgtQStatement`)

Hypotheses on a proper flow arc `η` and a regular counterflow at a time `s > 0`: the first exit does not end east
(`FirstContactNotEast … 0`), `η` has no last contact with `R(K_s)` (every excursion is bounded; below the critical gap,
`Prop51I.fwdNoLastContactQOn_smallGap`), and (E1) for target-component excursions. Suppose the counterflow tip is on
the left of `η`. In the counterflow chart `Ψ` (the tip at `∞`) take a free positive gate whose physical boundary value
is near `0` and the component `G` of `ℍ ∖ closure A` containing its half-ball (`A = Ψ(η ∩ D)`); `G` is on the right of
`η`. Every excursion adjacent to `G` has its later points in the target component (`isTargetComp_of_mem_closure`),
hence finishes west (`exists_west_of_adjacent`), hence — by the orientation step (`not_source_lt_start`) — starts left
of the gate. By Janiszewski's theorem (`mem_H_diff_fillH_adj`) the gate then lies in the unbounded domain of the
adjacent crosscuts, and `G`, being the gate's component off them, is unbounded: its far points are near the tip, on
the left of `η` (`false_of_not_isBounded`). Contradiction.

This is §1.7's argument with the outermost separator replaced by the gate component: the excursions bounding it are
exactly those "whose current access belongs to the original right-target component", and the separation lemma is
Janiszewski's theorem.

## Wiring

* **`prop51QOn_smallGap_of_tgt`**: Proposition 5.1 in the chart `Q` below the critical gap, from the counterflow's
  regularity and `FwdNoEastCrosscutTgtQOn` (with the proved first exit and no-last-contact);
* **`prop51QStatement_of_partA_of_tgt`**, **`cfFirstContactQStatement_of_partA_of_tgt`**: `Cond44Ref.Prop51QStatement`
  and Theorem 1.2's input `CfAvoidLeftQ.CfFirstContactQStatement` from Zhan's Part A inputs and (E1) in the
  target-component form (replacing PROVE-PROP51H-TOPO2's `…_of_noCrosscut'`, whose input `FwdNoEastCrosscutQOn` is not
  provable by the local route);
* `prop51QStatement_of_partA_of_window`, `cfFirstContactQStatement_of_partA_of_window`: the same from PROVE-AUX61-R23's
  named input `RestartWindowNullQOn` (restart comparison at one rational window);
* `fwdNoEastCrosscutTgtQOn_of_eastSide`: the target-component (E1) from its `HitsEastSideAlong` form.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

universe u

namespace InteractingSLE.Sec5.Prop51Tgt

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G Prop51HTopo Prop51HGate
open HalfPlaneSep

/-! ### The deterministic no-wrap step -/

/-- **The no-wrap step of Proposition 5.1 in the chart `Q`, with (E1) for target-component excursions** (spec p. 135
with R45, R50; Astra's follow-up 4, §1.7). Let `η` be a proper arc from `0`, `β` a Loewner trace of a continuous driver
`w` from `0` that never returns to `0`, and `s > 0`. If the first excursion of `η` in `ℍ ∖ R(K_s)` does not end in the
eastern part, `η` has no last contact with `R(K_s)`, and no eastern chart crosscut of `η` has a rational restart time
`t` after which a point of the crosscut lies in the original right-target component of `ℍ ∖ (R(K_s) ∪ η([0, t]))`,
then the counterflow tip `R(β(s))` is not on the left of `η`. -/
def FwdNoWrapTgtQStatement : Prop :=
  ∀ (η : ℝ → ℂ) (w : ℝ → ℝ) (β : ℝ → ℂ) (s : ℝ), IsProperArc η → Continuous w → w 0 = 0 →
    IsLoewnerTrace w β → 0 < s → (∀ v : ℝ, 0 < v → β v ≠ 0) →
    FirstContactNotEast w s 0 η → (∀ t : ℝ, ∃ v : ℝ, t < v ∧ η v ∉ H \ cfHullQ w s) →
    (∀ t : ℚ, 0 < t → ∀ τ₀ ∈ Ioo (0 : ℝ) t, ∀ u₀ : ℝ, (t : ℝ) < u₀ → Aux61Loc.IsEastCrosscut w s η τ₀ u₀ →
      ∀ u ∈ Ioo (t : ℝ) u₀, ¬ Aux61Kernel.IsTargetComp w s η t (η u)) →
    negInv (β s) ∉ leftSideOf (arcRange η)

/-- **`FwdNoWrapTgtQStatement`, proved** (the gate component, its western bounding excursions, the orientation step
and Janiszewski's theorem). -/
theorem fwdNoWrapTgtQStatement : FwdNoWrapTgtQStatement := by
  intro η w β s hη hw hw0 hβ hs0 hβne h0 hnl hE1 hL
  have hs : 0 ≤ s := hs0.le
  have hβs : β s ≠ 0 := hβne s hs0
  have htip : negInv (β s) ∉ arcRange η := hL.1.2
  set A := chartFlowSet η w s with hAdef
  have hbd : IsBounded A := isBounded_revChart_arcRange_of_mem_leftSideOf hη hβ hw hw0 hs hL
  obtain ⟨R, hR0, hR⟩ := exists_closure_subset_ball hbd
  -- the gate, with its physical boundary value near `0`
  obtain ⟨ρ, hρ, hρK⟩ := exists_pos_lt_norm_of_mem_cfHullQ hw hs0
  obtain ⟨g, hgρ⟩ := exists_positiveBoundaryGate_lt hη hβ hw hw0 hs (half_pos hρ)
  have : (𝓝[H] (g.source : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (closure_H ▸ mem_Hbar_of_im_eq_zero (by simp))
  obtain ⟨w₀, hw₀R, hw₀H, hw₀b⟩ := ((g.boundary_limit.eventually
    (Prop411Q.eventually_mem_rightSideOf hη g.target_pos)).and
    (show ∀ᶠ z in 𝓝[H] (g.source : ℂ), z ∈ H ∩ ball (g.source : ℂ) g.radius from
      inter_mem_nhdsWithin H (ball_mem_nhds _ g.radius_pos))).exists
  -- the gate component `G`
  set G := connectedComponentIn (H \ closure A) w₀ with hGdef
  have hgateA : ball (g.source : ℂ) g.radius ∩ H ⊆ H \ closure A := fun z hz =>
    ⟨hz.2, fun hzA => (Set.eq_empty_iff_forall_notMem.1 g.avoids) z ⟨hz.1, hzA⟩⟩
  have hw₀G : w₀ ∈ G := mem_connectedComponentIn (hgateA ⟨hw₀b, hw₀H⟩)
  have hGc : IsPreconnected G := isPreconnected_connectedComponentIn
  have hGsub : G ⊆ H \ closure A := connectedComponentIn_subset _ _
  have hGA : G ⊆ H \ A := fun z hz => ⟨(hGsub hz).1, fun h => (hGsub hz).2 (subset_closure h)⟩
  have hGgate : ball (g.source : ℂ) g.radius ∩ H ⊆ G :=
    ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected.subset_connectedComponentIn
      ⟨hw₀b, hw₀H⟩ hgateA
  have hGo : IsOpen G := (QuantumZipper.isOpen_H.sdiff isClosed_closure).connectedComponentIn
  -- `G` is on the right of `η`
  have hGR : ∀ z ∈ G, revChartInv w s z ∈ rightSideOf (arcRange η) := by
    have hSsub : revChartInv w s '' G ⊆ H \ arcRange η := by
      rintro _ ⟨z, hz, rfl⟩
      have hm := revChartInv_mem hw hw0 hs (hGA hz).1
      exact ⟨hm.1, fun hzP => (hGA hz).2
        ⟨revChartInv w s z, ⟨hzP, hm⟩, revChart_revChartInv hw hw0 hs (hGA hz).1⟩⟩
    have hSc : IsPreconnected (revChartInv w s '' G) :=
      hGc.image _ ((continuousOn_revChartInv hw hw0 hs).mono fun z hz => (hGA hz).1)
    intro z hz
    have hsame : revChartInv w s z ∈ connectedComponentIn (H \ arcRange η) (revChartInv w s w₀) :=
      hSc.subset_connectedComponentIn ⟨w₀, hw₀G, rfl⟩ hSsub ⟨z, hz, rfl⟩
    obtain ⟨-, x, hx, hxA, hxcl⟩ := hw₀R
    refine ⟨hSsub ⟨z, hz, rfl⟩, x, hx, hxA, ?_⟩
    rwa [← connectedComponentIn_eq hsame]
  -- the target-component transfer
  have htgt : ∀ {t u : ℝ}, 0 ≤ t → t < u → η u ∈ H \ cfHullQ w s → revChart w s (η u) ∈ closure G →
      Aux61Kernel.IsTargetComp w s η t (η u) := fun ht htu hu hcl =>
    isTargetComp_of_mem_closure hη hw hw0 hs g hρK hgρ hGc hGA hGgate ht htu hu hcl
  -- the excursions adjacent to `G`: western, starting left of the gate
  set 𝒜 : Set (Set ℝ) := {C | ∃ v ∈ excursionTimes η w s,
    C = connectedComponentIn (excursionTimes η w s) v ∧ revChart w s (η v) ∈ closure G} with h𝒜def
  have h𝒜 : ∀ C ∈ 𝒜, ∃ u ∈ excursionTimes η w s, C = connectedComponentIn (excursionTimes η w s) u :=
    fun C hC' => by
      obtain ⟨v, hv, hC, -⟩ := hC'
      exact ⟨v, hv, hC⟩
  have hcut : ∀ C ∈ 𝒜, ∃ κ : ExcursionChartCut η w s C, κ.start < g.source ∧ κ.finish < g.source := by
    rintro C ⟨v, hv, rfl, hvcl⟩
    obtain ⟨e, xf, hxf, hlimf⟩ := exists_west_of_adjacent hη hβ hw hw0 hs htip h0 hnl hE1 hv
      (fun t ht htv => htgt ht htv hv.2 hvcl)
    obtain ⟨κ⟩ := nonempty_excursionChartCut_of_west hη hβ hw hw0 hs htip e hxf hlimf
    refine ⟨κ, ?_, κ.finish_neg.trans g.source_pos⟩
    obtain ⟨t₀, ht₀, ht₀v⟩ := κ.time_surj (mem_connectedComponentIn hv)
    have hq : κ.cut t₀ ∈ closure G := by rw [κ.cut_eq t₀ ht₀, ht₀v]; exact hvcl
    have hnot := not_source_lt_start hη hw hw0 hs g hGc hGA hGgate hGR κ ht₀ hq
    have hne : κ.start ≠ g.source := by
      intro he
      have h1 := κ.start_mem_closure
      rw [he] at h1
      exact (Set.eq_empty_iff_forall_notMem.1 g.avoids) _ ⟨mem_ball_self g.radius_pos, h1⟩
    exact lt_of_le_of_ne (not_lt.1 hnot) hne
  choose κ hκ using hcut
  classical
  let Fc : Set ℝ → Set ℂ := fun C => if hC : C ∈ 𝒜 then (κ C hC).cut '' Icc 0 1 else ∅
  have hFc : ∀ C ∈ 𝒜, ∃ κ' : ExcursionChartCut η w s C,
      Fc C = κ'.cut '' Icc 0 1 ∧ κ'.start < g.source ∧ κ'.finish < g.source :=
    fun C hC => ⟨κ C hC, by simp only [Fc, hC, ↓reduceDIte], hκ C hC⟩
  -- Janiszewski: the gate is in the unbounded domain of the adjacent crosscuts
  have hfree := mem_H_diff_fillH_adj hη hw hw0 hs g.radius_pos g.avoids hR0 hR h𝒜 hFc hw₀b hw₀H
  set FB := closure (⋃ C ∈ 𝒜, Fc C) with hFBdef
  have hX : IsOpen (H \ FB) := QuantumZipper.isOpen_H.sdiff isClosed_closure
  -- the component of the gate off the adjacent crosscuts is `G`
  have hsplit : connectedComponentIn (H \ FB) w₀ ⊆ G ∪ ((H \ FB) \ closure G) := by
    intro z hz
    have hzX := connectedComponentIn_subset _ _ hz
    by_cases hzcl : z ∈ closure G
    · left
      by_cases hzA : z ∈ closure A
      · exfalso
        apply hzX.2
        obtain ⟨p, ⟨⟨v, hv0, rfl⟩, hpD⟩, hzp⟩ := mem_chartFlowSet_of_mem_closure hη hw hw0 hs hzA hzX.1
        have hvpos : 0 < v := by
          rcases (mem_Ici.1 hv0).eq_or_lt with he | he
          · have hH := hpD.1
            rw [← he, hη.zero] at hH
            exact (lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hH)).elim
          · exact he
        have hvU : v ∈ excursionTimes η w s := ⟨hvpos, hpD⟩
        have hC : connectedComponentIn (excursionTimes η w s) v ∈ 𝒜 := ⟨v, hvU, rfl, hzp ▸ hzcl⟩
        refine subset_closure (mem_iUnion₂.2 ⟨_, hC, ?_⟩)
        simp only [Fc, hC, ↓reduceDIte]
        obtain ⟨t₀, ht₀, ht₀v⟩ := (κ _ hC).time_surj (mem_connectedComponentIn hvU)
        exact ⟨t₀, Ioo_subset_Icc_self ht₀, by rw [(κ _ hC).cut_eq t₀ ht₀, ht₀v, hzp]⟩
      · have hzo : z ∈ H \ closure A := ⟨hzX.1, hzA⟩
        have hCo : IsOpen (connectedComponentIn (H \ closure A) z) :=
          (QuantumZipper.isOpen_H.sdiff isClosed_closure).connectedComponentIn
        obtain ⟨p, hpC, hpG⟩ := (_root_.mem_closure_iff.1 hzcl) _ hCo (mem_connectedComponentIn hzo)
        have h1 : connectedComponentIn (H \ closure A) w₀ = connectedComponentIn (H \ closure A) p :=
          connectedComponentIn_eq hpG
        have h2 : connectedComponentIn (H \ closure A) z = connectedComponentIn (H \ closure A) p :=
          connectedComponentIn_eq hpC
        show z ∈ connectedComponentIn (H \ closure A) w₀
        rw [h1, ← h2]
        exact mem_connectedComponentIn hzo
    · exact Or.inr ⟨hzX, hzcl⟩
  have hw₀X : w₀ ∈ H \ FB := H_diff_fillH_subset_H_diff isClosed_closure hfree
  have hPG : connectedComponentIn (H \ FB) w₀ ⊆ G :=
    isPreconnected_connectedComponentIn.subset_left_of_subset_union hGo (hX.sdiff isClosed_closure)
      (Set.disjoint_left.2 fun z hzG hz => hz.2 (subset_closure hzG)) hsplit
      ⟨w₀, mem_connectedComponentIn hw₀X, hw₀G⟩
  have hunb : ¬ IsBounded (connectedComponentIn (H \ FB) w₀) :=
    ((mem_H_diff_fillH_of_isClosed isClosed_closure).1 hfree).2
  exact false_of_not_isBounded hη hβ hw hw0 hs hβs hL (fun z hz => (hGA hz).1) hGR
    fun hb => hunb (hb.subset hPG)

/-! ### Proposition 5.1 in the chart `Q` and Theorem 1.2's input -/

/-- **Proposition 5.1 in the chart `Q` below the critical gap from (E1) for target-component excursions**: the
pathwise reduction `prop51QOn_of_gluedQ` with `fwdNoWrapTgtQStatement`, the proved first exit
(`fwdFirstExitQOn_smallGap`) and the proved absence of a last contact (`Prop51I.fwdNoLastContactQOn_smallGap`). -/
theorem prop51QOn_smallGap_of_tgt (hreg : Prop51Q.CfLineRegularQStatement.{u})
    (htgt : Aux61Kernel.FwdNoEastCrosscutTgtQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) :
    Prop51QOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂ :=
  prop51QOn_of_gluedQ hreg
    (GluedQ.and (fwdFirstExitQOn_smallGap hreg) (GluedQ.and (Prop51I.fwdNoLastContactQOn_smallGap hreg) htgt))
    fun η w β s hη hw hw0 hβ hs hne hΦ =>
      fwdNoWrapTgtQStatement η w β s hη hw hw0 hβ hs hne hΦ.1 hΦ.2.1 hΦ.2.2

/-- **`Cond44Ref.Prop51QStatement` from Zhan's Part A inputs and (E1) for target-component excursions below the
critical gap** (at and above it, `Prop51H.prop51QOn_largeGap_of_partA`). -/
theorem prop51QStatement_of_partA_of_tgt (hA : PartAInputsSixteenDiv)
    (htgt : Aux61Kernel.FwdNoEastCrosscutTgtQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) :
    Cond44Ref.Prop51QStatement.{u} :=
  prop51QStatement_of_on IsLargeGap (Prop51H.prop51QOn_largeGap_of_partA hA)
    (prop51QOn_smallGap_of_tgt (CfLineRegQ.cfLineRegularQStatement_of_partA hA) htgt)

/-- **Theorem 1.2's input `CfAvoidLeftQ.CfFirstContactQStatement` from Zhan's Part A inputs and (E1) for
target-component excursions** (through `CfAvoidLeftQ.cfFirstContactQStatement_of_prop51Q`). -/
theorem cfFirstContactQStatement_of_partA_of_tgt (hA : PartAInputsSixteenDiv)
    (htgt : Aux61Kernel.FwdNoEastCrosscutTgtQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) :
    CfAvoidLeftQ.CfFirstContactQStatement.{u} :=
  CfAvoidLeftQ.cfFirstContactQStatement_of_prop51Q (CfLineRegQ.cfLineRegularQStatement_of_partA hA)
    (prop51QStatement_of_partA_of_tgt hA htgt)

/-- **`Cond44Ref.Prop51QStatement` from Zhan's Part A inputs and PROVE-AUX61-R23's named input** (the restart
comparison at one rational window, below the critical gap). -/
theorem prop51QStatement_of_partA_of_window (hA : PartAInputsSixteenDiv)
    (hwin : Aux61Kernel.RestartWindowNullQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) :
    Cond44Ref.Prop51QStatement.{u} :=
  prop51QStatement_of_partA_of_tgt hA
    (Aux61Kernel.fwdNoEastCrosscutTgtQOn_of_window (CfLineRegQ.cfLineRegularQStatement_of_partA hA) hwin)

/-- **Theorem 1.2's input `CfAvoidLeftQ.CfFirstContactQStatement` from Zhan's Part A inputs and PROVE-AUX61-R23's
named input.** -/
theorem cfFirstContactQStatement_of_partA_of_window (hA : PartAInputsSixteenDiv)
    (hwin : Aux61Kernel.RestartWindowNullQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) :
    CfAvoidLeftQ.CfFirstContactQStatement.{u} :=
  cfFirstContactQStatement_of_partA_of_tgt hA
    (Aux61Kernel.fwdNoEastCrosscutTgtQOn_of_window (CfLineRegQ.cfLineRegularQStatement_of_partA hA) hwin)

/-- **The target-component (E1) from its `HitsEastSideAlong` form** (the converse of
`Aux61Kernel.fwdPostContactEastSideTgtQOn_of_crosscut`, deterministic on each sample): an eastern chart crosscut whose
remainder after a rational restart `t` meets the target component is a post-contact excursion running at `t` that hits
the eastern side proper. -/
theorem fwdNoEastCrosscutTgtQOn_of_eastSide {G : ℝ → ℝ → ℝ → Prop}
    (hside : Aux61Kernel.FwdPostContactEastSideTgtQOn.{u} G) : Aux61Kernel.FwdNoEastCrosscutTgtQOn.{u} G := by
  refine GluedQ.mono hside fun s η w hp t ht τ₀ hτ₀ u₀ htu hcross u hu htc => ?_
  obtain ⟨hτ0, -, hτD, -, hD, -, x₁, hx₁, hlim⟩ := hcross
  have hDt : η t ∈ H \ cfHullQ w s := hD t ⟨hτ₀.2, htu⟩
  have hDu : ∀ v ∈ Ioo (t : ℝ) u₀, η v ∈ H \ cfHullQ w s := fun v hv => hD v ⟨hτ₀.2.trans hv.1, hv.2⟩
  refine hp t ht ⟨τ₀, ⟨hτ0, hτ₀.2.le⟩, hτD⟩ hDt u₀ htu hDu ⟨u, hu, htc⟩ ⟨x₁, hx₁, ?_⟩
  exact mapClusterPt_of_tendsto_left htu hDu hlim

end InteractingSLE.Sec5.Prop51Tgt
