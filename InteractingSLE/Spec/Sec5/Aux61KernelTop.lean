/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61KernelWindow
import InteractingSLE.Spec.Sec5.Prop51HQNoContact

/-!
# (E1) for fresh excursions in the original right-target component, from the restart comparison at one window

Packet PROVE-AUX61-R23, piece R6 (the countable localization and the wiring). Sources: Astra's follow-up 4, Part (1)
(`source/external/AstraIG1/ig1_followup4_audited.txt`; ruling R71), §1 "Answer and scope" (L68–L80: "At a rational
flow-line time `r` … suppose that `dist(η(r), K) > 0` and that its current access belongs to the component containing
that target. Conditional on the two full histories, the next continuous boundary endpoint in that component cannot be
on an exposed open eastern side of `K`"), §1.3 (L162–L260) and §1.6 (L316–L331, "Intersect the probability-one events
over the countable rational times and the countable collar localizations").

## The target-component condition

Astra's (E1) — and its use in the no-wrap separation (§1.7, the outermost exterior excursion, L455–L463: "the whole
remaining excursion is therefore in the original right-target component") — is a statement about fresh excursions
**whose current access belongs to the original right-target component** of `ℍ ∖ (K ∪ η([0, r]))`. The conditional
heights used by the comparison ((1.2), L170–L178) are those of that component. `Aux61Loc.FwdNoEastCrosscutQOn` (PROVE-
AUX61LOC) has no such condition; an excursion restarted in another component (a pocket cut off by the old flow prefix
and `K`, possible after a passage of `η` through a pinch point of the filled hull) is not covered by the local
comparison, and excluding it amounts to Proposition 5.1 itself. This file therefore states (E1) in Astra's form:

* `IsTargetComp w s η t z`: `z` lies in the component of `ℍ ∖ (R(K_s) ∪ η([0, t]))` that contains a half-disc at a
  positive real point (the component adjacent to the free part of `ℝ₊`, which carries the original target; the old
  flow prefix and `R(K_s)` meet `ℝ₊` nowhere, so this component is unique);
* **`FwdNoEastCrosscutTgtQOn G`**: almost surely on the glued space, no eastern chart crosscut whose restart at a
  rational time `t` is in the target component (the form consumed by the outermost-excursion separation, PROVE-
  PROP51H-TOPO2).

## The reduction

* `RestartWindowEvent w s η t c`: the window `c` of `Aux61KernelWindow` at the restart `t`, its excursion event, and
  the target condition;
* **`RestartWindowNullQOn G`** (named input, the restart comparison at one window: Aux. lemmas 61–64 at a separated
  rational restart, Astra §§1.1–1.3): for every rational `t > 0` and every window code `c`, almost surely the window
  event does not happen;
* `GluedQ.forall_countable`: countably many `GluedQ` properties hold together;
* **`fwdNoEastCrosscutTgtQOn_of_window`**: `FwdNoEastCrosscutTgtQOn G` from `RestartWindowNullQOn G` and the
  counterflow's regularity (`exists_isWindow` on every sample);
* `PostContactEastSideTgt`, `FwdPostContactEastSideTgtQOn`: the same in PROVE-PROP51I's `HitsEastSideAlong` form (the
  restart condition of the no-wrap topology, with the target condition), `fwdPostContactEastSideTgtQOn_of_crosscut`,
  **`fwdPostContactEastSideTgtQOn_of_window`**;
* `GluedQ.of_regimes`; **`restartWindowNullQOn_largeGap`** (proved: at and above the critical gap the flow line never
  meets the hull, `Prop51G.fwdNoContactQStatement`); `restartWindowNullQOn_of_smallGap`,
  **`fwdNoEastCrosscutTgtQOn_of_window_smallGap`**: the named input is needed only below the critical gap.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Complex
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.Aux61Kernel

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord CrossCond CrossCond.Word49 LawUnique Cond44Ref Prop411Q Prop51G Prop51H Prop51I Aux61Loc

/-! ### The target component and the two statements -/

/-- **The original right-target component** of `ℍ ∖ (R(K_s) ∪ η([0, t]))`: the point `z` lies in the component that
contains a half-disc `{y ∈ ℍ : |y − x| < ρ}` at some positive real point `x` (the component adjacent to the free part
of `ℝ₊`; Astra follow-up 4, §1.1 "its current access belongs to the component containing that target"). -/
def IsTargetComp (w : ℝ → ℝ) (s : ℝ) (η : ℝ → ℂ) (t : ℝ) (z : ℂ) : Prop :=
  ∃ x : ℝ, 0 < x ∧ ∀ᶠ y in 𝓝[H] (x : ℂ), y ∈ connectedComponentIn (H \ (cfHullQ w s ∪ η '' Icc 0 t)) z

/-- **(E1) for fresh excursions in the target component** (Astra follow-up 4, Part (1), the precise conclusion at
L68–L80 and §1.6), almost surely on the glued space of `Cond44Ref.Prop51QStatement`, at every positive rational
counterflow time `s` and restart time `t`, on the regime `G`: if the excursion of the flow line in `ℍ ∖ R(K_s)` from a
contact at `τ₀ ∈ (0, t)` to an end time `u₀ > t` is an eastern chart crosscut (`IsEastCrosscut`), then its points after
`t` are not in the original right-target component of `ℍ ∖ (R(K_s) ∪ η([0, t]))`. -/
def FwdNoEastCrosscutTgtQOn (G : ℝ → ℝ → ℝ → Prop) : Prop :=
  GluedQ.{u} G fun s η w => ∀ t : ℚ, 0 < t → ∀ τ₀ ∈ Ioo (0 : ℝ) t, ∀ u₀ : ℝ, (t : ℝ) < u₀ →
    IsEastCrosscut w s η τ₀ u₀ → ∀ u ∈ Ioo (t : ℝ) u₀, ¬ IsTargetComp w s η t (η u)

/-- **The window event at the restart `t` with the code `c`**: the window (`IsWindow`), its excursion (a contact
before `t − δ`, none on `[t − δ, t]`, the excursion running at `t` stays in the window in the chart `Ψ` and lands at a
real point at its end time `u₀`), and the target-component condition at a point of the excursion. -/
def RestartWindowEvent (w : ℝ → ℝ) (s : ℝ) (η : ℝ → ℂ) (t : ℝ) (c : WinCode) : Prop :=
  IsWindow w s η t c ∧ ∃ u₀ : ℝ, WindowExcursion w s η t c u₀ ∧ ∃ u ∈ Ioo t u₀, IsTargetComp w s η t (η u)

/-- **Named input: the restart comparison at one window** (Aux. lemmas 61–64 at a separated rational restart; Astra
follow-up 4, §§1.1–1.3): for every positive rational restart time `t` and every window code `c`, almost surely on the
glued space the window event does not happen — a fresh excursion in the original right-target component does not land,
inside a window whose real points lie on the eastern side `(junR, ∞)` of the counterflow chart, at an eastern point. -/
def RestartWindowNullQOn (G : ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ (t : ℚ) (c : WinCode), 0 < t → GluedQ.{u} G fun s η w => ¬ RestartWindowEvent w s η t c

/-! ### Countable conjunctions of glued properties -/

/-- **Countably many `GluedQ` properties hold together.** -/
theorem GluedQ.forall_countable {G : ℝ → ℝ → ℝ → Prop} {ι : Type*} [Countable ι]
    {Φ : ι → ℝ → (ℝ → ℂ) → (ℝ → ℝ) → Prop} (h : ∀ i, GluedQ.{u} G (Φ i)) :
    GluedQ.{u} G fun s η w => ∀ i, Φ i s η w := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P _ hf η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
  exact ae_all_iff.2 fun i => h i κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P hf η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs

/-! ### The wiring -/

/-- **(E1) in the target component from the restart comparison at one window**, given the counterflow's regularity:
on every glued sample, an eastern chart crosscut restarted at a rational `t` in the target component has a rational
window (`exists_isWindow`) whose window event happens, which the countably many null events exclude. -/
theorem fwdNoEastCrosscutTgtQOn_of_window {G : ℝ → ℝ → ℝ → Prop} (hreg : Prop51Q.CfLineRegularQStatement.{u})
    (hwin : RestartWindowNullQOn.{u} G) : FwdNoEastCrosscutTgtQOn.{u} G := by
  have hall : GluedQ.{u} G fun s η w => ∀ i : ℚ × WinCode, 0 < i.1 → ¬ RestartWindowEvent w s η i.1 i.2 := by
    refine (GluedQ.forall_countable (ι := ℚ × WinCode)
      (Φ := fun i s η w => 0 < i.1 → ¬ RestartWindowEvent w s η i.1 i.2) fun i => ?_)
    by_cases hi : 0 < i.1
    · exact (hwin i.1 i.2 hi).mono fun _ _ _ hp _ => hp
    · intro κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P _ hf η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
      exact Eventually.of_forall fun _ h => absurd h hi
  intro κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
  have hχ := Sec4.chiC_pos hκ hκ4
  have hθχ : θ₁ * chiC κ ≤ θ₂ * chiC κ := mul_le_mul_of_nonneg_right h12.le hχ.le
  have hF := Theorem15.isOrderedForceWord_flowLine (Sec7.prop74Data a b) {0} 0
  have h44 := Sec7.Lemma71H.cond44_flowLine_prop74Data (θ := θ₂) hκ (a := a) (b := b) ha (by linarith)
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  have hXm : Measurable fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)) :=
    (measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)
  have harc := ae_glue_fst (μ := P) k hXm (ae_isProperArc_of_isFlowLine hκ hκ4.le hadm hfl)
  have hregG := hreg κ hκ hκ4 a b θ₁ hb (by linarith) P h hh P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  filter_upwards [harc, hregG, hall κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs]
    with p hpa hpr hpn t ht τ₀ hτ₀ u₀ htu hcross u hu htgt
  obtain ⟨-, hwc, hw0, hβ, -, -⟩ := hpr
  obtain ⟨c, hW, hE⟩ := exists_isWindow hpa hwc hw0 hβ (by exact_mod_cast hs.le) hcross ⟨hτ₀.2, htu⟩
  exact hpn (t, c) ht ⟨hW, u₀, hE, u, hu, htgt⟩

/-! ### The `HitsEastSideAlong` form (PROVE-PROP51I's (E1), with the target condition) -/

/-- **(E1) for one restart in the target component, in the `HitsEastSideAlong` form**
(`Prop51I.PostContactEastSideResidual` with Astra's target condition): if the flow line has met `R(K_s)` in `(0, t]`,
is in `ℍ ∖ R(K_s)` at `t`, and its excursion running at `t` on `(t, u₀)` is in the original right-target component,
that excursion does not hit the eastern side proper as `u ↑ u₀`. -/
def PostContactEastSideTgt (w : ℝ → ℝ) (s t : ℝ) (η : ℝ → ℂ) : Prop :=
  (∃ v ∈ Ioc 0 t, η v ∉ H \ cfHullQ w s) → η t ∈ H \ cfHullQ w s → ∀ u₀, t < u₀ →
    (∀ v ∈ Ioo t u₀, η v ∈ H \ cfHullQ w s) → (∃ u ∈ Ioo t u₀, IsTargetComp w s η t (η u)) →
    ¬ HitsEastSideAlong w s η (𝓝[Ioo t u₀] u₀)

/-- **(E1) in the target component, in the `HitsEastSideAlong` form**, almost surely on the glued space at every
positive rational counterflow time `s` and restart time `t`, on the regime `G`. -/
def FwdPostContactEastSideTgtQOn (G : ℝ → ℝ → ℝ → Prop) : Prop :=
  GluedQ.{u} G fun s η w => ∀ t : ℚ, 0 < t → PostContactEastSideTgt w s t η

/-- **The `HitsEastSideAlong` form from the crosscut form** (deterministic on every sample: an eastern hit of the
excursion running at `t` is an eastern chart crosscut from the last contact,
`Aux61Loc.isEastCrosscut_of_hitsEastSideAlong`). -/
theorem fwdPostContactEastSideTgtQOn_of_crosscut {G : ℝ → ℝ → ℝ → Prop}
    (hreg : Prop51Q.CfLineRegularQStatement.{u}) (hno : FwdNoEastCrosscutTgtQOn.{u} G) :
    FwdPostContactEastSideTgtQOn.{u} G := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
  have hχ := Sec4.chiC_pos hκ hκ4
  have hθχ : θ₁ * chiC κ ≤ θ₂ * chiC κ := mul_le_mul_of_nonneg_right h12.le hχ.le
  have hF := Theorem15.isOrderedForceWord_flowLine (Sec7.prop74Data a b) {0} 0
  have h44 := Sec7.Lemma71H.cond44_flowLine_prop74Data (θ := θ₂) hκ (a := a) (b := b) ha (by linarith)
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  have hXm : Measurable fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)) :=
    (measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)
  have harc := ae_glue_fst (μ := P) k hXm (ae_isProperArc_of_isFlowLine hκ hκ4.le hadm hfl)
  have hregG := hreg κ hκ hκ4 a b θ₁ hb (by linarith) P h hh P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  filter_upwards [harc, hregG, hno κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs]
    with p hpa hpr hpn t ht hc hDt u₀ htu hD htgt hhit
  obtain ⟨-, hwc, hw0, hβ, -, -⟩ := hpr
  obtain ⟨τ₀, hτ₀, hcross⟩ := isEastCrosscut_of_hitsEastSideAlong hpa hwc hw0 hβ (by exact_mod_cast hs.le) hc hDt
    htu hD hhit
  obtain ⟨u, hu, hut⟩ := htgt
  exact hpn t ht τ₀ hτ₀ u₀ htu hcross u hu hut

/-- **(E1) in the target component, `HitsEastSideAlong` form, from the restart comparison at one window.** -/
theorem fwdPostContactEastSideTgtQOn_of_window {G : ℝ → ℝ → ℝ → Prop} (hreg : Prop51Q.CfLineRegularQStatement.{u})
    (hwin : RestartWindowNullQOn.{u} G) : FwdPostContactEastSideTgtQOn.{u} G :=
  fwdPostContactEastSideTgtQOn_of_crosscut hreg (fwdNoEastCrosscutTgtQOn_of_window hreg hwin)

/-! ### Regimes: the large-gap case is free -/

/-- **A glued property on all angles from its two regimes.** -/
theorem GluedQ.of_regimes {G : ℝ → ℝ → ℝ → Prop} {Φ : ℝ → (ℝ → ℂ) → (ℝ → ℝ) → Prop} (h₁ : GluedQ.{u} G Φ)
    (h₂ : GluedQ.{u} (fun κ θ₁ θ₂ => ¬ G κ θ₁ θ₂) Φ) : GluedQ.{u} (fun _ _ _ => True) Φ := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 _ hb ha Ω mΩ P _ hf η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂' W₂ ζ₂ hcf hlaw k _ hk s hs
  by_cases hG : G κ θ₁ θ₂
  · exact h₁ κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P hf η ζ hh hfl P₂ h₂' W₂ ζ₂ hcf hlaw k hk s hs
  · exact h₂ κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P hf η ζ hh hfl P₂ h₂' W₂ ζ₂ hcf hlaw k hk s hs

/-- **The restart comparison at one window holds in the large-gap regime** (`θ₂ − θ₁ ≥ πκ/(4 − κ)`): there the flow
line never meets the counterflow hull (`Prop51G.fwdNoContactQStatement`, Aux. lemma 22's empty-span case), so no
window event (which needs a contact before the restart) happens. -/
theorem restartWindowNullQOn_largeGap : RestartWindowNullQOn.{u} IsLargeGap := by
  intro t c _ κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
  have hχ := Sec4.chiC_pos hκ hκ4
  have hθχ : θ₁ * chiC κ ≤ θ₂ * chiC κ := mul_le_mul_of_nonneg_right h12.le hχ.le
  have hF := Theorem15.isOrderedForceWord_flowLine (Sec7.prop74Data a b) {0} 0
  have h44 := Sec7.Lemma71H.cond44_flowLine_prop74Data (θ := θ₂) hκ (a := a) (b := b) ha (by linarith)
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  have hXm : Measurable fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)) :=
    (measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)
  have harc := ae_glue_fst (μ := P) k hXm (ae_isProperArc_of_isFlowLine hκ hκ4.le hadm hfl)
  filter_upwards [harc, fwdNoContactQStatement κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw
    k hk s hs] with p hpa hnc
  rintro ⟨-, u₀, ⟨⟨τ₀, hτ₀, hτD⟩, -⟩, -⟩
  exact hτD ⟨hpa.mem_H τ₀ hτ₀.1, hnc.1 τ₀ hτ₀.1⟩

/-- **The restart comparison on all angles from the small-gap regime** (the large-gap regime is free). -/
theorem restartWindowNullQOn_of_smallGap
    (hsmall : RestartWindowNullQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) :
    RestartWindowNullQOn.{u} fun _ _ _ => True := fun t c ht =>
  GluedQ.of_regimes (restartWindowNullQOn_largeGap t c ht) (hsmall t c ht)

/-- **(E1) in the target component on all angles, from the restart comparison below the critical gap.** -/
theorem fwdNoEastCrosscutTgtQOn_of_window_smallGap (hreg : Prop51Q.CfLineRegularQStatement.{u})
    (hsmall : RestartWindowNullQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) :
    FwdNoEastCrosscutTgtQOn.{u} fun _ _ _ => True :=
  fwdNoEastCrosscutTgtQOn_of_window hreg (restartWindowNullQOn_of_smallGap hsmall)

end InteractingSLE.Sec5.Aux61Kernel
