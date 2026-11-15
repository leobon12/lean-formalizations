/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HQPost

/-!
# Proposition 5.1's forward route in the chart `Q`: the eastern end of `∞` (E2) is excluded below the critical gap

Packet PROVE-PROP51I, item (c). PROVE-PROP51H reduced the post-contact barrier of the forward route to the residual
`Prop51H.FwdPostContactEastQOn` with two clauses: **(E1)** after a contact, an excursion of the flow line `η` in
`ℍ ∖ R(K_s)` does not end at a finite time on the eastern side proper of the counterflow hull, and **(E2)** after a
contact, an excursion that never ends does not leave through the eastern end of `∞` (R50, Astra's follow-up C).

**(E2) needs no Cameron–Martin argument below the critical gap.** Its premise — `η` stays in `ℍ ∖ R(K_s)` at every
time after the rational restart time `t` — is itself almost surely false there:

* below the critical gap `θ₂ − θ₁ < πκ/(4 − κ)` the flow line meets the counterflow hull `R(K_{s′})` at a finite
  positive time for **every** positive rational counterflow time `s′` (`fwdHitQOn_smallGap`: the first exit of
  PROVE-PROP51G, `Prop51G.ae_exitT`, is a hit of the western side at a finite time, never an end at `∞`);
* the counterflow hulls shrink to `∞` as `s′ ↓ 0` (`exists_rat_cfHullQ_far`, from the hull radius bound
  `QuantumZipper.CaraR.fwdHull_subset_closedBall`), while the prefix `η([0, t])` is compact; so for small `s′` the
  hit of `R(K_{s′}) ⊆ R(K_s)` happens after `t` (`not_forall_mem_of_hits`), which the premise forbids.

This is the scale picture behind Theorem 1.5's critical angle: below it the flow line bounces off the counterflow's
western side at all scales up to `∞`, so it has no last contact with `R(K_s)`.

* `notMem_of_tendsto_revChart_real`: a real chart limit at `t₀` puts `η(t₀)` outside `ℍ ∖ R(K_s)`;
* **`FwdHitQOn`**, **`fwdHitQOn_smallGap`**: the hit statement on the glued space, proved below the critical gap;
* `exists_rat_cfHullQ_far`, **`not_forall_mem_of_hits`** (deterministic);
* **`PostContactEastSideResidual`**, **`FwdPostContactEastSideQOn`**: the residual reduced to (E1) alone;
* **`FwdNoLastContactQOn`**, **`fwdNoLastContactQOn_smallGap`**: below the critical gap the flow line has no last
  contact with `R(K_s)` (every excursion after a positive time is bounded);
* **`fwdPostContactEastQOn_of_side`**: `Prop51H.FwdPostContactEastQOn` below the critical gap from (E1) alone;
* `prop51QStatement_of_partA_of_eastSide`, `cfFirstContactQStatement_of_partA_of_eastSide`: the wiring.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or a `*_of_param` result (the only probabilistic input is
PROVE-PROP51G's `ae_exitT`, from PROVE-CROSSCOND-THETA's image word and Aux. lemma 22).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.Prop51I

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord CrossCond CrossCond.Word49 CrossCond.Theta MartChar.RealFlow LawUnique Cond44Ref Prop411Q
  CfRegQ Prop49Exit Prop51G Prop51H

/-! ### The flow line meets every counterflow hull below the critical gap -/

section Hit

/-- **A real chart limit at `t₀` puts `η(t₀)` outside `ℍ ∖ R(K_s)`**: if `Ψ ∘ η` tends to a real point as `t ↑ t₀`,
then `η(t₀) ∉ ℍ ∖ R(K_s)` (at a point of `ℍ ∖ R(K_s)` the chart is continuous with values in `ℍ`). -/
theorem notMem_of_tendsto_revChart_real {η : ℝ → ℂ} (hη : IsProperArc η) {w : ℝ → ℝ} (hw : Continuous w)
    {s : ℝ} (hs : 0 ≤ s) {t₀ x₀ : ℝ} (ht₀ : 0 < t₀)
    (hlim : Tendsto (fun t => revChart w s (η t)) (𝓝[<] t₀) (𝓝 (x₀ : ℂ))) : η t₀ ∉ H \ cfHullQ w s := by
  intro hD
  have h1 : ContinuousAt η t₀ := hη.cont.continuousAt (Ici_mem_nhds ht₀)
  have h2 : ContinuousAt (revChart w s) (η t₀) :=
    (continuousOn_revChart hw hs).continuousAt ((isOpen_H_diff_negInv_fwdHull hw hs).mem_nhds hD)
  have h3 : Tendsto (fun t => revChart w s (η t)) (𝓝[<] t₀) (𝓝 (revChart w s (η t₀))) :=
    (ContinuousAt.comp (g := revChart w s) (f := η) h2 h1).tendsto.mono_left nhdsWithin_le_nhds
  have e := tendsto_nhds_unique h3 hlim
  have hH := revChart_mem_H hw hs hD
  rw [e] at hH
  exact lt_irrefl _ (show (0 : ℝ) < ((x₀ : ℝ) : ℂ).im from hH)

/-- **The flow line meets the counterflow hull `R(K_s)` at a finite positive time**, almost surely on the glued space
of `Cond44Ref.Prop51QStatement`, at every positive rational `s`, on the regime `G`. -/
def FwdHitQOn (G : ℝ → ℝ → ℝ → Prop) : Prop :=
  GluedQ.{u} G fun s η w => ∃ t₀ : ℝ, 0 < t₀ ∧ η t₀ ∉ H \ cfHullQ w s

/-- **Below the critical gap the flow line meets every counterflow hull** (`FwdHitQOn` on `θ₂ − θ₁ < πκ/(4 − κ)`):
PROVE-PROP51G's first exit (`ae_exitT`, Aux. lemma 22 for the image word of PROVE-CROSSCOND-THETA) is a hit of the
western side of `R(K_s)` at a finite time; read on the glued space as in `Prop51G.fwdFirstExitQOn_smallGap`. -/
theorem fwdHitQOn_smallGap (hreg : Prop51Q.CfLineRegularQStatement.{u}) :
    FwdHitQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂ := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
  have hχ := Sec4.chiC_pos hκ hκ4
  have hθχ : θ₁ * chiC κ ≤ θ₂ * chiC κ := mul_le_mul_of_nonneg_right h12.le hχ.le
  have hF := Theorem15.isOrderedForceWord_flowLine (Sec7.prop74Data a b) {0} 0
  have h44 := Sec7.Lemma71H.cond44_flowLine_prop74Data (θ := θ₂) hκ (a := a) (b := b) ha (by linarith)
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  have hfl₀ := hfl
  obtain ⟨h', 𝓕, W, VL, VR, B, htrans, hC, htr⟩ := hfl
  have hh' : h' = fun ω => Exist.flowField 0 (θ₂ * chiC κ) (h ω) :=
    funext fun ω => Lemma75Bridge.eq_flowField_of_isTranslateAddConst (htrans ω)
  set θ := θ₂ - θ₁ + π / 2 with hθdef
  have hXeq : (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = fun ω => cfFieldT κ θ (h' ω) := by
    funext ω
    rw [hh', cfField_flowField_eq_cfFieldT κ θ₁ θ₂]
  have hμ : glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
      ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)) =
      glueMeasure P k (fun ω => cfFieldT κ θ (h' ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) := by
    congr 1
  have hlaw' : P.map (fun ω => cfFieldT κ θ (h' ω)) = P₂.map h₂ := by rw [← hXeq]; exact hlaw
  have hθb : CfThetaBounds κ θ _ _ _ _ :=
    cfThetaBounds_prop74 (a := a) (b := b) (θ₁ := θ₁) (θ₂ := θ₂) hκ hb (by linarith)
  have hregG := hreg κ hκ hκ4 a b θ₁ hb (by linarith) P h hh P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  rw [hμ] at hregG ⊢
  have hNR : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h' ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      ∀ v : ℝ, 0 < v → histLine p.2 v ≠ 0 := by
    filter_upwards [hregG] with p hp
    exact hp.2.2.2.2.1
  have hexit := ae_exitT hκ hκ4 (by linarith) (charge_bound_of_not_isLargeGap hκ4 hG) hF h44 hθb hC hcf hlaw' k hk
    hNR hs
  have hseed : ∀ᵐ ω ∂P, seedLine ζ W ω = fun u : ℝ => η ω u.toNNReal := by
    filter_upwards [ae_seedLine_of_admissible hκ hκ4.le hF hadm hC.1, htr, hC.1.2.2.2.2] with ω hω ht hp
    obtain ⟨hζ, -, -⟩ := hω
    have e : (fun t => η ω t - ((0 : ℝ) : ℂ)) = η ω := by
      funext t
      simp
    rw [e] at ht
    exact seedLine_eq_of_isGeneratingTrace hζ hp.2.2.2.1 hp.1 ht
  have hseedG := ae_glue_fst (μ := P) k ((measurable_cfFieldT κ θ).comp hC.2.1) hseed
  have harc := ae_glue_fst (μ := P) k ((measurable_cfFieldT κ θ).comp hC.2.1)
    (ae_isProperArc_of_isFlowLine hκ hκ4.le hadm hfl₀)
  filter_upwards [hexit, hseedG, harc, hregG] with p hp hps hpa hpr
  obtain ⟨t₀, x₀, ht₀, -, -, -, hlim⟩ := hp
  rw [hps] at hlim
  exact ⟨t₀, ht₀, notMem_of_tendsto_revChart_real hpa hpr.2.1 (by exact_mod_cast hs.le) ht₀ hlim⟩

end Hit

/-! ### The counterflow hulls shrink to `∞`; the premise of (E2) is impossible (deterministic) -/

section Far

variable {w : ℝ → ℝ}

/-- **Small counterflow hulls are far away in the chart `Q`**: for a continuous driver with `w 0 = 0`, every bound
`M` is exceeded by the norm of every point of `R(K_{s′})` for some positive rational `s′ ≤ s`. -/
theorem exists_rat_cfHullQ_far (hw : Continuous w) (hw0 : w 0 = 0) {s : ℝ} (hs : 0 < s) (M : ℝ) :
    ∃ s' : ℚ, 0 < s' ∧ (s' : ℝ) ≤ s ∧ ∀ z ∈ cfHullQ w s', M < ‖z‖ := by
  set ε : ℝ := 1 / (|M| + 1) with hεdef
  have hM1 : 0 < |M| + 1 := by positivity
  have hε : 0 < ε := by positivity
  -- the driver is small near `0`
  obtain ⟨δ, hδ, hδw⟩ := Metric.continuousAt_iff.1 hw.continuousAt (ε / 4) (by positivity)
  set m : ℝ := min s (min (δ / 2) ((ε / 12) ^ 2)) with hmdef
  have hm : 0 < m := lt_min hs (lt_min (by positivity) (by positivity))
  obtain ⟨s', hs'0, hs'm⟩ := exists_rat_btwn hm
  have hs'pos : (0 : ℝ) < s' := hs'0
  refine ⟨s', by exact_mod_cast hs'pos, hs'm.le.trans (min_le_left _ _), fun z hz => ?_⟩
  obtain ⟨ζ', hζ', rfl⟩ := hz
  have hs'δ : (s' : ℝ) < δ := hs'm.trans_le ((min_le_right _ _).trans (min_le_left _ _)) |>.trans
    (by linarith)
  have hs'sq : (s' : ℝ) < (ε / 12) ^ 2 := hs'm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hbound : ∀ r ∈ Icc (0 : ℝ) s', |w r| ≤ ε / 4 := by
    intro r hr
    have hr' : dist r 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hr.1]
      exact hr.2.trans_lt hs'δ
    have := hδw hr'
    rw [Real.dist_eq, hw0, sub_zero] at this
    exact this.le
  have hball := QuantumZipper.CaraR.fwdHull_subset_closedBall hw hs'pos hbound hζ'
  rw [Metric.mem_closedBall, dist_zero_right] at hball
  have hsq : 3 * Real.sqrt s' < ε / 4 := by
    have h1 : Real.sqrt s' < ε / 12 := by
      rw [Real.sqrt_lt' (by positivity)]
      exact hs'sq
    linarith
  have hζH : ζ' ∈ H := (QuantumZipper.fwdHull_mono.2 _ hζ')
  have hζ0 : ζ' ≠ 0 := fun h0 => by
    rw [h0] at hζH
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hζH)
  have hnpos : 0 < ‖ζ'‖ := norm_pos_iff.2 hζ0
  have hsmall : ‖ζ'‖ ≤ ε / 2 := by linarith
  have hnorm : ‖negInv ζ'‖ = ‖ζ'‖⁻¹ := by simp [negInv]
  rw [hnorm]
  have hinv : 2 / ε ≤ ‖ζ'‖⁻¹ := by
    rw [inv_eq_one_div, div_le_div_iff₀ hε hnpos]
    linarith
  have h2ε : 2 / ε = 2 * (|M| + 1) := by
    rw [hεdef]
    field_simp
  have hMle : M ≤ |M| := le_abs_self M
  linarith

/-- **The premise of (E2) is impossible when the flow line meets every counterflow hull** (deterministic). If the
proper arc `η` meets `R(K_{s′})` at a positive time for every positive rational `s′`, then for `s > 0` and every `t`
it does not stay in `ℍ ∖ R(K_s)` at all times after `t`: for small `s′` the hull `R(K_{s′}) ⊆ R(K_s)` lies outside a
ball containing the compact prefix `η([0, t])`, so the hit of `R(K_{s′})` happens after `t`. -/
theorem not_forall_mem_of_hits {η : ℝ → ℂ} (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0)
    {s t : ℝ} (hs : 0 < s)
    (hhit : ∀ s' : ℚ, 0 < s' → ∃ t₀ : ℝ, 0 < t₀ ∧ η t₀ ∉ H \ cfHullQ w s') :
    ¬ ∀ v ∈ Ioi t, η v ∈ H \ cfHullQ w s := by
  intro hall
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
    (hη.cont.mono Icc_subset_Ici_self)
  obtain ⟨s', hs'0, hs's, hfar⟩ := exists_rat_cfHullQ_far hw hw0 hs M
  obtain ⟨t₀, ht₀, hnot⟩ := hhit s' hs'0
  have hK : η t₀ ∈ cfHullQ w s' := by
    by_contra hK
    exact hnot ⟨hη.mem_H t₀ ht₀, hK⟩
  have htt₀ : t < t₀ := by
    by_contra hle
    push Not at hle
    have := hM t₀ ⟨ht₀.le, hle⟩
    linarith [hfar _ hK]
  have hK' : η t₀ ∈ cfHullQ w s := image_mono (fwdHull_mono hs's) hK
  exact (hall t₀ htt₀).2 hK'

end Far

/-! ### The residual reduced to (E1); the wiring -/

section Residual

/-- **The post-contact residual on the eastern side proper** ((E1) of `Prop51H.PostContactEastResidual` alone): if
`η` has met `R(K_s)` in `(0, t]` and is in `ℍ ∖ R(K_s)` at `t`, its excursion running at `t` does not end at a finite
time on the eastern side proper of the counterflow hull. -/
def PostContactEastSideResidual (w : ℝ → ℝ) (s t : ℝ) (η : ℝ → ℂ) : Prop :=
  (∃ v ∈ Ioc 0 t, η v ∉ H \ cfHullQ w s) → (0 < t → η t ∈ H \ cfHullQ w s) →
    ∀ u₀, t < u₀ → (∀ v ∈ Ioo t u₀, η v ∈ H \ cfHullQ w s) → ¬ HitsEastSideAlong w s η (𝓝[Ioo t u₀] u₀)

/-- **(E1) on a regime of angles**, almost surely on the glued space at every positive rational counterflow time `s`
and restart time `t` (the named input that replaces `Prop51H.FwdPostContactEastQOn` below the critical gap). -/
def FwdPostContactEastSideQOn (G : ℝ → ℝ → ℝ → Prop) : Prop :=
  GluedQ.{u} G fun s η w => ∀ t : ℚ, 0 < t → PostContactEastSideResidual w s t η

/-- The residual from (E1) when the premise of (E2) fails. -/
theorem postContactEastResidual_of_side {w : ℝ → ℝ} {s t : ℝ} {η : ℝ → ℂ}
    (hside : PostContactEastSideResidual w s t η) (hnot : ¬ ∀ v ∈ Ioi t, η v ∈ H \ cfHullQ w s) :
    PostContactEastResidual w s t η :=
  fun hc hD => ⟨hside hc hD, fun hall => absurd hall hnot⟩

/-- **No last contact with the counterflow hull** on the regime `G`: almost surely on the glued space, at every positive
rational `s`, the flow line meets `R(K_s)` after every time `t`. -/
def FwdNoLastContactQOn (G : ℝ → ℝ → ℝ → Prop) : Prop :=
  GluedQ.{u} G fun s η w => ∀ t : ℝ, ∃ v : ℝ, t < v ∧ η v ∉ H \ cfHullQ w s

/-- **Below the critical gap the flow line has no last contact with `R(K_s)`** (`fwdHitQOn_smallGap` at every
positive rational time and `not_forall_mem_of_hits`): it bounces off the counterflow at all scales up to `∞`, so every
excursion of `η` in `ℍ ∖ R(K_s)` after a positive time is bounded. -/
theorem fwdNoLastContactQOn_smallGap (hreg : Prop51Q.CfLineRegularQStatement.{u}) :
    FwdNoLastContactQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂ := by
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
  have hH := fwdHitQOn_smallGap hreg κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  have hHall : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) hXm),
      ∀ s' : ℚ, 0 < s' → ∃ t₀ : ℝ, 0 < t₀ ∧
        (fun u : ℝ => η p.1 u.toNNReal) t₀ ∉ H \ cfHullQ (Prop411Q.cfDrv p.2) s' := by
    rw [ae_all_iff]
    intro s'
    by_cases hs' : 0 < s'
    · filter_upwards [hH s' hs'] with p hp using fun _ => hp
    · exact Eventually.of_forall fun p h => absurd h hs'
  filter_upwards [harc, hregG, hHall] with p hpa hpr hph t
  obtain ⟨-, hwc, hw0, -, -, -⟩ := hpr
  by_contra hno
  push Not at hno
  exact not_forall_mem_of_hits hpa hwc hw0 (by exact_mod_cast hs) hph fun v hv => hno v hv

/-- **`Prop51H.FwdPostContactEastQOn` below the critical gap from (E1) alone**: the premise of (E2) is excluded by
`fwdNoLastContactQOn_smallGap`. -/
theorem fwdPostContactEastQOn_of_side (hreg : Prop51Q.CfLineRegularQStatement.{u})
    (hside : FwdPostContactEastSideQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) :
    FwdPostContactEastQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂ :=
  (GluedQ.and hside (fwdNoLastContactQOn_smallGap hreg)).mono fun _ _ _ hp t ht =>
    postContactEastResidual_of_side (hp.1 t ht) fun hall => by
      obtain ⟨v, hv, hnot⟩ := hp.2 t
      exact hnot (hall v hv)

/-- **`Cond44Ref.Prop51QStatement` from Zhan's Part A inputs at `16/κ`, the no-wrap topology and (E1)** (below the
critical gap; at and above it, `Prop51H.fwdNoContactQStatement`). -/
theorem prop51QStatement_of_partA_of_eastSide (hA : PartAInputsSixteenDiv) (htopo : FwdNoWrapQStatement)
    (hside : FwdPostContactEastSideQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) : Prop51QStatement.{u} :=
  prop51QStatement_of_partA_of_east hA htopo
    (fwdPostContactEastQOn_of_side (CfLineRegQ.cfLineRegularQStatement_of_partA hA) hside)

/-- **Theorem 1.2's input `CfAvoidLeftQ.CfFirstContactQStatement` from Zhan's Part A inputs, the no-wrap topology and
(E1).** -/
theorem cfFirstContactQStatement_of_partA_of_eastSide (hA : PartAInputsSixteenDiv) (htopo : FwdNoWrapQStatement)
    (hside : FwdPostContactEastSideQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) :
    CfAvoidLeftQ.CfFirstContactQStatement.{u} :=
  cfFirstContactQStatement_of_partA_of_east hA htopo
    (fwdPostContactEastQOn_of_side (CfLineRegQ.cfLineRegularQStatement_of_partA hA) hside)

end Residual

end InteractingSLE.Sec5.Prop51I
