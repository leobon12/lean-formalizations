/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5LiftLattice
import InteractingSLE.Spec.Sec7.SideC5Relative
import InteractingSLE.Spec.Sec7.Aux29CorSide
import InteractingSLE.Spec.Supplement.BHMeanReal
import InteractingSLE.Spec.Sec5.MarkovFlow

/-!
# Lemma R.5's common phase: ambient lifts, references and the current chart

Packet PROVE-R5-LIFT. The lift differences of R.5's cover compare the current relative chart with the ambient
Loewner chart of the counterflow at a rational original time `s` (`R5Same.ambLift`). This file supplies the Loewner
and chart steps of the common-phase argument:

* **`tendsto_im_logDerivFwd_sub_of_notMem_closure`** (time compatibility): the canonical ambient lifts at two times
  `s ≤ s'` agree in the limit along an approach whose `f_s`-image tends to a real point off the closed hull of the
  increment `[s, s']` (`Markov.logDerivFwd_add` and (CA2) `BHMean.tendsto_im_logDerivFwd_of_notMem_closure`);
* **`tendsto_lift_sub_trans`** (chain): a lift difference current → old with limit `d₁` and an old-chart lift
  difference old → `A` with limit `d₂` at the transition point give the limit `d₁ + d₂` of current → `A`;
* **`tendsto_relChart_lift_sub_of_old`**: for the relative charts at capacities `p ≤ q` on a surviving collar
  (`PocketStopSide.tendsto_relChart_lift_sub_zero`, the own-stage zero lift difference), the current chart inherits
  the old chart's limit against any lift `A`;
* **`exists_int_forall_tendsto_relChart_ambLift`**: if the ambient transition `f_s ∘ old⁻¹` of an earlier relative
  chart reflects with positive derivative at every point of a preconnected real set `J` (for instance the old chart's
  exposed interval, which contains its driver when the reference is taken at an interior visit), then one integer
  `n` gives the limit `2πn` of `current lift − arg f_s′` at every current coordinate whose collar point lies in `J`.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H fwdHull fwdMap logDerivFwd)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Lift

open PocketStop PocketTraversal Lemma71C PocketStopSide

/-! ### Time compatibility of the ambient lifts -/

/-- **Time compatibility of the canonical ambient lifts.** For `s ≤ s'`, along an approach `F` staying off the hull
at `s'` whose `f_s`-image tends to a real point `x` off the closure of the increment hull (the hull of the restarted
driver `r ↦ W (s + r) − W s` at time `s' − s`), `Im log f_{s'}′ − Im log f_s′ → 0`. -/
theorem tendsto_im_logDerivFwd_sub_of_notMem_closure {W : ℝ → ℝ} (hW : Continuous W) {s s' : ℝ} (hs : 0 ≤ s)
    (hss' : s ≤ s') {α : Type*} {l : Filter α} {F : α → ℂ} (hF : ∀ᶠ a in l, F a ∈ H \ fwdHull W s') {x : ℝ}
    (hFx : Tendsto (fun a => fwdMap W s (F a)) l (𝓝 (x : ℂ)))
    (hx : (x : ℂ) ∉ closure (fwdHull (fun r => W (s + r) - W s) (s' - s))) :
    Tendsto (fun a => (logDerivFwd W s' (F a)).im - (logDerivFwd W s (F a)).im) l (𝓝 0) := by
  have hd : 0 ≤ s' - s := sub_nonneg.2 hss'
  have hWr : Continuous fun r => W (s + r) - W s :=
    (hW.comp (continuous_const.add continuous_id)).sub continuous_const
  have hWr0 : (fun r => W (s + r) - W s) 0 = 0 := by simp
  have hkey : ∀ᶠ a in l, (logDerivFwd (fun r => W (s + r) - W s) (s' - s) (fwdMap W s (F a))).im =
      (logDerivFwd W s' (F a)).im - (logDerivFwd W s (F a)).im := by
    filter_upwards [hF] with a ha
    have ha' : F a ∈ H \ fwdHull W (s + (s' - s)) := by rwa [add_sub_cancel]
    have h := Sec5.Markov.logDerivFwd_add hW hs hd ha'
    rw [add_sub_cancel] at h
    rw [h, Complex.add_im]
    ring
  have hFH : Tendsto (fun a => fwdMap W s (F a)) l (𝓝[H] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hFx, hF.mono fun a ha => ?_⟩
    exact QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs (Ito.mem_diff_fwdHull_of_le ha hss')
  exact ((Supp8.BHMean.tendsto_im_logDerivFwd_of_notMem_closure hWr hWr0 hd hx).comp hFH).congr' hkey

/-! ### Chains of lift differences -/

/-- **Chain of lift differences**: if the current inverse stays in the old chart's domain, the transition
`old ∘ current⁻¹` tends to `x` within `ℍ`, the lift difference current → old tends to `d₁`, and the old chart's lift
difference against `A` (read through the old inverse) tends to `d₂` at `x`, then the lift difference current → `A`
tends to `d₁ + d₂`. -/
theorem tendsto_lift_sub_trans {cur old : Chart} (hold : old.IsConformal) {A : ℂ → ℝ} {ξ x : ℂ} {d₁ d₂ : ℝ}
    (hdom : ∀ᶠ y in 𝓝[H] ξ, cur.2.1 y ∈ old.dom)
    (htr : Tendsto (fun y => old.1 (cur.2.1 y)) (𝓝[H] ξ) (𝓝 x))
    (h₁ : Tendsto (fun y => cur.2.2 (cur.2.1 y) - old.2.2 (cur.2.1 y)) (𝓝[H] ξ) (𝓝 d₁))
    (h₂ : Tendsto (fun w => old.2.2 (old.2.1 w) - A (old.2.1 w)) (𝓝[H] x) (𝓝 d₂)) :
    Tendsto (fun y => cur.2.2 (cur.2.1 y) - A (cur.2.1 y)) (𝓝[H] ξ) (𝓝 (d₁ + d₂)) := by
  have htr' : Tendsto (fun y => old.1 (cur.2.1 y)) (𝓝[H] ξ) (𝓝[H] x) :=
    tendsto_nhdsWithin_iff.2 ⟨htr, hdom.mono fun y hy => hold.fwd_mem hy⟩
  have h₃ := h₂.comp htr'
  refine (h₁.add h₃).congr' ?_
  filter_upwards [hdom] with y hy
  simp only [Function.comp_apply, hold.inv_fwd hy]
  ring

variable {Ω : Type*} {c : Ω → Chart} {γ : Ω → ℝ → ℂ} {ω : Ω}

/-- **The current relative chart inherits an earlier relative chart's lift limits**: on a surviving collar of the
relative chart at capacity `p ≤ q`, any limit `d` of the old lift difference against `A` at the collar point is the
limit of the current lift difference against `A` at `ξ` (the own-stage lift difference vanishes there). -/
theorem tendsto_relChart_lift_sub_of_old {p q : ℝ≥0} (hc : (c ω).IsConformal) (hγ : IsDrivenCurve (γ ω))
    (hq : (q : ℝ≥0∞) < capLife (γ ω)) (hpq : p ≤ q) {ξ x r : ℝ} (hr : 0 < r)
    (hCollar : (relChart c γ p ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆ ((relChart c γ q ω).dom : Set ℂ))
    (hTransition : Tendsto (fun z => (relChart c γ p ω).1 ((relChart c γ q ω).2.1 z)) (𝓝[H] (ξ : ℂ))
      (𝓝 (x : ℂ)))
    {A : ℂ → ℝ} {d : ℝ}
    (hold : Tendsto (fun w => (relChart c γ p ω).2.2 ((relChart c γ p ω).2.1 w) - A ((relChart c γ p ω).2.1 w))
      (𝓝[H] (x : ℂ)) (𝓝 d)) :
    Tendsto (fun y => (relChart c γ q ω).2.2 ((relChart c γ q ω).2.1 y) - A ((relChart c γ q ω).2.1 y))
      (𝓝[H] (ξ : ℂ)) (𝓝 d) := by
  have hpq' : (p : ℝ≥0∞) ≤ q := ENNReal.coe_le_coe.2 hpq
  have hp : (p : ℝ≥0∞) < capLife (γ ω) := lt_of_le_of_lt hpq' hq
  have hold' : (relChart c γ p ω).IsConformal := isConformal_relChart_of_driven hγ hp hc
  have hcur : (relChart c γ q ω).IsConformal := isConformal_relChart_of_driven hγ hq hc
  have hsub := relChart_dom_antitone hc hγ hq hpq
  have hdom : ∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c γ q ω).2.1 y ∈ (relChart c γ p ω).dom :=
    eventually_nhdsWithin_of_forall fun y hy => hsub (hcur.inv_mem_dom hy)
  have h₁ := tendsto_relChart_lift_sub_zero hc hγ hq hpq hr hCollar hTransition
  have h := tendsto_lift_sub_trans (cur := relChart c γ q ω) (old := relChart c γ p ω) (A := A)
    (ξ := (ξ : ℂ)) (x := (x : ℂ)) (d₁ := 0) (d₂ := d) hold' hdom hTransition h₁ hold
  rw [zero_add] at h
  exact h

/-- **The ambient lift limit of the current chart through one reference** (common phase on one connected set). Let
`old` be the relative chart at capacity `p ≤ q`, whose domain avoids the ambient hull at time `s`, and suppose the
ambient transition `f_s ∘ old⁻¹` reflects with positive derivative at every point of a preconnected real set `J`.
Then there is one integer `n` such that, at every current real coordinate `ξ` with a surviving collar of `old` whose
collar point lies in `J`, `current lift − Im log f_s′` read through the current inverse tends to `2πn`. -/
theorem exists_int_forall_tendsto_relChart_ambLift {p q : ℝ≥0} (hc : (c ω).IsConformal)
    (hγ : IsDrivenCurve (γ ω)) (hq : (q : ℝ≥0∞) < capLife (γ ω)) (hpq : p ≤ q) {ℓ : ℂ → ℂ}
    (hℓ : IsDerivLog (c ω).1 ℓ (c ω).dom) (hlift : ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ z).im)
    {W : ℝ → ℝ} (hW : Continuous W) {s : ℝ} (hs : 0 ≤ s)
    (hK : ((relChart c γ p ω).dom : Set ℂ) ⊆ H \ fwdHull W s) {J : Set ℝ} (hJ : IsPreconnected J)
    (hrefl : ∀ x ∈ J, ∃ b : ℝ, 0 < b ∧
      Tendsto (deriv fun y => fwdMap W s ((relChart c γ p ω).2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (b : ℂ))) :
    ∃ n : ℤ, ∀ (ξ x r : ℝ), x ∈ J → 0 < r →
      (relChart c γ p ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆ ((relChart c γ q ω).dom : Set ℂ) →
      Tendsto (fun z => (relChart c γ p ω).1 ((relChart c γ q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) →
      Tendsto (fun y => (relChart c γ q ω).2.2 ((relChart c γ q ω).2.1 y) -
          (logDerivFwd W s ((relChart c γ q ω).2.1 y)).im) (𝓝[H] (ξ : ℂ)) (𝓝 (2 * Real.pi * n)) := by
  have hpq' : (p : ℝ≥0∞) ≤ q := ENNReal.coe_le_coe.2 hpq
  have hp : (p : ℝ≥0∞) < capLife (γ ω) := lt_of_le_of_lt hpq' hq
  have hold : (relChart c γ p ω).IsConformal := isConformal_relChart_of_driven hγ hp hc
  obtain ⟨Lc, hLc, hliftc⟩ := Aux29Cor.exists_isDerivLog_relChart hγ hp hc hℓ hlift
  have hLg := isDerivLog_fwdMap hW hs
  obtain ⟨n, hn⟩ := exists_int_forall_tendsto_lift_sub (cur := relChart c γ p ω) (g := fwdMap W s)
      (Lg := logDerivFwd W s) hold hLc hliftc hLg hJ fun x hx => by
    obtain ⟨b, hb, hder⟩ := hrefl x hx
    exact ⟨1, one_pos, fun y hy => hK (hold.inv_mem_dom hy.1), b, hb, hder⟩
  exact ⟨n, fun ξ x r hx hr hCollar hTransition =>
    tendsto_relChart_lift_sub_of_old (A := fun z => (logDerivFwd W s z).im) hc hγ hq hpq hr hCollar
      hTransition (hn x hx)⟩

end InteractingSLE.Sec7.R5Lift
