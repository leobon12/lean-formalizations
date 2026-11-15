/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G15LandCore
import InteractingSLE.Spec.Restart.FCK2TermSource
import InteractingSLE.Spec.Restart.FCK2BdryVisit
import InteractingSLE.Foundations.Loewner.Reflect

/-!
# Lemma G15: the contact case of the endpoint step of S6 and SB1

Packet PROVE-T14-G15. This file proves **`terminalContactCompletionStatement`**: PROVE-T14-SBFIN's
`SB.Fin.TerminalContactCompletionStatement` (the case of the endpoint step in which a finite terminal endpoint of one
prefix lies on the other prefix), with no input. Consequently the positive-lifetime endpoint step
`TerminalEndpointPosStatement` holds outright, and Lemmas SB1 and S6 follow from W5 and their middle exclusions alone
(`sb1Statement_of_middle`, `s6Statement_of_middle`).

Source (supplement pp. 508–509, Lemma G15 and its proof): in the right-hand case (`q > max(z₁, z₂)`) "the entire `α`
prefix through `q` is contained in the filled hull of the `β` prefix through `q`. Only `β` can have a nonempty
continuation [...] Complete `α` by following this same `β` tail from `q`"; the left-hand case interchanges the roles.

* `hasOrderedProperCompletions_of_leftContact`: the left-hand case of `G15LandCore`'s
  `hasOrderedProperCompletions_of_rightContact`, by the reflection `z ↦ −z̄` (which exchanges the two paths);
* the weight step ("If `β` terminates, `r_β ≤ −2` implies `r_α ≤ −2`, so `α` also terminates. Consequently any
  nonempty actual continuation belongs to `β`"): a finite positive lifetime ends at a real point with the bad incident
  height (`FCPlumb.ae_original_terminal_bad_incident`), every real visit before the lifetime has the good one
  (`FCPlumb.ae_live_real_incident_bounds`), and the heights of the two angles differ by `(θ₂ − θ₁)χ > 0`. So when the
  outer path is the one that terminates at `q`, the inner path's visit of `q` is its own terminal endpoint, and the
  contact is again a cut of the inner path.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.G15Land

open Supp9B

/-! ### The left-hand case by reflection -/

section Left

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ}

theorem reflectCurve_eq_reflectC (γ : ℝ≥0 → ℂ) : reflectCurve γ = fun t => LP.reflectC (γ t) := rfl

theorem reflectCurve_apply_ofReal (γ : ℝ≥0 → ℂ) {t : ℝ≥0} {Q : ℝ} (h : γ t = Q) :
    reflectCurve γ t = ((-Q : ℝ) : ℂ) := by
  show Supp9B.refl (γ t) = _
  rw [h]
  apply Complex.ext <;> simp [Supp9B.refl]

/-- **Lemma G15's proper witnesses, left-hand case** (supplement p. 509: "For `q < min(z₁, z₂)`, close the `α` prefix
on its filled left side and repeat the argument"): if the cut `β(c)` of `β` is a real point `q < x₂` that `α` visits
at a time `x ≤ a`, then `α([0, a])` and `β([0, c])` have ordered proper completions. This is
`hasOrderedProperCompletions_of_rightContact` for the reflected pair `(−β̄, −ᾱ)`. -/
theorem hasOrderedProperCompletions_of_leftContact (hpα : Restart.IsPathGood α ζ₁ x₁)
    (hpβ : Restart.IsPathGood β ζ₂ x₂) (hx : x₂ ≤ x₁)
    (hW5 : ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ → (c : ℝ≥0∞) < ζ₂ → HasOrderedProperCompletions α a β c)
    {a c x : ℝ≥0} {Q : ℝ} (ha : (a : ℝ≥0∞) ≤ ζ₁) (hc : (c : ℝ≥0∞) ≤ ζ₂) (hxa : x ≤ a)
    {Sα Sc : ℝ≥0 → ℂ} (hSα : IsSlitCompletion α a Sα) (hSc : IsSlitCompletion β c Sc)
    (hβc : β c = Q) (hαx : α x = Q) (hQ : Q < x₂) :
    HasOrderedProperCompletions α a β c := by
  have hα0 : α 0 = x₁ := Sec7.IsPathGood.zero hpα
  have hβ0 : β 0 = x₂ := Sec7.IsPathGood.zero hpβ
  have hα0im : (α 0).im = 0 := by rw [hα0]; simp
  have hβ0im : (β 0).im = 0 := by rw [hβ0]; simp
  have hseed : (β 0).re ≤ (α 0).re := by rw [hα0, hβ0]; simpa using hx
  have hpα' : Restart.IsPathGood (reflectCurve β) ζ₂ (-x₂) := by
    rw [reflectCurve_eq_reflectC]; exact Restart.IsPathGood.reflect hpβ
  have hpβ' : Restart.IsPathGood (reflectCurve α) ζ₁ (-x₁) := by
    rw [reflectCurve_eq_reflectC]; exact Restart.IsPathGood.reflect hpα
  have hW5' : ∀ c' a' : ℝ≥0, (c' : ℝ≥0∞) < ζ₂ → (a' : ℝ≥0∞) < ζ₁ →
      HasOrderedProperCompletions (reflectCurve β) c' (reflectCurve α) a' := fun c' a' hc' ha' =>
    hasOrderedProperCompletions_reflect (hW5 a' c' ha' hc') hα0im hβ0im hseed
  have h := hasOrderedProperCompletions_of_rightContact hpα' hpβ' (neg_le_neg hx) hW5' hc ha hxa
    (isSlitCompletion_reflectCurve hSc) (isSlitCompletion_reflectCurve hSα)
    (reflectCurve_apply_ofReal β hβc) (reflectCurve_apply_ofReal α hαx) (neg_lt_neg hQ)
  have h' := hasOrderedProperCompletions_reflect h (by simp [reflectCurve, hβ0im])
    (by simp [reflectCurve, hα0im]) (by simp [reflectCurve, hseed])
  simpa using h'

end Left

/-! ### The weight step -/

/-- **Only the outer path can continue past an exterior real terminal meeting** (supplement p. 509: "If `β`
terminates, `r_β ≤ −2` implies `r_α ≤ −2`, so `α` also terminates"; reflected for `q < min(z₁, z₂)`). For `θ₁ < θ₂`:
if one flow line ends at a real point `q` with the bad incident height of angle `θ₂` on its right (`b(q⁺) + θ₂χ ≤ −λ`),
then a flow line of angle `θ₁` cannot visit `q` from its right before its lifetime, and symmetrically on the left. -/
theorem right_height_contra {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂) {v : ℝ}
    (hbad : v + θ₂ * chiC κ ≤ -sleLambda κ) (hgood : -sleLambda κ < v + θ₁ * chiC κ) : False := by
  have := mul_lt_mul_of_pos_right hθ (Sec4.chiC_pos hκ hκ4)
  linarith

theorem left_height_contra {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂) {v : ℝ}
    (hbad : sleLambda κ ≤ v + θ₁ * chiC κ) (hgood : v + θ₂ * chiC κ < sleLambda κ) : False := by
  have := mul_lt_mul_of_pos_right hθ (Sec4.chiC_pos hκ hκ4)
  linarith

/-! ### The contact case of the endpoint step -/

/-- **Lemma G15 / the contact case of the endpoint step of S6 and SB1** (`SB.Fin.TerminalContactCompletionStatement`,
PROVE-T14-SBFIN), proved: almost surely, if every pair of strict prefixes has W5's ordered completions and every
terminal contact is an exterior original-real point, then every pair of available prefixes one of whose finite
terminal endpoints lies on the other prefix has ordered proper completions.

Proof. Let the contact point be `q` (real, outside `[x₂, x₁]`). If `q > x₁` and the cut `α(a)` is `q`, or `q < x₂` and
the cut `β(c)` is `q`, the deterministic G15 (`hasOrderedProperCompletions_of_rightContact`,
`hasOrderedProperCompletions_of_leftContact`) applies. In the two remaining configurations the outer path terminates
at `q` (`β` with `q > x₁`, `α` with `q < x₂`) while the inner path would visit `q` strictly before its own lifetime;
the incident heights exclude this (`ae_original_terminal_bad_incident`, `ae_live_real_incident_bounds`). -/
theorem terminalContactCompletionStatement : Fin.TerminalContactCompletionStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ hp₁ hp₂
  filter_upwards [Restart.ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
    Restart.ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂,
    End.ae_forall_exists_slitCompletion_of_isFlowLine hκ hκ4 hη₁,
    End.ae_forall_exists_slitCompletion_of_isFlowLine hκ hκ4 hη₂,
    Restart.FCPlumb.ae_original_terminal_bad_incident hκ hb hη₁,
    Restart.FCPlumb.ae_original_terminal_bad_incident hκ hb hη₂,
    Restart.FCPlumb.ae_live_real_incident_bounds hκ hκ4 hb hh hη₁,
    Restart.FCPlumb.ae_live_real_incident_bounds hκ hκ4 hb hh hη₂]
    with ω hg₁ hg₂ hs₁ hs₂ hbad₁ hbad₂ hlive₁ hlive₂ hstrict hext a c ha hc hcon
  have hα0 : η₁ ω 0 = x₁ := Sec7.IsPathGood.zero hg₁
  have hβ0 : η₂ ω 0 = x₂ := Sec7.IsPathGood.zero hg₂
  obtain ⟨Sα, hSα⟩ := hs₁ a ha
  obtain ⟨Sc, hSc⟩ := hs₂ c hc
  rcases hcon with ⟨haζ, y, hy, hyq⟩ | ⟨hcζ, x, hx', hxq⟩
  · -- `α` is cut at its terminal endpoint `q = α(a) = β(y)`, `y ≤ c`
    have hyζ : (y : ℝ≥0∞) ≤ ζ₂ ω := (ENNReal.coe_le_coe.2 hy.2).trans hc
    obtain ⟨Q, hQ, hQs⟩ := hext a y ha hyζ (Or.inl haζ) hyq.symm
    rcases hQs with hQl | hQr
    · -- `q < x₂`: the inner `β` also ends at `q`
      rcases hy.2.lt_or_eq with hyc | rfl
      · exfalso
        have hyζ' : (y : ℝ≥0∞) < ζ₂ ω := (ENNReal.coe_lt_coe.2 hyc).trans_le hc
        have ha0 : 0 < a := by
          refine pos_iff_ne_zero.2 fun h0 => ?_
          rw [h0, hα0] at hQ
          exact (hQl.trans_le hx).ne (Complex.ofReal_injective hQ).symm
        obtain ⟨-, hbad⟩ := hbad₁ a ha0 haζ
        rw [hQ, Complex.ofReal_re] at hbad
        have hgood := (hlive₂ y hyζ' Q (hyq.trans hQ)).1 hQl.le
        rcases hbad with ⟨-, hb'⟩ | ⟨hle, -⟩
        · exact left_height_contra hκ hκ4 hθ hb' hgood
        · exact absurd (hQl.trans_le hx) (not_lt.2 hle)
      · exact hasOrderedProperCompletions_of_leftContact hg₁ hg₂ hx hstrict ha hc le_rfl hSα hSc
          (hyq.trans hQ) hQ hQl
    · exact hasOrderedProperCompletions_of_rightContact hg₁ hg₂ hx hstrict ha hc hy.2 hSα hSc hQ
        (hyq.trans hQ) hQr
  · -- `β` is cut at its terminal endpoint `q = β(c) = α(x)`, `x ≤ a`
    have hxζ : (x : ℝ≥0∞) ≤ ζ₁ ω := (ENNReal.coe_le_coe.2 hx'.2).trans ha
    obtain ⟨Q, hQ, hQs⟩ := hext x c hxζ hc (Or.inr hcζ) hxq
    rcases hQs with hQl | hQr
    · exact hasOrderedProperCompletions_of_leftContact hg₁ hg₂ hx hstrict ha hc hx'.2 hSα hSc
        (hxq.symm.trans hQ) hQ hQl
    · -- `q > x₁`: the inner `α` also ends at `q`
      rcases hx'.2.lt_or_eq with hxa | rfl
      · exfalso
        have hxζ' : (x : ℝ≥0∞) < ζ₁ ω := (ENNReal.coe_lt_coe.2 hxa).trans_le ha
        have hc0 : 0 < c := by
          refine pos_iff_ne_zero.2 fun h0 => ?_
          rw [h0, hβ0] at hxq
          rw [hxq] at hQ
          exact (hx.trans_lt hQr).ne (Complex.ofReal_injective hQ)
        obtain ⟨-, hbad⟩ := hbad₂ c hc0 hcζ
        rw [← hxq, hQ, Complex.ofReal_re] at hbad
        have hgood := (hlive₁ x hxζ' Q hQ).2 hQr.le
        rcases hbad with ⟨hle, -⟩ | ⟨-, hb'⟩
        · exact absurd (hx.trans_lt hQr) (not_lt.2 hle)
        · exact right_height_contra hκ hκ4 hθ hb' hgood
      · exact hasOrderedProperCompletions_of_rightContact hg₁ hg₂ hx hstrict ha hc le_rfl hSα hSc hQ
          (hxq.symm.trans hQ) hQr

/-- **The positive-lifetime endpoint step of S6 and SB1**, unconditional. -/
theorem terminalEndpointPosStatement : Fin.TerminalEndpointPosStatement.{u} :=
  Fin.terminalEndpointPosStatement_of_contact terminalContactCompletionStatement

/-- **Lemma SB1** from W5 and its middle exclusion (the endpoint step is now proved). -/
theorem sb1Statement_of_middle (hW5 : Theorem15.W5Statement.{u}) (hM : SB1MiddleStatement.{u}) :
    SB1Statement.{u} :=
  Fin.sb1Statement_of_inputs_pos hW5 hM terminalEndpointPosStatement

/-- **Lemma S6** from W5 and its middle exclusion (the endpoint step is now proved). -/
theorem s6Statement_of_middle (hW5 : Theorem15.W5Statement.{u}) (hM : S6MiddleStatement.{u}) :
    S6Statement.{u} :=
  Fin.s6Statement_of_inputs_pos hW5 hM terminalEndpointPosStatement

end InteractingSLE.Theorem14.SB.G15Land
