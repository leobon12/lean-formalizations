/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.Statements
import InteractingSLE.Spec.RealContact.CrossChart
import InteractingSLE.Spec.AuditFix.BoundaryContactInputs

/-!
# Theorem 1.5 (iii), critical angles, at every contact, from clause (i) (ruling R124 (c))

Packet PROVE-RC-CROSS. `criticalCrossingContact_of_ordered`: clause (iii) at every contact
(`CriticalCrossingContactStatement`) from clause (i) at every contact (`CriticalOrderedContactStatement`, universe
`0`, the canonical space of the restart carrier).

Route (specification supplement p. 544, "Critical exclusion after a crossing", extended to every contact):

1. **The restart carrier with the active prime end** (closed, `AuditFix.ContactInputs.firstContactRestartLim`): at the
   first contact with two nonempty continuations, the continuations are, under the conditional kernel `K c` at almost
   every datum `c`, the angle-`θ₁` and angle-`θ₂` flow lines from the common seed `0` of the conditional field.
2. **Clause (i) per datum in the chart**, for the pair (lower angle `θ₂` first, higher angle `θ₁` second, both from `0`,
   `θ₁ − θ₂ ≥ πκ/(4 − κ)`): `K c`-almost surely every chart contact is `(0, 0)` or terminal for both; in particular
   it lies in the measurable chart event `EndpointContactsOnly` (`measurableSet_endpointContactsOnly`), which
   integrates back (`Restart.ae_mem_of_compProd_eq`).
3. **Transfer** (`isFirstContact_or_terminal_of_chart`): Lemma 7.7 (closed, `ContactInputs.lemma77`) gives the first
   contact of any contact with confinement; Aux. lemma 25 gives injectivity; the chart limits and capacity clocks of
   `Theorem15D5.IsChartContinuationLim` map later physical contacts (real points and terminal times included) to chart
   contacts.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace RealContact

open AuditFix.ContactInputs

/-- **Theorem 1.5 (iii), critical angles, at every contact, from clause (i).** For `x₂ < x₁`, `θ₂ < θ₁ < θ₂ + π`
and `θ₁ − θ₂ ≥ πκ/(4 − κ)`: almost surely every common point `η₁ s = η₂ t` of the closed available paths is the first
contact or terminal for both paths. Clause (i) is used only per datum, for the common-seed conditional pair in the
first-contact restart chart (universe `0`). -/
theorem criticalCrossingContact_of_ordered (hO : CriticalOrderedContactStatement.{0}) :
    CriticalCrossingContactStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ hθπ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ hcrit
  obtain ⟨S, mS, H, γ₁, γ₂, U₁, U₂, M, β, X, K, hcoord, hM, hβ, hX, hK, hlaw, hcond, hpath⟩ :=
    firstContactRestartLim κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθπ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  have hKE : ∀ᵐ c ∂(P.restrict M).map β, ∀ᵐ s ∂(K c),
      s ∈ {s | EndpointContactsOnly (γ₂ s) (U₂ s) (γ₁ s) (U₁ s)} := by
    filter_upwards [hcond] with c hc
    obtain ⟨hgff, hf₁, hf₂⟩ := hc
    filter_upwards [hO hκ hκ4 c.fn c.jumps c.isPiecewiseConstantBoundaryData (le_refl (0 : ℝ)) hθ hgff hf₂ hf₁
      hcrit] with s hs
    intro u v hu hv huv
    rcases hs u v hu hv huv with ⟨-, rfl, rfl⟩ | ⟨h1, h2⟩
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · exact ⟨Or.inr h1, Or.inr h2⟩
  have hae := Restart.ae_mem_of_compProd_eq hM hβ hX hlaw
    (measurableSet_endpointContactsOnly (isRestartCoordinates_swap hcoord)) hKE
  obtain ⟨-, -, -, -, -, hγc₁, hγc₂⟩ := hcoord
  filter_upwards [hae, hpath,
    lemma77 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθπ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂,
    Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
    Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂,
    Sec7.ae_continuousOn_of_isFlowLine hη₁, Sec7.ae_continuousOn_of_isFlowLine hη₂]
    with ω hωE hωp h7 hi₁ hi₂ hc₁ hc₂
  intro s t hs ht hst
  obtain ⟨s₀, t₀, h₀, hconf₁, hconf₂⟩ := h7 ⟨s, t, hs, ht, hst⟩
  refine isFirstContact_or_terminal_of_chart hc₁ hc₂ hi₁ hi₂ h₀ hconf₁ hconf₂ (fun hs₀ ht₀ => ?_) hs ht hst
  obtain ⟨hωM, φ, -, -, c₁, c₂, -, -, -, -, -, -, -, hm₁, him₁, hm₂, him₂, -, -, hl₁, hl₂⟩ :=
    hωp s₀ t₀ h₀ hs₀ ht₀
  exact ⟨φ, γ₁ (X ω), γ₂ (X ω), U₁ (X ω), U₂ (X ω), c₁, c₂, hγc₁ (X ω), hγc₂ (X ω), hm₁, him₁, hm₂, him₂,
    hl₁, hl₂, hωE hωM⟩

end RealContact

end InteractingSLE
