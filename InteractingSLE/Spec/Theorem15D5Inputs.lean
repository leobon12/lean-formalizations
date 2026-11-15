/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S10B712D
import InteractingSLE.Spec.Restart.Integrate

/-!
# Theorem 1.5 by the short final proof (§D.5 of the follow-up note): the interfaces

Packet PROVE-T15-D5 (ruling R38: `source/external/AstraIG1/ig1_followup_proofs.txt` L2303–L2386, "D.5. Theorem
1.5: the short final proof and its exact inputs"). D.5 assumes five interfaces "proved with their literal
hypotheses" and deduces Theorem 1.5 from them. In Lean they are the following named propositions (each on the frozen
carriers, universe-polymorphic like `Theorem15Inputs`).

1. *Continuous proper simple finite-force flow lines and a universal determining graph* (Theorems 1.2–1.3,
   `κ < 4`): `Theorem15.Aux25Statement` (simplicity), `Theorem15.Lemma75Statement` (universal determination),
   `Supp10.FiniteEndpointRealStatement` (a genuine finite continuation endpoint is original-real).
2. *Common first contact and the actual conditional continuation coupling* (7.7–7.8), "including the active prime
   end […] and reconstruction of both original clocks": `Supp10.Lemma77Statement` (first contact, confinement),
   `Restart.FirstContactRestartStatement` (the restart carrier) and its form with the active prime end,
   `FirstContactRestartLimStatement` (below).
3. *W5's strict-prefix ordered proper-completion theorem*, with its contact-order theorem:
   `Theorem15.W5Statement`; the deterministic contact-order theorems `Supp10.G5Statement` (common seed) and
   `Supp10.Aux84Statement` (ordered distinct seeds).
4. *W0b; G7's stopped precontact kernel and GB7a's exclusion of an open boundary interval of outward cumulative
   weight at least `c`*: `Supp9.W0bStatement`; `G7GB7aFirstHitStatement` (below).
5. *The rational-cut collar of 7.12D* (an interior contact gives a first hit on the exposed old side at a retained
   pair): proved, `Theorem15D5.notMem_H_of_firstHit_strict` (`Theorem15D5Critical.lean`).

New here:

* `StrictContactsIncreasing`: increasing order of the contacts strictly before both lifetimes (the order 7.12D's
  proof uses: "W5 gives all the earlier ordered proper completions and, by their contact-order theorem, increasing
  coordinates of the contacts"; only strict contacts occur in that proof).
* `G7GB7aFirstHitStatement` (interface 4's G7 + GB7a at a retained pair of interface 5): its hypothesis is GB7a's,
  the right outward cumulative weight of the exposed first left side is at least `c = κ/2 − 2`, and its order
  premise is the strict contact order. It implies PROVE-SUPP10-B's `Supp10.Thm712DFirstHitStatement`
  (`thm712DFirstHitStatement_of_g7GB7a`), whose premises are stronger (full contact order, `D_θ ≥ κ/2`).
* `IsChartContinuationLim`, `FirstContactRestartLimStatement`: the restart carrier with the active prime end, i.e.
  the chart limits of the continuations at their own points (`φ → γᵢ(u)` along the active domain at `ηᵢ(cᵢ u)`),
  which the frozen `CrossesFromRightAt` asks for. It implies `Restart.FirstContactRestartStatement`
  (`firstContactRestartStatement_of_lim`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem15D5

open Sec7 Theorem15 Supp10 Restart

/-! ### Strict contact order -/

/-- **Increasing order of the strict contacts**: two contacts of `α|[0, T₁)` and `β|[0, T₂)` (both parameters
strictly below the lifetimes) with `s < s'` have `t < t'`. -/
def StrictContactsIncreasing (α : ℝ≥0 → ℂ) (T₁ : ℝ≥0∞) (β : ℝ≥0 → ℂ) (T₂ : ℝ≥0∞) : Prop :=
  ∀ s s' t t' : ℝ≥0, (s : ℝ≥0∞) < T₁ → (s' : ℝ≥0∞) < T₁ → (t : ℝ≥0∞) < T₂ → (t' : ℝ≥0∞) < T₂ →
    α s = β t → α s' = β t' → s < s' → t < t'

/-- Full contact order (finite terminal values included) gives the strict one. -/
theorem ContactsIncreasing.strict {α β : ℝ≥0 → ℂ} {T₁ T₂ : ℝ≥0∞} (h : ContactsIncreasing α T₁ β T₂) :
    StrictContactsIncreasing α T₁ β T₂ := fun s s' t t' hs hs' ht ht' hst hst' hlt =>
  h (s, t) ⟨zero_le, hs.le, zero_le, ht.le, hst⟩ (s', t') ⟨zero_le, hs'.le, zero_le, ht'.le, hst'⟩ hlt

/-! ### Interface 4: G7 and GB7a at a retained pair -/

/-- **Interface 4 (G7 + GB7a) at the retained pair of interface 5** (follow-up note D.5, items 4–5; specification
supplement §10.1, proof of Theorem 7.12D, pp. 543–544). `η₁` is the lower-angle flow from `x₁`, `η₂` the
higher-angle flow from `x₂ ≤ x₁`; the hypothesis is GB7a's: the exposed first left side, of height `−λ − θ₁χ`, has
right outward cumulative weight (seen by the angle-`θ₂` path, after adding `θ₂χ`) at least `c = κ/2 − 2`. Almost
surely, given W5's ordered proper completions and the increasing order of the strict contacts ("W5 gives all the
earlier ordered proper completions and, by their contact-order theorem, increasing coordinates of the contacts"):
at a retained pair of strictly available own cutoffs `u` (first path) and `r` (second path) with `η₂(r)` off the
retained first prefix `A = η₁([0, u])`, the second future does not make its first new contact with `A` at an
interior point `η₁(x) ∈ ℍ`, `x < u`. Source: "Stop the actual second future at its first new contact with the
retained old union […]. G7 identifies this entire conditional stopped field–path law with the canonical finite-word
flow. […] this first hit belongs to an open interval of the exposed first left side in (7.12D.1). […] GB7a excludes
every point of this interval for the canonical conditional law". -/
def G7GB7aFirstHitStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ →
    κ / 2 - 2 ≤
      Sec4.cumWeightRight κ ((-sleLambda κ - θ₁ * QuantumZipper.chiC κ) + θ₂ * QuantumZipper.chiC κ) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, (∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ ω → (c : ℝ≥0∞) < ζ₂ ω →
          HasOrderedProperCompletions (η₁ ω) a (η₂ ω) c) →
        StrictContactsIncreasing (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) →
        ∀ u r : ℝ≥0, (u : ℝ≥0∞) < ζ₁ ω → (r : ℝ≥0∞) < ζ₂ ω → η₂ ω r ∉ η₁ ω '' Icc 0 u →
          ∀ t x : ℝ≥0, r < t → (t : ℝ≥0∞) < ζ₂ ω → x < u → η₂ ω t = η₁ ω x →
            η₁ ω x ∈ QuantumZipper.H → (∀ t' : ℝ≥0, r < t' → t' < t → η₂ ω t' ∉ η₁ ω '' Icc 0 u) →
            False

/-- **(7.12D.1) turns the critical angle into GB7a's weight hypothesis** (supplement p. 543; D.5: "Its right
outward cumulative force weight is therefore `D − 2`. If `D ≥ κ/2`, this is at least `c`"). -/
theorem cumWeightRight_exposed_ge_of_half_le {κ : ℝ} (hκ : 0 < κ) {θ₁ θ₂ : ℝ}
    (hD : κ / 2 ≤ (θ₂ - θ₁) * QuantumZipper.chiC κ / sleLambda κ) :
    κ / 2 - 2 ≤
      Sec4.cumWeightRight κ ((-sleLambda κ - θ₁ * QuantumZipper.chiC κ) + θ₂ * QuantumZipper.chiC κ) :=
  (thm712D_one hκ θ₁ θ₂).2 hD

/-- Interface 4 in the D.5 form implies PROVE-SUPP10-B's local step of Theorem 7.12D (whose premises, full contact
order and `D_θ ≥ κ/2`, are stronger). -/
theorem thm712DFirstHitStatement_of_g7GB7a (hFH : G7GB7aFirstHitStatement.{u}) :
    Thm712DFirstHitStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hD Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  filter_upwards [hFH κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx (cumWeightRight_exposed_ge_of_half_le hκ hD) P h hh
    η₁ η₂ ζ₁ ζ₂ h₁ h₂] with ω hω
  intro hord hCI
  exact hω hord (ContactsIncreasing.strict hCI)

/-! ### Interface 2 with the active prime end -/

/-- **The pathwise restart at a first contact, with the active prime end**: `Restart.IsChartContinuation` together
with the chart limits of the two continuations at their own points: for `u < Uᵢ`, `φ` tends to `γᵢ(u)` along the
active domain `D` at the physical point `ηᵢ(cᵢ u)` (D.5, interface 2: "including the active prime end […] and
reconstruction of both original clocks"; supplement p. 542: "the incoming seed order is reversed by their outgoing
paths in the common active chart"). At a point `γᵢ(u) ∈ ℍ` this is the continuity of `φ` inside `D`; at a chart
boundary point it is the boundary correspondence of the chart along the continuation. -/
def IsChartContinuationLim (κ : ℝ) (h H : LQGMetric.DistOn upperHalfPlaneOpens) (η₁ : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞)
    (s₀ : ℝ≥0) (η₂ : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) (t₀ : ℝ≥0) (γ₁ γ₂ : ℝ≥0 → ℂ) (U₁ U₂ : ℝ≥0∞) : Prop :=
  ∃ (φ ψ : ℂ → ℂ) (lift : ℂ → ℝ) (c₁ c₂ : ℝ≥0 → ℝ≥0),
    IsActiveChart (activeDomain η₁ s₀ η₂ t₀) (η₁ s₀) φ ∧
    BijOn ψ QuantumZipper.H (activeDomain η₁ s₀ η₂ t₀) ∧ (∀ w ∈ QuantumZipper.H, φ (ψ w) = w) ∧
    (∀ w ∉ QuantumZipper.H, ψ w ∉ activeDomain η₁ s₀ η₂ t₀) ∧
    ContinuousOn lift (activeDomain η₁ s₀ η₂ t₀) ∧
    (∀ z ∈ activeDomain η₁ s₀ η₂ t₀,
      deriv φ z = (‖deriv φ z‖ : ℂ) * Complex.exp (Complex.I * (lift z : ℂ))) ∧
    IsChartTransport (φ, ψ, lift) 1 0 (QuantumZipper.chiC κ) h H ∧
    StrictMonoOn c₁ {u | (u : ℝ≥0∞) ≤ U₁} ∧
    c₁ '' {u | (u : ℝ≥0∞) ≤ U₁} = {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ₁} ∧
    StrictMonoOn c₂ {u | (u : ℝ≥0∞) ≤ U₂} ∧
    c₂ '' {u | (u : ℝ≥0∞) ≤ U₂} = {t | t₀ ≤ t ∧ (t : ℝ≥0∞) ≤ ζ₂} ∧
    (∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₁ → η₁ (c₁ u) = ψ (γ₁ u)) ∧
    (∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₂ → η₂ (c₂ u) = ψ (γ₂ u)) ∧
    (∀ u : ℝ≥0, (u : ℝ≥0∞) < U₁ →
      Tendsto φ (𝓝[activeDomain η₁ s₀ η₂ t₀] (η₁ (c₁ u))) (𝓝 (γ₁ u))) ∧
    ∀ u : ℝ≥0, (u : ℝ≥0∞) < U₂ → Tendsto φ (𝓝[activeDomain η₁ s₀ η₂ t₀] (η₂ (c₂ u))) (𝓝 (γ₂ u))

theorem IsChartContinuationLim.isChartContinuation {κ : ℝ} {h H : LQGMetric.DistOn upperHalfPlaneOpens}
    {η₁ : ℝ≥0 → ℂ} {ζ₁ : ℝ≥0∞} {s₀ : ℝ≥0} {η₂ : ℝ≥0 → ℂ} {ζ₂ : ℝ≥0∞} {t₀ : ℝ≥0} {γ₁ γ₂ : ℝ≥0 → ℂ}
    {U₁ U₂ : ℝ≥0∞} (hC : IsChartContinuationLim κ h H η₁ ζ₁ s₀ η₂ ζ₂ t₀ γ₁ γ₂ U₁ U₂) :
    IsChartContinuation κ h H η₁ ζ₁ s₀ η₂ ζ₂ t₀ γ₁ γ₂ U₁ U₂ := by
  obtain ⟨φ, ψ, lift, c₁, c₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, -, -⟩ := hC
  exact ⟨φ, ψ, lift, c₁, c₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- **Interface 2 with the active prime end: the first-contact restart carrier with chart limits**
(`Restart.FirstContactRestartStatement` with `IsChartContinuationLim` in place of `IsChartContinuation`). -/
def FirstContactRestartLimStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∃ (S : Type) (_ : MeasurableSpace S) (H : S → LQGMetric.DistOn upperHalfPlaneOpens)
      (γ₁ γ₂ : S → ℝ≥0 → ℂ) (U₁ U₂ : S → ℝ≥0∞) (M : Set Ω) (β : Ω → BoundaryWord) (X : Ω → S)
      (K : Kernel BoundaryWord S),
      IsRestartCoordinates H γ₁ γ₂ U₁ U₂ ∧ MeasurableSet M ∧ Measurable β ∧ Measurable X ∧
      IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K ∧
      (∀ᵐ c ∂(P.restrict M).map β, IsConditionalFlowPair κ θ₁ θ₂ c (K c) H γ₁ γ₂ U₁ U₂) ∧
      ∀ᵐ ω ∂P, ∀ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ →
        (s₀ : ℝ≥0∞) < ζ₁ ω → (t₀ : ℝ≥0∞) < ζ₂ ω →
        ω ∈ M ∧ IsChartContinuationLim κ (h ω) (H (X ω)) (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀
          (γ₁ (X ω)) (γ₂ (X ω)) (U₁ (X ω)) (U₂ (X ω))

/-- The carrier with the active prime end gives the restart carrier. -/
theorem firstContactRestartStatement_of_lim (hR : FirstContactRestartLimStatement.{u}) :
    FirstContactRestartStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  obtain ⟨S, mS, H, γ₁, γ₂, U₁, U₂, M, β, X, K, hco, hM, hβ, hX, hK, hlaw, hpair, hpath⟩ :=
    hR κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  refine ⟨S, mS, H, γ₁, γ₂, U₁, U₂, M, β, X, K, hco, hM, hβ, hX, hK, hlaw, hpair, ?_⟩
  filter_upwards [hpath] with ω hω s₀ t₀ h₀ hs₀ ht₀
  obtain ⟨hMω, hC⟩ := hω s₀ t₀ h₀ hs₀ ht₀
  exact ⟨hMω, hC.isChartContinuation⟩

end Theorem15D5

end InteractingSLE
