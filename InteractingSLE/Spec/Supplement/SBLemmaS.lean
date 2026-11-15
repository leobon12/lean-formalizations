/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2Remainder

/-!
# Lemmas S2–S6 of the supplement (one-sided erasure and gluing)

Packet PROVE-T14-SB2. Exact statements, on the frozen carriers and the carriers of `SB2Remainder`, of the lemmas of
supplement pp. 577–584 (`source/spec/p577-624.md` L5–L133) used by Lemmas SB1–SB2 and Theorem SB4. Convention S1 is
`SB.IsOneSided` (`SB2Remainder.lean`). None of S2–S6 is proved here (see the handoff).

* `S2HullStatement`, `S2LiftStatement` — Lemma S2 (one-sided hull restriction, p. 577), deterministic: (S2.1) and the
  `D_A` membership; the continuous injective proper lift from the left entry prime end;
* `S3Statement` — Lemma S3 (no open erased interval for a strict upper angle, p. 579);
* `S4Statement` — Lemma S4 (the actual upper path in a retained own domain, p. 579), in the form of `SB2UpperStatement`
  for an own angle history (schedule) from `0` with all angles below `ϑ`;
* `S5Statement`, `S5InsideStatement` — Lemma S5 (one-sided physical gluing, p. 582), deterministic;
* `S6Statement` — Lemma S6 (terminal completion when the middle groups are admissible, p. 583).

The own angle histories of S0 (p. 576) are the frozen schedule histories `⟨0, true, scheduleProgram 0 l⟩` through
`k` instructions (`schedulePrefix`); the finite compact ranges `A` of S1–S2 are images `p '' [0, 1]` of continuous
paths from `0` in `closure ℍ` ("Take any parameterized part of the original history in `A` from `0` to its first visit
to `L`").
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace SB

/-- The own angle history of S0 from `0` through `k` instructions of the schedule `l` (physical set). -/
def schedulePrefix {Ω : Type u} (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω : Ω) : Set ℂ :=
  prefixPhysSet κ b jumps ⟨0, true, scheduleProgram 0 l⟩ (fun j => E ⟨0, true, scheduleProgram 0 l⟩ j ω) k

/-! ### Lemma S2 (deterministic) -/

/-- **Lemma S2, the hull restriction** (supplement p. 577, (S2.1)): let `A = p([0, 1])` be the compact range of a
continuous path from `0` in `closure ℍ`, and `β'` a proper continuous injective curve in `closure ℍ` from `0` whose
closed right side contains `A` (the S1 witness). Then `L = min(A ∩ ℝ) ≤ 0`, the witness visits `L` at some `t_L`
(`t_L = 0` if `L = 0`), `β'([0, t_L]) ⊆ K_A` (the filled hull with its real base), `β'((t_L, ∞)) ⊆ closure D_A`, and
"every interior point of the second range which is off `A` lies in `D_A`". -/
def S2HullStatement : Prop :=
  ∀ (p : ℝ → ℂ) (β' : ℝ≥0 → ℂ), ContinuousOn p (Icc 0 1) → p 0 = 0 → (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) →
    Supp9B.IsProperCurve β' → β' 0 = 0 → p '' Icc 0 1 ⊆ Supp9B.closedRightSide β' →
    realMin (p '' Icc 0 1) ≤ 0 ∧
      ∃ tL : ℝ≥0, β' tL = realMin (p '' Icc 0 1) ∧ (realMin (p '' Icc 0 1) = 0 → tL = 0) ∧
        β' '' Icc 0 tL ⊆ hullK (p '' Icc 0 1) ∧
        β' '' Ioi tL ⊆ closure (H \ fillH (p '' Icc 0 1)) ∧
        ∀ t : ℝ≥0, tL < t → β' t ∈ H → β' t ∉ p '' Icc 0 1 → β' t ∈ H \ fillH (p '' Icc 0 1)

/-- **Lemma S2, the one-sided lift** (supplement pp. 577–579): in the setting of `S2HullStatement`, if the inverse
map of a left entry chart `c` of `D_A` at `L` "has its continuous finite-fiber extension" `g` to `closure ℍ`, then
"the post-`t_L` arc has a continuous injective proper lift in `closure ℍ` under `g_A`, starting from the left
original-real base prime end `g_A(L⁻)` and ending at infinity": a proper curve `γ` from `0` with `g ∘ γ = β'(t_L + ·)`.
(The capacity and driver assertions for available intervals without a shared open subarc are not included.) -/
def S2LiftStatement : Prop :=
  ∀ (p : ℝ → ℂ) (β' : ℝ≥0 → ℂ), ContinuousOn p (Icc 0 1) → p 0 = 0 → (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) →
    Supp9B.IsProperCurve β' → β' 0 = 0 → p '' Icc 0 1 ⊆ Supp9B.closedRightSide β' →
    ∀ (c : Chart) (g : ℂ → ℂ), IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c →
      ContinuousOn g {z | 0 ≤ z.im} → EqOn g c.2.1 H → (∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) →
    ∀ tL : ℝ≥0, β' tL = realMin (p '' Icc 0 1) →
      ∃ γ : ℝ≥0 → ℂ, Supp9B.IsProperCurve γ ∧ γ 0 = 0 ∧ ∀ s : ℝ≥0, g (γ s) = β' (tL + s)

/-! ### Lemmas S3 and S4 (probabilistic) -/

/-- **Lemma S3** (no open erased interval for a strict upper angle; supplement p. 579), in the setting of Theorem 1.4:
let `A` be the own angle history from `0` through `k` instructions of a schedule `l` with all angles below `ϑ`, and
`β` the angle-`ϑ` flow from `0`; if S1 holds almost surely for `A` and every available prefix of `β`, then almost
surely, after the entrance at `L = min(A ∩ ℝ)`, the available path `β` has no common nontrivial open subarc with
`A`. -/
def S3Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
    ∀ (l : List (ℝ × ℝ≥0)) (k : ℕ) (ϑ : ℝ), l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) ∧ p.1 < ϑ) → ϑ ≤ Real.pi / 2 →
    ∀ (β : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps 0 ϑ P h β ζ →
      (∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (schedulePrefix κ b jumps E l k ω) (β ω) a) →
      ∀ᵐ ω ∂P, ∀ s₁ s₂ : ℝ≥0, firstVisit (β ω) (ζ ω) (realMin (schedulePrefix κ b jumps E l k ω)) ≤ s₁ →
        s₁ < s₂ → (s₂ : ℝ≥0∞) ≤ ζ ω → ¬ β ω '' Ioo s₁ s₂ ⊆ schedulePrefix κ b jumps E l k ω

/-- **Lemma S4** (the actual upper path in a retained own domain; supplement p. 579), in the setting of Theorem 1.4,
for the clipped own stops `T = t ∧ ζ`: with the hypotheses of S3, (i) `β([0, T ∧ τ]) ⊆ K_A`, where `τ` is the first
visit to `L`; (ii) conditionally on the retained history (`𝒢 ⊇ pastSigma`), on `{τ < T}`: in a left entry chart `c`
of `D_A` at `L`, a driver `Wr` is the canonical angle-`ϑ` flow of the conditional field, the surviving original real
points keep their heights, and the lift of the post-`τ` portion is the physical trace of `Wr` stopped at a relative
stop `Tr ≤ ζr` ("stopped by the reconstructed original rule `T`"). The same form as `SB2UpperStatement`. -/
def S4Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
    ∀ (l : List (ℝ × ℝ≥0)) (k : ℕ) (ϑ : ℝ), l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) ∧ p.1 < ϑ) → ϑ ≤ Real.pi / 2 →
    ∀ (β : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps 0 ϑ P h β ζ →
      (∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (schedulePrefix κ b jumps E l k ω) (β ω) a) →
    ∀ t : ℝ≥0∞,
      (∀ᵐ ω ∂P, β ω '' {s | (s : ℝ≥0∞) ≤ min (min t (ζ ω))
          (firstVisit (β ω) (ζ ω) (realMin (schedulePrefix κ b jumps E l k ω)))} ⊆
        hullK (schedulePrefix κ b jumps E l k ω)) ∧
      ∃ (𝒢 : MeasurableSpace Ω) (c : Ω → Chart) (bc : Ω → ℝ → ℝ) (jc : Ω → Finset ℝ) (Wr : ℝ≥0 → Ω → ℝ)
        (ζr Tr : Ω → ℝ≥0∞),
        𝒢 ≤ mΩ ∧ pastSigma κ b jumps ⟨0, true, scheduleProgram 0 l⟩ (E ⟨0, true, scheduleProgram 0 l⟩) k ≤ 𝒢 ∧
        IsCondFlowLineDriverOn (mΩ := mΩ) κ ϑ 𝒢 P
          {ω | firstVisit (β ω) (ζ ω) (realMin (schedulePrefix κ b jumps E l k ω)) < min t (ζ ω)} h c bc jc Wr ζr ∧
        ∀ᵐ ω ∂P, firstVisit (β ω) (ζ ω) (realMin (schedulePrefix κ b jumps E l k ω)) < min t (ζ ω) →
          IsLeftEntryChart (schedulePrefix κ b jumps E l k ω) (realMin (schedulePrefix κ b jumps E l k ω)) (c ω) ∧
          RetainsOriginalHeights (schedulePrefix κ b jumps E l k ω) (c ω) b jumps (bc ω) (jc ω) ∧
          Tr ω ≤ ζr ω ∧
          β ω '' {s | firstVisit (β ω) (ζ ω) (realMin (schedulePrefix κ b jumps E l k ω)) < (s : ℝ≥0∞) ∧
              (s : ℝ≥0∞) ≤ min t (ζ ω)} ⊆ (c ω).tipSet (fun r => Wr r ω) (Tr ω) ∧
          (c ω).tipSet (fun r => Wr r ω) (Tr ω) ⊆
            β ω '' {s | firstVisit (β ω) (ζ ω) (realMin (schedulePrefix κ b jumps E l k ω)) ≤ (s : ℝ≥0∞) ∧
              (s : ℝ≥0∞) ≤ min t (ζ ω)}

/-! ### Lemma S5 (deterministic) -/

/-- **Lemma S5** (one-sided physical gluing; supplement p. 582), the main clause: in the geometric setup of S2 (a
compact range `A = p([0, 1])` from `0`, a second prefix `β([0, a₂])` from `0` with S1 for `A`, a left entry chart `c`
of `D_A` at `L` whose inverse has the continuous finite-fiber extension `g`), suppose the second prefix has entered
`D_A` at `t_L` with simple relative lift `bR` from `0` (`g ∘ bR = β(t_L + ·)` on `[0, a₂ − t_L]`), and `aR` is a simple
available relative first prefix from a real `w ≥ 0`, with `aR([0, a₁])`, `bR([0, a₂ − t_L])` having ordered proper
completions with `bR` on the left. Then "the physical range `A ∪ g_A⁻¹(a)` and the original actual second prefix
satisfy the one-sided predicate S1". -/
def S5Statement : Prop :=
  ∀ (p : ℝ → ℂ) (β : ℝ≥0 → ℂ) (a₂ : ℝ≥0), ContinuousOn p (Icc 0 1) → p 0 = 0 →
    (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) → β 0 = 0 → IsOneSided (p '' Icc 0 1) β a₂ →
    ∀ (c : Chart) (g : ℂ → ℂ), IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c →
      ContinuousOn g {z | 0 ≤ z.im} → EqOn g c.2.1 H → (∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) →
    ∀ (tL a₁ : ℝ≥0) (aR bR : ℝ≥0 → ℂ) (w : ℝ), tL ≤ a₂ → β tL = realMin (p '' Icc 0 1) → bR 0 = 0 →
      (∀ s : ℝ≥0, s ≤ a₂ - tL → g (bR s) = β (tL + s)) → 0 ≤ w → aR 0 = w →
      HasOrderedProperCompletions aR a₁ bR (a₂ - tL) →
      IsOneSided (p '' Icc 0 1 ∪ g '' (aR '' Icc 0 a₁)) β a₂

/-- **Lemma S5, the inside clause** (supplement p. 582): "If the whole actual second prefix is contained in `K_A`, the
same conclusion holds for every available own-domain extension of `A`": S1 for `A` and the prefix `β([0, a₂]) ⊆ K_A`
gives S1 for `A ∪ A'` whenever `A' ⊆ closure D_A`. -/
def S5InsideStatement : Prop :=
  ∀ (p : ℝ → ℂ) (β : ℝ≥0 → ℂ) (a₂ : ℝ≥0), ContinuousOn p (Icc 0 1) → p 0 = 0 →
    (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) → β 0 = 0 → IsOneSided (p '' Icc 0 1) β a₂ →
    β '' Icc 0 a₂ ⊆ hullK (p '' Icc 0 1) →
    ∀ A' : Set ℂ, A' ⊆ closure (H \ fillH (p '' Icc 0 1)) → IsOneSided (p '' Icc 0 1 ∪ A') β a₂

/-! ### Lemma S6 -/

/-- **Lemma S6** (terminal completion when the middle groups are admissible; supplement p. 583): "For two
constant-angle canonical flows from ordered seeds `x_β ≤ x_α`, with strictly ordered angles and admissible initial
groups, suppose every cumulative group of either path on the intervening seed interval is admissible. Then W5's
strong proper-completion assertion extends to their finite available terminal endpoints." As in `W5Statement`, the
lower angle `θ₁` is the right seed `x₁ ≥ x₂`; its left groups and the upper path's right groups on `(x₂, x₁)` are
admissible; the initial lifetimes are nonzero. -/
def S6Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
      (∀ x ∈ Ioo x₂ x₁, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + θ₁ * chiC κ)) →
      (∀ x ∈ Ioo x₂ x₁, x ∉ jumps → -2 < Sec4.cumWeightRight κ (b x + θ₂ * chiC κ)) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      (∀ᵐ ω ∂P, 0 < ζ₁ ω) → (∀ᵐ ω ∂P, 0 < ζ₂ ω) →
      ∀ᵐ ω ∂P, ∀ a c : ℝ≥0, (a : ℝ≥0∞) ≤ ζ₁ ω → (c : ℝ≥0∞) ≤ ζ₂ ω →
        HasOrderedProperCompletions (η₁ ω) a (η₂ ω) c

/-- **S6 gives SB1 when the middle word is doubly admissible** (SB1's hybrid condition with its first alternative
everywhere): SB1's conclusion for the lower flow from `v` at angle `−π/2` and the upper flow from `u < v` at angle
`ψ > −π/2`, from S6 with `(x₁, θ₁) = (v, −π/2)`, `(x₂, θ₂) = (u, ψ)`. -/
theorem sb1_of_s6 (hS6 : S6Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {u v ψ : ℝ} (huv : u < v) (hψ : -(Real.pi / 2) < ψ)
    (hL : ∀ x ∈ Ioo u v, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    (hR : ∀ x ∈ Ioo u v, x ∉ jumps → -2 < Sec4.cumWeightRight κ (b x + ψ * chiC κ))
    {ηL ηU : Ω → ℝ≥0 → ℂ} {ζL ζU : Ω → ℝ≥0∞} (hηL : IsFlowLine κ b jumps v (-(Real.pi / 2)) P h ηL ζL)
    (hηU : IsFlowLine κ b jumps u ψ P h ηU ζU) (hζL : ∀ᵐ ω ∂P, 0 < ζL ω) (hζU : ∀ᵐ ω ∂P, 0 < ζU ω) :
    ∀ᵐ ω ∂P, ∀ a c : ℝ≥0, (a : ℝ≥0∞) ≤ ζL ω → (c : ℝ≥0∞) ≤ ζU ω →
      HasOrderedProperCompletions (ηL ω) a (ηU ω) c :=
  hS6 κ hκ hκ4 b jumps hb v u (-(Real.pi / 2)) ψ huv.le hψ hL hR P h hh ηL ηU ζL ζU hηL hηU hζL hζU

end SB

end Theorem14

end InteractingSLE
