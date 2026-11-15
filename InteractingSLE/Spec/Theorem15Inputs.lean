import InteractingSLE.Frozen.Spec.IsFlowLine
import InteractingSLE.Frozen.Spec.IsGFFWithBoundaryData
import InteractingSLE.Frozen.Spec.IsPiecewiseConstantBoundaryData
import InteractingSLE.Frozen.Spec.HasOrderedProperCompletions
import InteractingSLE.Frozen.Spec.IsInteriorAvailableContact
import InteractingSLE.Frozen.Spec.IsFirstContact
import InteractingSLE.Frozen.Spec.CrossesFromRightAt
import InteractingSLE.Frozen.Spec.AgreeAsCurvesAfter
import InteractingSLE.Frozen.Spec.IsOrderedForceWord
import InteractingSLE.Frozen.Spec.sleLambda

/-!
# Theorem 1.5: the named inputs from other sections

Packet PROVE-SEC7-B2. The specification proves Theorem 1.5 (p. 5: "The proof is W5 and 7.12C–7.12D"; supplement
§3.5, p. 462, and §10.1, p. 544: "Therefore W5, 7.12C and 7.12D supply all three interaction clauses of Theorem 1.5")
from results of the supplement's Sections 9 and 10 and from the single-path results of §§4, 7.1. None of these is in
Lean yet. Each is stated here as a `…Statement : Prop`, on the frozen carriers, with its exact source and page. The
assembly (`Theorem15.lean`) uses nothing else.

| Input | Source |
|---|---|
| `W5Statement` | Theorem W5, supplement §9, pp. 533–534 |
| `W8FirstContactStatement` | Theorem W8, supplement §10, pp. 538–539 (= Theorem 7.9B, p. 459), at `σ = 0`, `Tᵢ = ζᵢ` |
| `Thm712CCrossingStatement` | Theorem 7.12C, supplement §10.1, p. 542 (strict angles), at `Tᵢ = ζᵢ` |
| `Thm712CMergingStatement` | Theorem 7.12C, supplement §10.1, p. 542 (equal angles; also Corollary 7.12E, p. 460) |
| `Thm712DStatement` | Theorem 7.12D, supplement §10.1, p. 543 |
| `CriticalExclusionAfterCrossingStatement` | "Critical exclusion after a crossing", supplement §10.1, p. 544 |
| `Aux25Statement` | Aux. lemma 25, §4.2, p. 127 |
| `Lemma75Statement` | Lemma 7.5, p. 252, in the universal form used by 7.12C (p. 542) and 7.12E (p. 461) |

Every statement uses the available lifetimes `ζᵢ` of the frozen `IsFlowLine` as the source's own-filtration stops
`Tᵢ` ("stopped at an own-filtration time `Tᵢ` no later than its continuation threshold", p. 542): a specialization
of the source statement, so each input is implied by its source theorem.

Also here: the flow-line force word is ordered (`isOrderedForceWord_flowLine`), so Aux. lemma 25 applies to flow
lines (`ae_injOn_of_isFlowLine`), and the angle threshold `D_θ ≥ κ/2 ⟺ Δθ ≥ πκ/(4 − κ)` (p. 544).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem15

/-! ### The named inputs -/

/-- **Named input: Theorem W5** (propagation of strict-prefix ordered completion; supplement §9, pp. 533–534):
"Use the canonical finite-word constant-angle flows with nonzero initial available lifetimes and `θ₁ < θ₂`, from
ordered distinct real seeds or from one common seed. […] Then, almost surely, every pair of finite prefixes strictly
before their original continuation lifetimes has the ordered proper completions of W0." The lower angle `θ₁` is the
right seed `x₁ ≥ x₂` (W0, p. 528; Theorem 7.10, p. 459). A flow line with an inadmissible seed has lifetime `0` and
then the conclusion is vacuous (no `a < 0`), so the premise "nonzero initial available lifetimes" is not repeated.
-/
def W5Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ ω → (c : ℝ≥0∞) < ζ₂ ω →
        HasOrderedProperCompletions (η₁ ω) a (η₂ ω) c

/-- **Named input: Theorem W8** (general finite-word later-contact restart; supplement §10, pp. 538–539; it is the
complete proof of Theorem 7.9B, p. 459), its common-selection assertion at `σ = 0` with `Tᵢ = ζᵢ`: for flow lines
from `x₂ < x₁` with `θ₁ < θ₂ + π`, "the two finite-parameter first contact selections between the full first prefix
and the second suffix starting at `σ` are either both absent, or are attained at the same physical point". Attained
infima `τ₁, τ₂` with `α₁(τ₁) = α₂(τ₂)` are exactly a first contact `(τ₁, τ₂)` in the sense of `IsFirstContact`
(finite parameters, finite terminal values included, p. 458). -/
def W8FirstContactStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, (∃ s t : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω ∧ (t : ℝ≥0∞) ≤ ζ₂ ω ∧ η₁ ω s = η₂ ω t) →
        ∃ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀

/-- **Named input: Theorem 7.12C, strict angles** (available-time crossing; supplement §10.1, p. 542), at
`Tᵢ = ζᵢ`: for `x₂ < x₁` and `θ₂ < θ₁ < θ₂ + π`, "when both have a nonempty available continuation, the first path
crosses from the right of the second to its left in the following precise stopped-order sense: the incoming seed
order is reversed by their outgoing paths in the common active chart. Every pair of strict finite outgoing prefixes
has proper ordered completions with the angle-`θ₁` path on the left of the angle-`θ₂` path." The frozen
`CrossesFromRightAt` is this stopped-order sense (its docstring cites p. 542). -/
def Thm712CCrossingStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₂ < θ₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ∀ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ →
        (s₀ : ℝ≥0∞) < ζ₁ ω → (t₀ : ℝ≥0∞) < ζ₂ ω →
        CrossesFromRightAt (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀

/-- **Named input: Theorem 7.12C, equal angles** (available-time merging; supplement §10.1, p. 542; the same
assertion is Corollary 7.12E, p. 460), at `Tᵢ = ζᵢ`: for `x₂ < x₁` and `θ₁ = θ₂`, "the two paths merge at their first
common point: after the individual increasing capacity changes, they are restrictions of one canonical conditional
flow and agree for as long as both portions are available" — `AgreeAsCurvesAfter` at the first contact. Only the
branch with two nonempty continuations is used ("If either path stops at the meeting, there is no subsequent
crossing or merging portion asserted for it"). -/
def Thm712CMergingStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ : ℝ, x₂ < x₁ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ∀ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ →
        (s₀ : ℝ≥0∞) < ζ₁ ω → (t₀ : ℝ≥0∞) < ζ₂ ω →
        AgreeAsCurvesAfter (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀

/-- **Named input: Theorem 7.12D** (critical-angle exclusion of interior contacts; supplement §10.1, p. 543): "Let
two canonical constant-angle flows have ordered or common real seeds, with lower angle `θ₋` on the right and higher
angle `θ₊` on the left. Put `D_θ = (θ₊ − θ₋)χ/λ`. If `D_θ ≥ κ/2`, their available ranges have no common point in the
open original domain. […] It asserts no exclusion of a common original-real terminal point." Here `η₁` (angle
`θ₁ = θ₋`, seed `x₁`) is the right path and `η₂` (angle `θ₂ = θ₊`, seed `x₂ ≤ x₁`) the left one; the available
ranges include finite terminal values. -/
def Thm712DStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → κ / 2 ≤ (θ₂ - θ₁) * QuantumZipper.chiC κ / sleLambda κ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → (t : ℝ≥0∞) ≤ ζ₂ ω → η₁ ω s = η₂ ω t →
        η₁ ω s ∉ QuantumZipper.H

/-- **Named input: critical exclusion after a crossing** (supplement §10.1, p. 544): "In Theorem 7.12C, suppose in
addition that `(θ₁ − θ₂)χ/λ ≥ κ/2`. […] There is no subsequent common interior point. First-contact confinement and
no return put every subsequent common point of the original open domain in the interior of this chart, so the same
exclusion holds physically." On the meeting branch with two nonempty continuations, every common point of the
available ranges in `ℍ` is the first contact point. -/
def CriticalExclusionAfterCrossingStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₂ < θ₁ → θ₁ < θ₂ + Real.pi →
    κ / 2 ≤ (θ₁ - θ₂) * QuantumZipper.chiC κ / sleLambda κ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ∀ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ →
        (s₀ : ℝ≥0∞) < ζ₁ ω → (t₀ : ℝ≥0∞) < ζ₂ ω →
        ∀ s t : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → (t : ℝ≥0∞) ≤ ζ₂ ω → η₁ ω s = η₂ ω t →
          η₁ ω s ∈ QuantumZipper.H → η₁ ω s = η₁ ω s₀

/-- **Named input: Aux. lemma 25** (simplicity of every continuous available flow prefix; §4.2, p. 127): "Let
`0 < κ < 4`. An integrated finite-force `SLE_κ(ρ)` trace which is continuous on an available stopped interval is
injective there, up to and including a continuous finite terminal endpoint. […] It applies to each finite compact
portion when the available lifetime is unbounded." Almost surely, every continuous generating trace on the whole
available interval `[0, ζ]` is injective there. -/
def Aux25Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
      ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
        InjOn η {t | (t : ℝ≥0∞) ≤ ζ ω}

/-- **Named input: Lemma 7.5** (p. 252: "In the setting of Theorem 1.1 for `κ ∈ (0,4)`, the
`SLE_κ(ρ^L; ρ^R)` flow line `η` of `h` is almost surely determined by `h`"), in the universal form in which the
specification uses it (supplement §2.6, p. 456, "the universal determining graph"; Theorem 7.12C's proof, p. 542,
"Universal finite-force determination gives one canonical path function"; Corollary 7.12E's proof, p. 461): for each
boundary datum, seed and angle there is one Borel map `Φ` of the field giving the lifetime and the capacity-
parametrized available path of every flow line of every field with that boundary datum. -/
def Lemma75Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x θ : ℝ, ∃ Φ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps x θ P h η ζ →
      ∀ᵐ ω ∂P, (Φ (h ω)).1 = ζ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → (Φ (h ω)).2 t = η ω t

/-! ### Bridges -/

/-- The force word of a flow line is ordered: the seed marks `0⁻`, `0⁺` come first, then the genuine jumps
`y < x` at the decreasing positions `y - x < 0` on the left and the jumps `y > x` at the increasing positions
`y - x > 0` on the right. -/
theorem isOrderedForceWord_flowLine (b : ℝ → ℝ) (jumps : Finset ℝ) (x : ℝ) :
    IsOrderedForceWord (flowLineXL b jumps x) (flowLineXR b jumps x) := by
  set SL := (PiecewiseConstantBoundaryData.jumpSet b jumps).filter (· < x) with hSL
  set SR := (PiecewiseConstantBoundaryData.jumpSet b jumps).filter (x < ·) with hSR
  have hL : ∀ k, SL.orderEmbOfFin rfl k - x < 0 := fun k =>
    sub_neg.2 (Finset.mem_filter.1 (SL.orderEmbOfFin_mem rfl k)).2
  have hR : ∀ k, 0 < SR.orderEmbOfFin rfl k - x := fun k =>
    sub_pos.2 (Finset.mem_filter.1 (SR.orderEmbOfFin_mem rfl k)).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · exact le_rfl
    · exact (hL _).le
    · exact absurd hij (not_le.2 (Fin.succ_pos i'))
    · show SL.orderEmbOfFin rfl (Fin.rev j') - x ≤ SL.orderEmbOfFin rfl (Fin.rev i') - x
      exact sub_le_sub_right ((SL.orderEmbOfFin rfl).monotone (Fin.rev_le_rev.2 (Fin.succ_le_succ_iff.1 hij))) x
  · intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · exact le_rfl
    · exact (hL _).le
  · intro i j hij
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · exact le_rfl
    · exact (hR _).le
    · exact absurd hij (not_le.2 (Fin.succ_pos i'))
    · show SR.orderEmbOfFin rfl i' - x ≤ SR.orderEmbOfFin rfl j' - x
      exact sub_le_sub_right ((SR.orderEmbOfFin rfl).monotone (Fin.succ_le_succ_iff.1 hij)) x
  · intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · exact le_rfl
    · exact (hR _).le

/-- **Aux. lemma 25 for flow lines.** Almost surely a flow line is injective on its available interval
`{t | t ≤ ζ}` (its translate is a continuous generating trace of an integrated evolution of the ordered flow-line
force word). -/
theorem ae_injOn_of_isFlowLine (hA : Aux25Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} {x θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ}
    {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b jumps x θ P h η ζ) :
    ∀ᵐ ω ∂P, InjOn (η ω) {t | (t : ℝ≥0∞) ≤ ζ ω} := by
  obtain ⟨h', 𝓕, W, VL, VR, B, -, hcoup, htr⟩ := hη
  have hinj := hA κ hκ hκ4 _ _ (flowLineRhoL κ b jumps x θ) (flowLineRhoR κ b jumps x θ)
    (isOrderedForceWord_flowLine b jumps x) P 𝓕 W VL VR B ζ hcoup.1
  filter_upwards [hinj, htr] with ω hω htω
  intro s hs t ht hst
  exact hω _ htω hs ht (by simp only [hst])

/-- `χ/λ = (4 − κ)/(2π)` (supplement p. 544: "since `χ/λ = (4 − κ)/(2π)`"). -/
theorem chiC_div_sleLambda {κ : ℝ} (hκ : 0 < κ) :
    QuantumZipper.chiC κ / sleLambda κ = (4 - κ) / (2 * Real.pi) := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  unfold QuantumZipper.chiC sleLambda
  rw [div_eq_div_iff (div_ne_zero Real.pi_ne_zero hs.ne') (by positivity)]
  field_simp
  rw [Real.sq_sqrt hκ.le]
  norm_num

/-- **The critical angle** (supplement p. 544): `D_θ = Δθ·χ/λ ≥ κ/2 ⟺ Δθ ≥ πκ/(4 − κ)`, for `0 < κ < 4`. -/
theorem half_le_mul_chiC_div_sleLambda_iff {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (d : ℝ) :
    κ / 2 ≤ d * QuantumZipper.chiC κ / sleLambda κ ↔ Real.pi * κ / (4 - κ) ≤ d := by
  have h4 : 0 < 4 - κ := sub_pos.2 hκ4
  rw [mul_div_assoc, chiC_div_sleLambda hκ, div_le_iff₀ h4, ← mul_div_assoc,
    le_div_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith [Real.pi_pos]

end Theorem15

end InteractingSLE
