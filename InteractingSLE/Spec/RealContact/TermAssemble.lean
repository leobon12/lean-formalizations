/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermInv

/-!
# The terminal retained pair: (Det) from the clock of the first path

Packet PROVE-RC-TERM (ruling R124). `TermField.lean` reduced the named input `TerminalRetainedCondDetStatement` to
(Det) for explicit data (`TerminalRetainedDetStatement`). `IsTerminalRetainedContinuation` has thirteen clauses. This
file discharges the eight clauses which only concern the completed second path — the active chart at the terminal
point, its inverse, lift and chart field (`TermPath.lean`, `TermInv.lean`), and the junction — and leaves:

**`TerminalRetainedClockStatement`** (named input, **not proved in Lean**): almost surely on the trigger event, the
seed position is positive, the word has the original datum just left of the terminal point, and there is a clock `c₁`
on `[0, σ]`, `σ` at most the lifetime of the decoded canonical flow code `Γ` of the chart field from the seed
position, strictly increasing, onto the physical times of the first path up to and including its first new contact
with the completed second path, with `η₁ ∘ c₁ = termInv ∘ Γ` (the first path is the canonical flow of the chart field,
read through the extended inverse chart).

* **`terminalRetainedDet_of_clock`**, **`terminalRetainedCondDet_of_clock`**: (Det) and the named input from the clock
  statement.

The junction clause is `Term.IsFreshRealTip.eq_zero_of_extendFrom_eq`: the extended inverse chart takes the terminal
point as value only at `0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

universe u

namespace InteractingSLE.RealContact

open Restart LQGMetric Sec2.Assembly Exist.Staged Exist.StagedLaw Term

open PiecewiseConstantBoundaryData (leftLim)

/-- **Named input: the clock of the first path in the chart of the completed second path** (Lemma G7's conclusion at
the retained pair `(0, ζ₂)`, supplement pp. 497–498, without the chart clauses). Binders of
`TerminalRetainedDetStatement`. Almost surely on the trigger event, with `r` the record of the second path through its
lifetime, `Γ` the decoded canonical flow code of the chart field from the seed position and `U` its lifetime:
* the seed position `Term.termSeed x₁ x₂ r` is positive;
* the word `Term.termWord κ θ₂ c r` has the original datum just left of the terminal point;
* there are a clock `c₁` and `σ ≤ U` with `c₁` strictly increasing on `[0, σ]`, mapping it onto the physical times
  `t ≤ ζ₁` with no contact with `η₂([0, T])` strictly between `0` and `t`, and `η₁ (c₁ s) = Term.termInv x₂ r (Γ s)`
  for `s ≤ σ`.

**Not proved in Lean.** -/
def TerminalRetainedClockStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ →
    κ / 2 - 2 ≤
      Sec4.cumWeightRight κ ((-sleLambda κ - θ₁ * QuantumZipper.chiC κ) + θ₂ * QuantumZipper.chiC κ) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ F : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞,
      IsCanonicalFlowCode κ θ₁ F →
    ∀ (c : BoundaryWord) (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞), c.IsSorted → c.jumps = jumps.image (· - x₂) →
      (∀ y ∉ jumps.image (· - x₂), c.fn y = b (y + x₂)) → Measurable E → (∀ ω, IsRegularDriver (E ω)) →
      (∀ ω, (E ω).2 = ζ₂ ω) →
      IsFlowLineDriver κ c.fn c.jumps θ₂ P (fun ω => Exist.flowField x₂ 0 (h ω)) (fun s ω => (E ω).1 s)
        (fun ω => (E ω).2) →
      (∀ᵐ ω ∂P, IsGeneratingTrace (E ω).1 (ζ₂ ω) (fun t => η₂ ω t - x₂)) →
      ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (e : ℝ), (T : ℝ≥0∞) = ζ₂ ω → η₂ ω T = e → e < x₂ →
        (∃ (s : ℝ≥0) (y : ℝ), (s : ℝ≥0∞) < ζ₁ ω ∧ η₁ ω s = y ∧ y ≤ e) →
        0 < termSeed x₁ x₂ (termRec (E ω)) ∧
        leftLim (termWord κ θ₂ c (termRec (E ω))).fn 0 = leftLim b e ∧
        ∃ (c₁ : ℝ≥0 → ℝ≥0) (σ : ℝ≥0∞),
          σ ≤ (F ((termWord κ θ₂ c (termRec (E ω)), termSeed x₁ x₂ (termRec (E ω))),
            termField κ x₂ (termRec (E ω)) (h ω))).2 ∧
          StrictMonoOn c₁ {s | (s : ℝ≥0∞) ≤ σ} ∧
          c₁ '' {s | (s : ℝ≥0∞) ≤ σ} =
            {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ₁ ω ∧ ∀ t' : ℝ≥0, 0 < t' → t' < t → η₁ ω t' ∉ η₂ ω '' Icc 0 T} ∧
          ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ σ → η₁ ω (c₁ s) = termInv x₂ (termRec (E ω))
            (decPath (F ((termWord κ θ₂ c (termRec (E ω)), termSeed x₁ x₂ (termRec (E ω))),
              termField κ x₂ (termRec (E ω)) (h ω))) s)

/-- **The pathwise assembly**: for one sample, the chart clauses of `IsTerminalRetainedContinuation` and the junction
from the facts on the second path, and the remaining clauses from the clock. -/
theorem isTerminalRetainedContinuation_of_clock {κ : ℝ} {b : ℝ → ℝ} {hf : DistOn upperHalfPlaneOpens}
    {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ : ℝ≥0∞} {x₂ q : ℝ} {T : ℝ≥0} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    (hg : LocalExt.IsDrvGood (recHist (termRec e))) (hT : (T : ℝ≥0∞) = e.2)
    (hη : IsGeneratingTrace e.1 e.2 (fun t => η₂ t - x₂)) (hinj : InjOn η₂ {t | (t : ℝ≥0∞) ≤ e.2})
    (htip : η₂ T = q) (hq : q < x₂) (h₁ : (η₁ 0).im = 0) {w : BoundaryWord} {Γ : ℝ≥0 → ℂ} {U : ℝ≥0∞}
    (hword : leftLim w.fn 0 = leftLim b q) {c₁ : ℝ≥0 → ℝ≥0} {σ : ℝ≥0∞} (hσ : σ ≤ U)
    (hmono : StrictMonoOn c₁ {s | (s : ℝ≥0∞) ≤ σ})
    (himg : c₁ '' {s | (s : ℝ≥0∞) ≤ σ} =
      {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ₁ ∧ ∀ t' : ℝ≥0, 0 < t' → t' < t → η₁ t' ∉ η₂ '' Icc 0 T})
    (hpath : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ σ → η₁ (c₁ s) = termInv x₂ (termRec e) (Γ s)) :
    IsTerminalRetainedContinuation κ b hf (termField κ x₂ (termRec e) hf) η₁ ζ₁ η₂ T w Γ U := by
  have hne : q ≠ x₂ := ne_of_lt hq
  have hfresh := isFreshRealTip_of_trace he hg hT hη hinj htip hne
  have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hfresh.trace hfresh.cont hfresh.zero hfresh.pos
    hfresh.traceCont
  have hD := activeDomain_eq_image he hg hT hη hinj htip hne h₁
  refine ⟨termFwd x₂ (termRec e), termInv x₂ (termRec e), termLift x₂ (termRec e), c₁, σ,
    isActiveChart_term he hg hT hη hinj htip hne h₁, ?_, fun v hv => termFwd_termInv hv, ?_, ?_, ?_,
    isChartTransport_term he hg κ x₂ hf, hσ, hmono, himg, hpath, fun s hs hs' => ?_, ?_⟩
  · rw [hD]
    exact bijOn_termInv
  · intro v hv
    rw [hD]
    exact termInv_notMem hB hv
  · rw [hD]
    exact continuousOn_termLift
  · intro z hz
    rw [hD] at hz
    exact deriv_termFwd hz
  · -- the junction
    have h1 := hpath s hs
    rw [hs', htip] at h1
    by_cases h0 : 0 ≤ (Γ s).im
    · rw [termInv, ite_eq_left h0] at h1
      refine hfresh.eq_zero_of_extendFrom_eq (show Γ s ∈ Hbar from h0) ?_
      rw [Complex.ofReal_sub, h1, add_sub_cancel_right]
    · rw [termInv, ite_eq_right h0] at h1
      exact absurd (Complex.ofReal_injective h1) hne
  · rw [htip, Complex.ofReal_re]
    exact hword

/-- **(Det) for the explicit data from the clock of the first path.** The almost sure facts on the second path: its
record through a finite lifetime is good (`Exist.StagedLaw.ae_isDrvGood_of_isFlowLineDriver`), it is injective on its
closed available interval (Aux. lemma 25), and the first seed is real. -/
theorem terminalRetainedDet_of_clock (hC : TerminalRetainedClockStatement.{u}) :
    TerminalRetainedDetStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hwt Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ F hF c E hcs hcJ hcb hEm hreg
    hE2 hfl htrace
  have hclock := hC κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hwt P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ F hF c E hcs hcJ hcb hEm
    hreg hE2 hfl htrace
  have hgood : ∀ᵐ ω ∂P, min ⊤ (E ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (E ω))) :=
    ae_isDrvGood_of_isFlowLineDriver hκ ⊤ hreg hfl
  filter_upwards [hclock, hgood, htrace, Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂,
    Supp10.ae_apply_zero_of_isFlowLine hη₁] with ω hω hgω htω hinjω h0ω T e hT he hex hvis
  obtain ⟨hpos, hword, c₁, σ, hσ, hmono, himg, hpath⟩ := hω T e hT he hex hvis
  have hTe : (T : ℝ≥0∞) = (E ω).2 := by rw [hE2]; exact hT
  have hg : LocalExt.IsDrvGood (recHist (termRec (E ω))) :=
    hgω (by rw [min_eq_right le_top, ← hTe]; exact ENNReal.coe_ne_top)
  have hη : IsGeneratingTrace (E ω).1 (E ω).2 (fun t => η₂ ω t - x₂) := by rw [hE2]; exact htω
  have hinj : InjOn (η₂ ω) {t | (t : ℝ≥0∞) ≤ (E ω).2} := by rw [hE2]; exact hinjω
  have h₁ : (η₁ ω 0).im = 0 := by rw [h0ω, Complex.ofReal_im]
  exact ⟨hpos, isTerminalRetainedContinuation_of_clock (hreg ω) hg hTe hη hinj he hex h₁ hword hσ hmono himg
    hpath⟩

/-- **The named input `TerminalRetainedCondDetStatement` from the clock of the first path.** -/
theorem terminalRetainedCondDet_of_clock (hC : TerminalRetainedClockStatement.{u}) :
    TerminalRetainedCondDetStatement.{u} :=
  terminalRetainedCondDet_of_det (terminalRetainedDet_of_clock hC)

end InteractingSLE.RealContact
